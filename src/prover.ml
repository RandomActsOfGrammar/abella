(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Term
open Metaterm
open Format
open Tactics
open Types
open Extensions

module H = Hashtbl

type lemmas = (id * metaterm) list
let lemmas : lemmas ref = ref []

type subgoal = unit -> unit
let subgoals : subgoal list ref = ref []

type hyp = {
  id : id ;
  term : metaterm ;
  mutable abbrev : string option ;
}

type sequent = {
  mutable vars : (id * term) list ;
  mutable hyps : hyp list ;
  mutable goal : metaterm ;
  mutable count : int ;
  mutable name : string ;
}

let sequent = {
  vars = [] ;
  hyps = [] ;
  goal = termobj (const "placeholder") ;
  count = 0 ;
  name = "" ;
}

let extend_name i =
  if sequent.name = "" then
    sequent.name <- string_of_int i
  else
    sequent.name <- sequent.name ^ "." ^ (string_of_int i)

let annotate gs =
  let rec aux i gs =
    match gs with
      | [] -> []
      | g::rest ->
          (fun () -> g (); extend_name i) :: aux (i+1) rest
  in
  let n = List.length gs in
    if n < 2 then
      gs
    else
      aux 1 gs

let add_subgoals new_subgoals =
  subgoals := annotate new_subgoals @ !subgoals

let localize_metaterm term =
  term
  |> replace_metaterm_vars sequent.vars
  |> replace_metaterm_nominal_vars

let localize_term term =
  term
  |> replace_term_vars sequent.vars
  |> replace_term_nominal_vars


(* The vars = sequent.vars is superfluous, but forces the copy *)
let copy_sequent () =
  {sequent with vars = sequent.vars}

let set_sequent other =
  sequent.vars <- other.vars ;
  sequent.hyps <- other.hyps ;
  sequent.goal <- other.goal ;
  sequent.count <- other.count ;
  sequent.name <- other.name

let fresh_hyp_name base =
  if base = "" then begin
    sequent.count <- sequent.count + 1 ;
    "H" ^ (string_of_int sequent.count)
  end else
    fresh_name base (List.map (fun h -> (h.id, ())) sequent.hyps)

let normalize_sequent () =
  sequent.goal <- normalize sequent.goal ;
  sequent.hyps <-
    sequent.hyps |> List.map (fun h -> { h with term = normalize h.term })

(* Clauses *)

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let clauses : clauses ref = ref []

let add_clauses new_clauses =
  clauses := !clauses @ new_clauses

let parse_defs str =
  Parser.defs Lexer.token (Lexing.from_string str)

let defs : defs = H.create 10
let () = H.add defs ("member", 2)
  (Inductive, parse_defs ("member A (A :: L). \
                         \ member A (B :: L) := member A L."))

let add_def dtype new_def =
  let head = def_sig new_def in
    try
      let (ty, dcs) = H.find defs head in
        if ty = dtype then
          H.replace defs head (ty, dcs @ [new_def])
        else
          failwith (sprintf "%s has already been defined as %s"
                      (sig_to_string head) (def_type_to_string ty))
    with Not_found -> H.add defs head (dtype, [new_def])


(* Undo support *)

type undo_stack = (sequent * subgoal list * Term.bind_state) list
let undo_stack : undo_stack ref = ref []

let save_undo_state () =
  undo_stack := (copy_sequent (), !subgoals, Term.get_bind_state ())::
    !undo_stack

let undo () =
  match !undo_stack with
    | (saved_sequent, saved_subgoals, bind_state)::rest ->
        set_sequent saved_sequent ;
        subgoals := saved_subgoals ;
        Term.set_bind_state bind_state ;
        undo_stack := rest
    | [] -> failwith "Nothing left to undo"


(* Proof state manipulation utilities *)

let reset_prover =
  let original_sequent = copy_sequent () in
    fun () ->
      set_sequent original_sequent ;
      subgoals := [] ;
      undo_stack := []

let full_reset_prover =
  let original_clauses = !clauses in
  let original_defs = H.copy defs in
    fun () ->
      reset_prover () ;
      clauses := original_clauses ;
      H.assign defs original_defs

let add_hyp ?(name=fresh_hyp_name "") term =
  sequent.hyps <- List.append sequent.hyps
    [{ id = name ; term = term ; abbrev = None }]

let remove_hyp name =
  sequent.hyps <- List.remove_all (fun h -> h.id = name) sequent.hyps

let add_var v =
  sequent.vars <- List.append sequent.vars [v]

let add_if_new_var (name, v) =
  if not (List.mem_assoc name sequent.vars) then
    add_var (name, v)

let add_lemma name lemma =
  lemmas := (name, lemma)::!lemmas

let get_hyp name =
  let hyp = List.find (fun h -> h.id = name) sequent.hyps in
    hyp.term

let get_lemma name =
  List.assoc name !lemmas

let get_hyp_or_lemma name =
  try
    get_hyp name
  with
      Not_found -> get_lemma name

let next_subgoal () =
  match !subgoals with
    | [] -> failwith "Proof completed."
    | set_subgoal::rest ->
        set_subgoal () ;
        normalize_sequent () ;
        subgoals := rest


(* Pretty print *)

let vars_to_string () =
  match sequent.vars with
    | [] -> ""
    | _ -> "Variables: " ^ (String.concat ", " (List.map fst sequent.vars))

let format_hyp fmt hyp =
  fprintf fmt "%s : " hyp.id ;
  begin match hyp.abbrev with
    | None -> format_metaterm fmt hyp.term
    | Some s -> fprintf fmt "%s" s
  end;
  pp_force_newline fmt ()

let format_hyps fmt =
  List.iter (format_hyp fmt) sequent.hyps

let format_count_subgoals fmt =
  match List.length !subgoals with
    | 0 -> ()
    | 1 -> fprintf fmt "1 other subgoal.@\n@\n"
    | n -> fprintf fmt "%d other subgoals.@\n@\n" n

let format_display_subgoals fmt =
  save_undo_state () ;
  List.iter (fun set_state ->
               set_state () ;
               fprintf fmt "@[<1>Subgoal %s is:@\n%a@]@\n@\n"
                 sequent.name format_metaterm (normalize sequent.goal))
    !subgoals ;
  undo ()

let subgoals_off = ref false

let format_other_subgoals fmt =
  if !subgoals_off then
    format_count_subgoals fmt
  else
    format_display_subgoals fmt

let format_sequent fmt =
  pp_open_box fmt 2 ;
  fprintf fmt "  %s@\n" (vars_to_string ()) ;
  format_hyps fmt ;
  fprintf fmt "============================@\n" ;
  fprintf fmt " %a" format_metaterm sequent.goal ;
  pp_close_box fmt ()

let format_display fmt =
  pp_open_box fmt 0 ;
  if sequent.name = "" then
    fprintf fmt "@\n"
  else
    fprintf fmt "Subgoal %s:@\n@\n" sequent.name;
  format_sequent fmt ;
  fprintf fmt "@\n@\n" ;
  format_other_subgoals fmt ;
  pp_close_box fmt () ;
  pp_print_flush fmt ()

let display () =
  format_display std_formatter

let get_display () =
  let b = Buffer.create 100 in
    format_display (formatter_of_buffer b) ;
    Buffer.contents b


(* Object level instantiation *)

let inst h n t =
  let ht = get_hyp h in
    match ht with
      | Obj _ -> t |> localize_term
                   |> object_inst ht n
                   |> add_hyp
      | _ -> failwith
          "Instantiation can only be used on hypotheses of the form {...}"


(* Object level cut *)

let cut h arg =
  let h = get_hyp h in
  let arg = get_hyp arg in
    match h, arg with
      | Obj(obj_h, _), Obj(obj_arg, _) ->
          add_hyp (object_cut obj_h obj_arg)
      | _ -> failwith "Cut can only be used on hypotheses of the form {...}"


(* Search *)

let has_inductive_hyps hyp =
  let rec aux term =
    match term with
      | Binding(Forall, _, body) -> aux body
      | Binding(Nabla, _, body) -> aux body
      | Arrow(Obj(_, Smaller i), _) -> true
      | Arrow(Pred(_, Smaller i), _) -> true
      | Arrow(left, right) -> aux right
      | _ -> false
  in
    aux hyp.term

let remove_inductive_hypotheses hyps =
  List.remove_all has_inductive_hyps hyps

let has_coinductive_result hyp =
  let rec aux term nested =
    match term with
      | Binding(Forall, _, body) -> aux body true
      | Binding(Nabla, _, body) -> aux body true
      | Arrow(left, right) -> aux right true
      | Pred(_, CoSmaller _) -> nested
      | _ -> false
  in
    aux hyp.term false

let remove_coinductive_hypotheses hyps =
  List.remove_all has_coinductive_result hyps

let defs_to_list defs =
  H.fold (fun _ (_, dcs) acc -> dcs @ acc) defs []

let search_goal ?(depth=5) goal =
  let hyps = sequent.hyps
    |> remove_inductive_hypotheses
    |> remove_coinductive_hypotheses
    |> List.map (fun h -> h.term)
  in
  let search_depth n =
    Tactics.search
      ~depth:n
      ~hyps
      ~clauses:!clauses
      ~defs:(defs_to_list defs)
      goal
  in
    List.exists search_depth (List.range 1 depth)

let search ?(limit=None) ?(interactive=true) () =
  if
    match limit with
      | None -> search_goal sequent.goal
      | Some depth -> search_goal ~depth sequent.goal
  then
    next_subgoal ()
  else if not interactive then
    failwith "Search failed"

(* Apply *)

let get_some_hyp name =
  if name = "_" then
    None
  else
    Some (get_hyp name)

let goal_to_subgoal g =
  let saved_sequent = copy_sequent () in
  let bind_state = Term.get_bind_state () in
    fun () ->
      set_sequent saved_sequent ;
      Term.set_bind_state bind_state ;
      sequent.goal <- g

let ensure_no_logic_variable terms =
  let logic_vars = List.flatten_map (metaterm_vars_alist Logic) terms in
  if List.length logic_vars > 0 then
    failwith "Found logic variable at toplevel"

let ensure_no_restrictions term =
  let rec aux t nested =
    match t with
      | Binding(Forall, _, body) -> aux body true
      | Binding(Nabla, _, body) -> aux body true
      | Arrow(left, right) -> aux left true; aux right true
      | Obj(_, Smaller i) | Obj(_, Equal i)
      | Pred(_, Smaller i) | Pred(_, Equal i) ->
          if nested then invalid_metaterm_arg term
      | Pred(_, CoSmaller i) ->
          invalid_metaterm_arg term
      | _ -> ()
  in
    aux term false

let apply h args ws =
  let stmt = get_hyp_or_lemma h in
  let args = List.map get_some_hyp args in
  let () = List.iter (Option.map_default ensure_no_restrictions ()) args in
  let ws = List.map (fun (x,t) -> x, localize_term t) ws in
  let result, obligations = Tactics.apply_with stmt args ws in
  let remaining_obligations =
    List.remove_all (fun g -> search_goal (normalize g)) obligations in
  let () = ensure_no_logic_variable (result :: remaining_obligations) in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
  let resulting_case = recursive_metaterm_case ~used:sequent.vars result in
  let resulting_subgoal =
    let restore = goal_to_subgoal sequent.goal in
      fun () ->
        restore () ;
        match resulting_case with
          | None -> assert false
          | Some case ->
              List.iter add_if_new_var case.stateless_new_vars ;
              List.iter add_hyp case.stateless_new_hyps
  in
    if resulting_case = None then
      add_subgoals obligation_subgoals
    else
      add_subgoals (obligation_subgoals @ [resulting_subgoal]) ;
    next_subgoal ()


(* Case analysis *)

(* Lifting during case analysis may cause some variables to be bound to
   themselves. We need to update sequent.vars to reflect this. *)
let update_self_bound_vars () =
  sequent.vars <-
    sequent.vars |> List.map
        (fun (id, term) ->
           match term_head_var term with
             | Some v when term_to_name v = id ->
                 (id, v)
             | _ -> (id, term))

let add_cases_to_subgoals cases =
  let case_to_subgoal case =
    let saved_sequent = copy_sequent () in
      fun () ->
        set_sequent saved_sequent ;
        List.iter add_if_new_var case.new_vars ;
        List.iter add_hyp case.new_hyps ;
        begin match case.new_goal with
          | None -> ()
          | Some g -> sequent.goal <- g
        end ;
        Term.set_bind_state case.bind_state ;
        update_self_bound_vars () ;
  in
    add_subgoals (List.map case_to_subgoal cases)

let case ?(keep=false) str =
  let term = get_hyp str in
  let global_support =
    (List.flatten_map metaterm_support
       (List.map (fun h -> h.term) sequent.hyps)) @
      (metaterm_support sequent.goal)
  in
  let cases =
    Tactics.case ~used:sequent.vars ~clauses:!clauses
      ~defs:(defs_to_list defs) ~global_support term
  in
    if not keep then remove_hyp str ;
    add_cases_to_subgoals cases ;
    next_subgoal ()


(* Induction *)

let get_restriction r =
  match r with
    | Smaller n -> n
    | CoSmaller n -> n
    | Equal n -> n
    | Irrelevant -> 0

let get_max_restriction t =
  let rec aux t =
    match t with
      | True | False | Eq _ -> 0
      | Obj(_, r) -> get_restriction r
      | Arrow(a, b) -> max (aux a) (aux b)
      | Binding(_, _, body) -> aux body
      | Or(a, b) -> max (aux a) (aux b)
      | And(a, b) -> max (aux a) (aux b)
      | Pred(_, r) -> get_restriction r
  in
    aux t

let next_restriction () =
  1 + (sequent.hyps |> List.map (fun h -> h.term) |>
           List.map get_max_restriction |> List.max)

let rec nth_product n term =
  match term with
    | Binding(Forall, _, body) -> nth_product n body
    | Binding(Nabla, _, body) -> nth_product n body
    | Arrow(left, right) ->
        if n = 1 then
          left
        else
          nth_product (n-1) right
    | _ -> failwith "Can only induct on predicates and judgments"

let ensure_is_inductive term =
  match term with
    | Obj _ -> ()
    | Pred(p, _) ->
        let psig = term_sig p in
          begin try
            match H.find defs psig with
              | Inductive, _ -> ()
              | CoInductive, _ -> failwith
                  (sprintf "Cannot induct on %s since it has\
                          \ been coinductively defined" (sig_to_string psig))
          with Not_found ->
            failwith (sprintf "Cannot induct on %s since it has\
                             \ not been defined" (sig_to_string psig))
          end
    | _ -> failwith "Can only induct on predicates and judgments"

let add_ih h =
  add_hyp ~name:(fresh_hyp_name "IH") h

let induction ind_args =
  List.iter
    (fun (arg, goal) -> ensure_is_inductive (nth_product arg goal))
    (List.combine ind_args (and_to_list sequent.goal)) ;
  let res_num = next_restriction () in
  let (ihs, new_goal) = Tactics.induction ind_args res_num sequent.goal in
    List.iter (fun h -> add_hyp ~name:(fresh_hyp_name "IH") h) ihs ;
    sequent.goal <- new_goal


(* CoInduction *)

let rec conclusion term =
  match term with
    | Binding(Forall, _, body) -> conclusion body
    | Binding(Nabla, _, body) -> conclusion body
    | Arrow(left, right) -> conclusion right
    | Pred(p, _) -> p
    | _ -> failwith "Cannot coinduct on a goal of this form"

let ensure_is_coinductive p =
  let psig = term_sig p in
    try
      match H.find defs psig with
        | CoInductive, _ -> ()
        | Inductive, _ -> failwith
            (sprintf "Cannot coinduct on %s since it has\
                    \ been inductively defined" (sig_to_string psig))
    with Not_found ->
      failwith (sprintf "Cannot coinduct on %s since it has\
                       \ not been defined" (sig_to_string psig))

let coinduction () =
  ensure_is_coinductive (conclusion sequent.goal) ;
  let res_num = next_restriction () in
  let (ch, new_goal) = Tactics.coinduction res_num sequent.goal in
  let name = fresh_hyp_name "CH" in
    add_hyp ~name ch ;
    sequent.goal <- new_goal


(* Assert *)

let assert_hyp term =
  let term = localize_metaterm term in
  let delayed_subgoal =
    { bind_state = get_bind_state () ;
      new_vars = [] ;
      new_hyps = [term] ;
      new_goal = Some sequent.goal }
  in
    sequent.goal <- term ;
    if search_goal sequent.goal then
      add_cases_to_subgoals [delayed_subgoal]
    else begin
      let new_subgoal =
        { bind_state = get_bind_state () ;
          new_vars = [] ;
          new_hyps = [] ;
          new_goal = None }
      in
        add_cases_to_subgoals [new_subgoal; delayed_subgoal]
    end ;
    next_subgoal ()

(* Object logic monotone *)

let monotone h t =
  let ht = get_hyp h in
    match ht with
      | Obj(obj, r) ->
          let t = localize_term t in
          let new_obj = { obj with context = Context.normalize [t] } in
          let delayed_subgoal =
            { bind_state = get_bind_state () ;
              new_vars = [] ;
              new_hyps = [Obj(new_obj, r)] ;
              new_goal = Some sequent.goal }
          in
            sequent.goal <-
              Binding(Forall, ["X"],
                      Arrow(member (Term.const "X")
                              (Context.context_to_term obj.context),
                            member (Term.const "X")
                              t)) ;
            if search_goal sequent.goal then
              add_cases_to_subgoals [delayed_subgoal]
            else begin
              let new_subgoal =
                { bind_state = get_bind_state () ;
                  new_vars = [] ;
                  new_hyps = [] ;
                  new_goal = None }
              in
                add_cases_to_subgoals [new_subgoal; delayed_subgoal]
            end ;
            next_subgoal ()
      | _ -> failwith
          "Monotone can only be used on hypotheses of the form {...}"


(* Theorem *)

let theorem thm =
  sequent.goal <- thm


(* Introduction of forall variables *)

let intros () =
  let rec aux term =
    match term with
      | Binding(Forall, bindings, body) ->
          let alist = fresh_alist ~tag:Eigen ~used:sequent.vars bindings in
            List.iter add_var (List.map alist_to_used alist) ;
            let alist = raise_alist ~support:(metaterm_support body) alist in
              aux (replace_metaterm_vars alist body)
      | Binding(Nabla, bindings, body) ->
          aux (replace_metaterm_vars
                 (List.combine bindings
                    (fresh_nominals (List.length bindings) body))
                 body)
      | Arrow(left, right) ->
          add_hyp (normalize left) ;
          aux right
      | _ -> term
  in
    sequent.goal <- aux sequent.goal

(* Split *)

let split propogate_result =
  let rec accum_goals conjs prev =
    match conjs with
      | [] -> []
      | g::rest ->
          let saved = goal_to_subgoal g in
          let subgoal () =
            saved () ;
            if propogate_result then List.iter add_hyp (List.rev prev)
          in
            subgoal :: (accum_goals rest (g :: prev))
  in
  let conjs = and_to_list sequent.goal in
    if List.length conjs = 1 then failwith "Needless use of split" ;
    add_subgoals (accum_goals (and_to_list sequent.goal) []) ;
    next_subgoal ()

(* Left and right side of disjunction *)

let left () =
  match sequent.goal with
    | Or(left, _) -> sequent.goal <- left
    | _ -> ()

let right () =
  match sequent.goal with
    | Or(_, right) -> sequent.goal <- right
    | _ -> ()


(* Unfold *)

let unfold () =
  let goal = unfold ~defs:(defs_to_list defs) sequent.goal in
  let goals = and_to_list goal in
    add_subgoals (List.map goal_to_subgoal goals) ;
    next_subgoal ()

(* Exists *)

let exists t =
  match sequent.goal with
    | Binding(Metaterm.Exists, id::ids, body) ->
        let t = localize_term t in
        let goal = exists ids (replace_metaterm_vars [(id, t)] body) in
          sequent.goal <- goal
    | _ -> ()

(* Skip *)

let skip () =
  next_subgoal ()

(* Clear *)

let clear hs =
  List.iter remove_hyp hs

(* Abbrev *)

let abbrev id str =
  List.iter (fun h -> if h.id = id then h.abbrev <- Some str) sequent.hyps

let unabbrev ids =
  List.iter (fun h -> if List.mem h.id ids then h.abbrev <- None) sequent.hyps
