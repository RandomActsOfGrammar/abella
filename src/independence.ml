open Term
open Typing
open Metaterm
open Format
open Tactics
open Checks
open Abella_types
open Extensions
open Prover

module H = Hashtbl

(* Independence *)

let rec get_head_predicate trm =
  match (observe trm) with
  | Var v -> [var_to_string v]
  | App (t, tlst) ->
     if (is_imp trm) then
       let left, right = extract_imp trm in
       get_head_predicate right
     else if (is_amp trm) then
       let left, right = extract_amp trm in
       (get_head_predicate left) @ (get_head_predicate right)
     else if (is_pi trm) then
       let abs = extract_pi trm in
       get_head_predicate abs
     else
       get_head_predicate t
  | Lam (tctx, t) -> get_head_predicate t
  | _ -> failwith "Invalid clause found in determining head predicate"

let rec get_body_clauses trm =
  match (observe trm) with
  | App (t, tlist) ->
     if (is_imp trm) then
       let left, right = extract_imp trm in
       left::(get_body_clauses right)
     else if (is_pi trm) then
       let abs = extract_pi trm in
       get_body_clauses abs
     else
       [] (*Reached end of body*)
  | Lam (tctx, t) -> get_body_clauses t
  | _ -> []

let rec term_eq t1 t2 =
  match (observe t1), (observe t2) with
  | Var v1, Var v2 -> (var_to_string v1) = (var_to_string v2)
  | App (p1, l1), App (p2, l2) ->
     if ((is_imp t1) && (is_imp t2)) then
       let left1, right1 = extract_imp t1 in
       let left2, right2 = extract_imp t2 in
       (term_eq left1 left2) && (term_eq right1 right2)
     else if ((is_amp t1) && (is_amp t2)) then
       let left1, right1 = extract_amp t1 in
       let left2, right2 = extract_amp t2 in
       (term_eq left1 left2) && (term_eq right1 right2)
     else if ((is_pi t1) && (is_pi t2)) then
       let abs1 = extract_pi t1 in
       let abs2 = extract_pi t2 in
       term_eq abs1 abs2
     else
       term_eq p1 p2
  | Lam (tctx1, trm1), Lam (tctx2, trm2) -> term_eq trm1 trm2
  | DB i, DB j -> true
  | Susp (trm1, i1, j1, env1), Susp (trm2, i2, j2, evn2) -> term_eq trm1 trm2
  | _ -> failwith "Ptr still in term after observer"

let rec member trm lst =
  match lst with
  | [] -> false
  | h::t ->
     if (term_eq trm h) then
       true
     else
       member trm t

type set_ref =
  | Ref of id
  | Formula of term

let pred_list : string list ref = ref []

let dynamic_contexts : (id, term list) H.t = H.create 10

let dependencies : (id, id list) H.t = H.create 10


let collect_contexts () =
  let ctx_col : (string, set_ref list) H.t = H.create 10 in
  let gamma' = ref !clauses in

  let rec simplify_constraints cnstrnts output =
    let rec add_formulas lst pred =
      match lst with
      | [] -> false
      | h::t ->
         match h with
         | Formula trm ->
            if not (member trm (H.find output pred)) then
              let _ = H.replace output pred (trm::(H.find output pred)) in
              let _ = add_formulas t in
              true
            else
              add_formulas t pred
         | Ref s ->
            if ((H.mem cnstrnts s) && s <> pred) then
              add_formulas ((H.find cnstrnts s) @ t) pred
            else
              add_formulas t pred

    in
    let rec simplify_iterate lst changed =
      match lst with
      | [] -> changed
      | h::t -> simplify_iterate t ((add_formulas (H.find cnstrnts h) h) || changed)

    in
    let rec simplify_aux () =
      if (simplify_iterate !pred_list false) then
        simplify_aux ()
      else
        ()

    in
    List.iter (fun h -> H.add output h [];
                        if (not (H.mem cnstrnts h)) then (*add empty context constraints*)
                          H.add cnstrnts h []
              ) !pred_list;
    simplify_aux ()

  in
  let add_constraints trm =
    let head_pred_trm = get_head_predicate trm in
    let body_trm = get_body_clauses trm in
    let rec go_through_body body =
      match body with
      | [] -> ()
      | g_i::t ->
         let head_predicates_g_i = get_head_predicate g_i in
         let body_g_i = get_body_clauses g_i in
         let _ = go_through_body t in
         let _ = gamma' := body_g_i @ !gamma' in
         List.iter (fun hp_g_i ->
             if H.mem ctx_col hp_g_i then
               H.replace ctx_col hp_g_i ((List.map (fun p -> Ref p) (List.filter (fun s -> s <> hp_g_i) head_pred_trm)) @
                                           (List.map (fun t -> Formula t) body_g_i) @
                                             (H.find ctx_col hp_g_i))
             else
               H.add ctx_col hp_g_i ((List.map (fun p -> Ref p) (List.filter (fun s -> s <> hp_g_i) head_pred_trm)) @
                                       (List.map (fun t -> Formula t) body_g_i))
           ) head_predicates_g_i
    in go_through_body body_trm

  in
  while !gamma' <> [] do
    match !gamma' with
    | h::t -> gamma' := t; add_constraints h
    | [] -> ()
  done;

  (*can probably change to use sign instead of ctx_col--certain to get all declared predicates*)
  let extract_all_predicates () =
    let rec find_set_ref_preds lst found_preds =
      match lst with
      | [] -> found_preds
      | h::t ->
         match h with
         | Ref s -> if (List.mem s found_preds) then
                      find_set_ref_preds t found_preds
                    else
                      find_set_ref_preds t (s::found_preds)
         | Formula _ -> find_set_ref_preds t found_preds
    in
    H.fold (fun p set_ref_lst lst ->
        if (List.mem p lst) then
          find_set_ref_preds set_ref_lst lst
        else
          find_set_ref_preds set_ref_lst (p::lst)
      ) ctx_col []

  in pred_list := extract_all_predicates ();
  simplify_constraints ctx_col dynamic_contexts
  (*display all predicates in pred_list -- testing purposes only*)
  (*;print_string "Predicates\n";
  List.iter (fun p -> print_string (p ^ "; ")) !pred_list;
  print_string "\n";*)
  (*display dynamic contexts --  testing purposes only*)
  (*;print_string "Dynamic Contexts\n";
  H.iter (fun p l -> print_string ("Pred: " ^ p ^ "\n");
                     List.iter (fun t -> print_string ((term_to_string t) ^ ";\n")) l
         ) dynamic_contexts*)


let collect_dependencies () =
  let dep_col = H.create 10 in
  let gamma' = !clauses in

  let simplify_constraints cnstrnts output =
    let rec add_dependencies lst pred =
      match lst with
      | [] -> false
      | dep_pred::tail ->
         let changed = List.fold_right (fun p changed -> if (not (List.mem p (H.find output pred))) then
                                                           let _ = H.replace output pred (p::(H.find output pred)) in
                                                           true
                                                         else
                                                           changed) (H.find output dep_pred) false in
         (add_dependencies tail pred) || changed

    in
    let rec simplify_aux () =
      let a = List.fold_right (fun h changed -> add_dependencies (H.find cnstrnts h) h) !pred_list false in
      if (a) then
        simplify_aux ()
      else
        ()

    in
    List.iter (fun h -> H.add output h [h]) !pred_list;
    simplify_aux ()

  in
  let add_constraints (pred : string) =
    let find_matching_preds cl lst =
      match lst with
      | [] -> ()
      | h::t ->
         if (h = pred) then
           let body = get_body_clauses cl in
           List.iter (fun trm ->
               let head_preds = get_head_predicate trm in
               List.iter (fun head ->
                   if (List.mem head (H.find dep_col pred)) then
                     ()
                   else
                     H.replace dep_col pred (head::(H.find dep_col pred))
                 ) head_preds
             ) body

    in
    let aux lst =
      List.iter (fun cl ->
          let head_predicates = get_head_predicate cl in
          find_matching_preds cl head_predicates
        ) lst
    in
    H.add dep_col pred [];
    aux gamma';
    aux (H.find dynamic_contexts pred)

  in
  List.iter (fun pred -> add_constraints pred) !pred_list;
  simplify_constraints dep_col dependencies
  (*display dependencies --  testing purposes only*)
  (*;print_string "Dependencies\n";
  H.iter (fun p l -> print_string ("Pred: " ^ p ^ "\n");
                     List.iter (fun t -> print_string (t ^ "; ")) l; print_string "\n";
         ) dependencies*)


(*Prove g independent of f*)
let independent f g =

  let outfile = open_out "out.thm" in

  let make_ctx_name pred =
    "ctx_" ^ pred

  in
  let make_subctx_name pred_super pred_sub =
    (make_ctx_name pred_sub) ^ "_subctx_" ^ (make_ctx_name pred_super)

  in
  let define_ctx pred =
    let ctx_formulas = H.find dynamic_contexts pred in
    let ctx_name = make_ctx_name pred in
    let rec add_formula form_lst def_str =
      match form_lst with
      | [] -> def_str ^ ".\n\n"
      | h::t -> (*TODO--do checking/replacing to remove names L, E; ensure variable names are capitalized*)
         let new_def = def_str ^ ";\n\t" ^ ctx_name ^ " ((" ^ (term_to_string h) ^ ") :: L) := " ^ ctx_name ^ " L" in
         add_formula t new_def
    in
    let rec add_proof_step form_lst thm_str prf_str =
      match form_lst with
      | [] -> thm_str ^ prf_str ^ "\n\n"
      | [h] ->
         let new_thm = thm_str ^ "E = (" ^ (term_to_string h) ^ ").\n" in
         let new_prf = prf_str ^ "\n\tcase H2. search. apply IH to H3 H4. search." in
         add_proof_step [] new_thm new_prf
      | h::t -> (*TODO--capitalizing variable names, adding exists for variables*)
         let new_thm = thm_str ^ "E = (" ^ (term_to_string h) ^ ") \\/" in
           let new_prf = prf_str ^ "\n\tcase H2. search. apply IH to H3 H4. search." in
         add_proof_step t new_thm new_prf
    in
    
    let def_start = "Define " ^ ctx_name ^" : olist -> prop by\n\t" ^ ctx_name ^ " nil" in
    let definition = add_formula ctx_formulas def_start in
    output_string outfile definition;

    if (List.length ctx_formulas > 0) then
      let thm_stmt = "Theorem " ^ ctx_name ^ "_mem : forall L E, " ^ ctx_name ^ " L -> member E L -> " in
      let prf_start = "induction on 1. intros. case H1.\n\tcase H2." in
      let thm_prf = add_proof_step ctx_formulas thm_stmt prf_start in
      let () = output_string outfile thm_prf in
      flush outfile

  in
  let subctx_thm pred g_ctx =
    let rec add_step lst prf_str =
      match lst with
      | [] -> prf_str ^ "\n\n"
      | h::t ->
         let new_prf = prf_str ^ "\n\tapply IH to H2. search." in
         add_step t new_prf
    in
    if (pred <> g) then
      let thm_prf = "Theorem " ^ (make_subctx_name g pred) ^ " : forall L, ctx_" ^
                      g ^ " L -> ctx_" ^ pred ^ " L.\ninduction on 1. intros. case H1.\n\tsearch." in
      let subctx_prf = add_step g_ctx thm_prf in
      let () = output_string outfile subctx_prf in
      flush outfile

  in
  let dep_g = H.find dependencies g in
  if (List.mem f dep_g) then
    failwith ("Cannot prove " ^ g ^ " independent of " ^ f ^ "--dependency exists");
  List.iter define_ctx dep_g;
  let g_ctx = H.find dynamic_contexts g in
  List.iter (fun dep_pred -> subctx_thm dep_pred g_ctx) dep_g;
  close_out outfile
