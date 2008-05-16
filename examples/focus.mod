% Formulas
form (atom A).
form (imp B C) :- form B, form C.

% The full logic
conc B :- hyp B.
conc (imp B C) :- hyp B => conc C.
conc D :- hyp (imp B C), conc B, hyp C => conc D.

% The focused logic (two phases: focused and unfocused)
focus (atom A) A.
focus (imp B C) A :- unfocus B, hyp C => focus C A.

unfocus (imp B C) :- hyp B => unfocus C.
unfocus (atom A) :- hyp B, focus B A.
