(* Rule REFL *)

let test_refl = REFL `x:bool`

let _ = save_thm "test_refl" test_refl


(* (\* Rule SYM *\) *)

(* let test_sym = SYM (REFL `x:bool`);; *)

(* let _ = save_thm "test_sym" test_sym *)


(* Rule TRANS *)

let test_trans = TRANS test_refl test_refl

let _ = save_thm "test_trans" test_trans


(* Rule ABS *)

let test_abs = ABS `x:bool` test_trans

let _ = save_thm "test_abs" test_abs


(* Export *)

let _ = export_list ["test_refl"; (* "test_sym"; *) "test_trans"; "test_abs"]
