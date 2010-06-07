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


(* Rule BETA *)

let test_beta = BETA `(\x. \y. x <=> y) x`

let _ = save_thm "test_beta" test_beta


(* Rule INST *)

let test_inst = INST [(`(\y:bool. y) y:bool`, `x:bool`);(`u:bool`,`t:bool`)] (REFL `(x <=> y) <=> (z <=> t)`)

let _ = save_thm "test_inst" test_inst


(* Rule MK_COMB *)

let test_mk_comb = MK_COMB (REFL `\x:bool. x`, REFL `y:bool`)

let _ = save_thm "test_mk_comb" test_mk_comb


(* Rule ASSUME *)

let test_assume = ASSUME `x:bool`

let _ = save_thm "test_assume" test_assume


(* Rule DISCH *)

(* let test_disch = DISCH `x:bool` test_assume *)

(* let _ = save_thm "test_disch" test_disch *)


(* Mixing rules *)

let test_mix = ABS `y:bool` (TRANS test_inst (REFL `((\y. y) y <=> y) <=> z <=> u`))

let _ = save_thm "test_mix" test_mix


let test_mix2 = ABS `z:bool` (ASSUME `x <=> y`)

let _ = save_thm "test_mix2" test_mix2


let test_mix3 = INST [] test_mix2

let _ = save_thm "test_mix3" test_mix3


(* let test_mix4 = DISCH `x <=> y` test_mix3 *)

(* let _ = save_thm "test_mix4" test_mix4 *)


(* Export *)

let _ = export_list ["test_refl"; (* "test_sym"; *) "test_trans"; "test_abs"; "test_beta"; "test_inst"; "test_mix"; "test_mk_comb"; "test_assume"; "test_mix2"; "test_mix3"(* ; "test_disch"; "test_mix4" *)]
