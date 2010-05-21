let test_refl = REFL `x:bool`

let _ = save_thm "test_refl" test_refl

let _ = export_list ["test_refl"]
