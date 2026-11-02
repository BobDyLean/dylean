module

public
instance: Ord Unit where
  compare _ _ := .eq

public
instance: Std.ReflOrd Unit where
  compare_self := by simp [compare]

public
instance: Std.LawfulEqOrd Unit where
  eq_of_compare := by simp [compare]

public
instance: Std.OrientedOrd Unit where
  eq_swap := by simp [compare]

public
instance: Std.TransOrd Unit where
  isLE_trans := by simp [compare]
