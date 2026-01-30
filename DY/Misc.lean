instance: Ord Unit where
  compare _ _ := .eq

instance: Std.ReflOrd Unit where
  compare_self := by grind

instance: Std.LawfulEqOrd Unit where
  eq_of_compare := by grind

instance: Std.OrientedOrd Unit where
  eq_swap := by grind [Ordering.swap]

instance: Std.TransOrd Unit where
  isLE_trans := by grind

def ByteArray.compare (x y: ByteArray): Ordering :=
  Ord.compare x.data y.data

instance: Ord ByteArray where
  compare x y := ByteArray.compare x y

instance: Std.ReflOrd ByteArray where
  compare_self := by
    simp only [compare]
    simp [ByteArray.compare]

instance: Std.LawfulEqOrd ByteArray where
  eq_of_compare := by
    simp only [compare]
    simp only [ByteArray.compare]
    intro ⟨ x ⟩ ⟨ y ⟩ h
    simp only [ByteArray.mk.injEq]
    apply Std.LawfulEqOrd.eq_of_compare
    exact h

instance: Std.OrientedOrd ByteArray where
  eq_swap := by
    simp only [compare]
    simp only [ByteArray.compare]
    intro x y
    apply Std.OrientedOrd.eq_swap

instance: Std.TransOrd ByteArray where
  isLE_trans := by
    simp only [compare]
    simp only [ByteArray.compare]
    intro x y z
    apply Std.TransOrd.isLE_trans
