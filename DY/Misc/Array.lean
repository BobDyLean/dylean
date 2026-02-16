module

import all Init.Data.Array.Attach

-- TODO: upstream?
-- there is Array.unattach_attachWith, but not this version
public
theorem Array.attachWith_unattach
  {a: Type u}
  {p: a → Prop}
  (arr: Array (Subtype p)) (h: ∀ x, x ∈ (Array.unattach arr) → p x)
  : Array.attachWith (Array.unattach arr) p h = arr
:= by
  cases arr
  rename_i l
  simp only [Array.attachWith, Array.unattach]
  simp only [List.unattach_toArray, List.mem_toArray] at h
  induction l <;>
  simp_all
