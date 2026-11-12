/-
  This module formalizes Knaster-Tarski fixpoint theorem
  (more specifically, the existence of least fixpoint)
  https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem
-/

module

namespace DY.Fixpoint

public
abbrev Set (α: Type u) := α → Prop

-- we keep this instance private
local
instance: HasSubset (Set α) where
  Subset set1 set2 :=
    ∀ x, set1 x → set2 x

@[expose]
public
def IsMonotonic {α: Type u} (f: Set α → Set α): Prop :=
  ∀ set1 set2: Set α,
    (∀ x, set1 x → set2 x) →
    (∀ x, f set1 x → f set2 x)

theorem IsMonotonic_eq
  {α: Type u}
  (f: Set α → Set α)
  : IsMonotonic f = (∀ set1 set2, set1 ⊆ set2 → f set1 ⊆ f set2)
:= rfl

@[expose]
public
def combine {α: Type u} {Id: Type} (fs: Id → (Set α → Set α)) (set: Set α): Set α :=
  fun x => ∃ id, fs id set x

public
theorem combine_isMonotonic
  {α: Type u}
  {Id: Type}
  (fs: Id → (Set α → Set α))
  (h_fs: ∀ id, IsMonotonic (fs id))
  : IsMonotonic (combine fs)
  := by
    intro s1 s2 h_subset x ⟨ id, _ ⟩
    simp_all only [IsMonotonic, combine]
    exists id
    grind

-- Stated without the local `⊆` instance so that the exposed body
-- only mentions public declarations.
@[expose]
public
def mkLeastFixpoint {α: Type u} (f: Set α → Set α): Set α :=
  fun x =>
    ∀ s: Set α, (∀ y, f s y → s y) → s x

public
theorem mkLeastFixpoint_is_fixpoint
  {α: Type u}
  (f: Set α → Set α)
  (h_mono: IsMonotonic f)
  : f (mkLeastFixpoint f) = mkLeastFixpoint f
:= by
  -- `D s` means `s` is a pre-fixpoint of `f`; `mkLeastFixpoint f` is their intersection.
  let D: Set α → Prop := fun s => ∀ y, f s y → s y
  have h_lfp_le: ∀ s, D s → ∀ x, mkLeastFixpoint f x → s x := by
    intro s hs x hx
    exact hx s hs
  have h_D_lfp: D (mkLeastFixpoint f) := by
    intro y hy s hs
    exact hs y (h_mono _ _ (h_lfp_le s hs) y hy)
  funext x
  apply propext
  constructor
  · intro h s hs
    exact hs x (h_mono _ _ (h_lfp_le s hs) x h)
  · intro h
    exact h (f (mkLeastFixpoint f)) (fun y hy => h_mono _ _ h_D_lfp y hy)

public
theorem mkLeastFixpoint_is_least
  {α: Type u}
  (f: Set α → Set α)
  (_: IsMonotonic f)
  (set: Set α)
  :
  (∀ x, f set x → set x) →
  (∀ x, mkLeastFixpoint f x → set x)
:= by
  simp_all [IsMonotonic_eq, Subset, mkLeastFixpoint]

end DY.Fixpoint
