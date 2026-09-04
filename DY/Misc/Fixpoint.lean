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

public
def mkLeastFixpoint {α: Type u} (f: Set α → Set α): Set α :=
  fun x =>
    ∀ s: Set α, f s ⊆ s → s x

public
theorem mkLeastFixpoint_is_fixpoint
  {α: Type u}
  (f: Set α → Set α)
  (h_mono: IsMonotonic f)
  : f (mkLeastFixpoint f) = mkLeastFixpoint f
:= by
  let D: Set α → Prop := fun s => f s ⊆ s
  let l: Set α := fun x => ∀ s, D s → s x
  have: ∀ s, D s → D (f s) := by grind [IsMonotonic_eq]
  have: ∀ s, D s → l ⊆ s := by
    dsimp only [mkLeastFixpoint, Subset, D]
    intro s h1 h2 h3
    exact h3 s h1
  have: ∀ s, D s → f l ⊆ s := by
    intro s h
    have: f s ⊆ s := by grind
    have: l ⊆ s := by grind
    have: f l ⊆ f s := by grind [IsMonotonic_eq]
    simp_all [Subset]
  have: f l ⊆ l := by
    subst D l
    simp_all [Subset]
  have: D l := by grind
  have: D (f l) := by grind
  simp_all [Subset]
  unfold mkLeastFixpoint
  grind

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
