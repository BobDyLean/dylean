/-
  This module formalizes Kleene's fixpoint theorem
  https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem
-/

module

namespace DY.Kleene

@[expose]
public
def Set (α: Type u) := α → Prop

public
instance: HasSubset (Set α) where
  Subset set1 set2 :=
    ∀ x, set1 x → set2 x

@[ext]
theorem Set.ext
  {α: Type u}
  (set1 set2: Set α)
  :
  (∀ x, set1 x ↔ set2 x) →
  set1 = set2
  := by
    intro h
    funext
    simp_all

@[expose]
public
def Chain (α: Type u) := Nat → Set α

public
def Chain.IsDirected {α: Type u} (chain: Chain α): Prop :=
  ∀ i j, i ≤ j → (chain i) ⊆ (chain j)

@[expose]
public
def Chain.union (chain: Chain α): Set α :=
  fun x => ∃ n, chain n x

@[expose]
public
def Chain.map (f: Set α → Set α) (chain: Chain α): Chain α :=
  fun n => fun x => f (chain n) x

@[expose]
public
def IsScottContinuous {α: Type u} (f: Set α → Set α): Prop :=
  ∀ chain: Chain α,
    chain.IsDirected →
    f (chain.union) = (chain.map f).union

def IsMonotonic {α: Type u} (f: Set α → Set α): Prop :=
  ∀ set1 set2: Set α,
    set1 ⊆ set2 →
    f set1 ⊆ f set2

theorem isScottContinuous_implies_isMonotonic
  {α: Type u} (f: Set α → Set α):
  IsScottContinuous f →
  IsMonotonic f
  := by
    intro h_scott set1 set2 h_subset x
    let chain: Chain α := fun n => if n = 0 then set1 else set2
    have h_chain_directed: chain.IsDirected := by
      subst chain
      intros i j
      by_cases i = 0 <;>
      by_cases j = 0 <;>
      simp_all [Subset]
    have h_chain_scott := h_scott chain h_chain_directed
    have h_chain_scott_left: chain.union = set2 := by
      ext x
      simp only [Chain.union]
      constructor
      · intro ⟨ n, h_n ⟩
        by_cases n = 0
        · apply h_subset x
          grind
        · grind
      · intro h
        exists 1
    have h_chain_scott_right: (chain.map f).union = (fun x => f set1 x ∨ f set2 x) := by
      ext x
      subst chain
      simp_all only [Chain.union, Chain.map, iff_or_self]
      intro
      exists 0
    rewrite [h_chain_scott_left] at h_chain_scott
    rewrite [h_chain_scott_right] at h_chain_scott
    rewrite [h_chain_scott]
    grind

def mkWeakestFixpointAux {α: Type u} (f: Set α → Set α): Chain α :=
  fun n =>
    if n = 0 then
      fun _ => False
    else
      f (mkWeakestFixpointAux f (n-1))

public
def mkWeakestFixpoint {α: Type u} (f: Set α → Set α): Set α :=
  (mkWeakestFixpointAux f).union

theorem mkWeakestFixpointAux_monotonic_consecutive
  {α: Type u}
  (f: Set α → Set α)
  (h_scott: IsScottContinuous f)
  (i: Nat)
  : mkWeakestFixpointAux f i ⊆ mkWeakestFixpointAux f (i+1)
  := by
    induction i with
    | zero => simp [mkWeakestFixpointAux, Subset]
    | succ i ih =>
      unfold mkWeakestFixpointAux
      exact isScottContinuous_implies_isMonotonic f h_scott (mkWeakestFixpointAux f i) (mkWeakestFixpointAux f (i+1)) ih

theorem mkWeakestFixpointAux_monotonic
  {α: Type u}
  (f: Set α → Set α)
  (h_scott: IsScottContinuous f)
  (i j: Nat)
  :
  i ≤ j →
  mkWeakestFixpointAux f i ⊆ mkWeakestFixpointAux f j
  := by
    intro h_ij
    induction h_ij with
    | refl => simp [Subset]
    | step =>
      rename_i j' _ _
      have := mkWeakestFixpointAux_monotonic_consecutive f h_scott j'
      simp_all [Subset]

public
theorem mkWeakestFixpoint_is_fixpoint
  {α: Type u}
  (f: Set α → Set α)
  (h_scott: IsScottContinuous f)
  : f (mkWeakestFixpoint f) = mkWeakestFixpoint f
  := by
    unfold mkWeakestFixpoint
    have := h_scott (mkWeakestFixpointAux f) (mkWeakestFixpointAux_monotonic f h_scott)
    rewrite [this]
    ext x
    simp [Chain.union, Chain.map]
    have: ∀ n, f (mkWeakestFixpointAux f n) x = mkWeakestFixpointAux f (n+1) x := by
      intro n
      conv =>
        rhs
        unfold mkWeakestFixpointAux
        simp
    simp only [this]
    constructor
    · rintro ⟨ n, h_n ⟩
      exists n+1
    · rintro ⟨ n, h_n ⟩
      by_cases n = 0
      · unfold mkWeakestFixpointAux at h_n
        subst_vars
        simp at h_n
      · exists n-1
        unfold mkWeakestFixpointAux
        unfold mkWeakestFixpointAux at h_n
        simp_all

theorem mkWeakestFixpoint_is_weakest_aux
  {α: Type u}
  (f: Set α → Set α)
  (h_scott: IsScottContinuous f)
  (set: Set α)
  (n: Nat)
  :
  (f set) ⊆ set →
  mkWeakestFixpointAux f n ⊆ set
  := by
    induction n with
    | zero =>
      unfold mkWeakestFixpointAux
      simp [Subset]
    | succ n ih =>
      unfold mkWeakestFixpointAux
      have := isScottContinuous_implies_isMonotonic f h_scott (mkWeakestFixpointAux f n) set
      simp
      intro h
      simp_all [Subset]

public
theorem mkWeakestFixpoint_is_weakest
  {α: Type u}
  (f: Set α → Set α)
  (h_scott: IsScottContinuous f)
  (set: Set α)
  :
  (f set) ⊆ set →
  mkWeakestFixpoint f ⊆ set
  := by
    intro h
    simp [mkWeakestFixpoint, Chain.union, Subset]
    intro x n
    have := mkWeakestFixpoint_is_weakest_aux f h_scott set n h
    simp_all [Subset]

@[expose]
public
def combine {α: Type u} {Id: Type} (fs: Id → (Set α → Set α)) (set: Set α): Set α :=
  fun x => ∃ id, fs id set x

public
theorem combine_isScottContinuous
  {α: Type u}
  {Id: Type}
  (fs: Id → (Set α → Set α))
  (h_fs: ∀ id, IsScottContinuous (fs id))
  : IsScottContinuous (combine fs)
  := by
    intro chain h_chain
    unfold combine
    ext x
    constructor
    · intro ⟨id, h_f⟩
      have := h_fs id chain h_chain
      simp_all [Chain.union, Chain.map]
      grind
    · intro h
      have ⟨n, id, h_id⟩ := h
      have := h_fs id chain h_chain
      exists id
      simp_all only
      exists n

@[expose]
public
def Forall {α: Type u} (p: α → Prop) (l: List α): Prop :=
  ∀ x, x ∈ l → p x

public
theorem isScottContinuous_Forall_lemma
  {α: Type u}
  (chain: Chain α)
  (h_chain: chain.IsDirected)
  (l: List α)
  :
    Forall (chain.union) l =
    exists n, Forall (chain n) l
  := by
    simp only [eq_iff_iff]
    constructor
    · induction l with
      | nil => simp [Forall, Chain.union]
      | cons h t ih =>
        simp only [Forall, List.mem_cons, Chain.union, forall_eq_or_imp, and_imp, forall_exists_index]
        intro nh h_nh h_t
        have ⟨nt, h_nt⟩ : exists nt, Forall (chain nt) t := by simp_all [Forall, Chain.union]
        exists (max nh nt)
        have := h_chain nh (max nh nt) (by grind)
        have := h_chain nt (max nh nt) (by grind)
        simp_all [Forall, Subset]
    · simp [Forall, Chain.union]
      grind

end DY.Kleene
