/-
  This module allows to derive `Ord` and associated properties
  on inductives defined modularly through the "à la carte" system
-/

module

public import DY.ALaCarte.Basic

namespace DY.ALaCarte

/-
  Below are functions and theorems on List and Array
  to handle functions and theorems that call themselves
  recursively through compareLex and associated theorems.
-/

def Array.attachWithSize
  {α: Type} [SizeOf α]
  (arr: Array α) (n: Nat) (H : sizeOf arr ≤ n := by grind)
  : Array {x: α // sizeOf x < n}
:=
  arr.attachWith (fun x => sizeOf x < n) (by
    intro h h_x
    have := Array.sizeOf_lt_of_mem h_x
    grind
  )

def List.attachWithSize
  {α: Type} [SizeOf α]
  (l: List α) (n: Nat) (H : sizeOf l ≤ n := by grind)
  : List {x: α // sizeOf x < n}
:=
  l.attachWith (fun x => sizeOf x < n) (by
    intro h h_x
    have := List.sizeOf_lt_of_mem h_x
    grind [List.sizeOf_lt_of_mem]
  )

theorem Array.attachWithSize_eq_attachWithSize_toList
  {α: Type} [SizeOf α]
  (arr: Array α) (n: Nat) (H : sizeOf arr ≤ n)
  : (Array.attachWithSize arr n H).toList = List.attachWithSize arr.toList n (by cases arr; simp_all; grind)
:= by
  rfl


@[wf_preprocess]
theorem Array.compareLex_wfParam
  {α: Type} [SizeOf α]
  (cmp: α → α → Ordering) (arr1: Array α) (arr2: Array α)
  : Array.compareLex cmp (wfParam arr1) (wfParam arr2) = Array.compareLex cmp ((Array.attachWithSize arr1 (max (sizeOf arr1) (sizeOf arr2))).unattach) ((Array.attachWithSize arr2 (max (sizeOf arr1) (sizeOf arr2))).unattach)
:= by
  cases arr1; rename_i l1
  cases arr2; rename_i l2
  simp only [Array.compareLex_eq_compareLex_toList, Array.toList_unattach, Array.attachWithSize_eq_attachWithSize_toList, wfParam, Array.mk.sizeOf_spec]
  fun_induction List.compareLex cmp l1 l2
  all_goals
  conv => rhs; unfold List.compareLex
  simp_all [List.attachWithSize]

theorem List.unattach_eq_nil
  {α: Type u} {P: α → Prop}
  (l: List (Subtype P))
  : l.unattach = [] ↔ l = []
:= by
  cases l <;> simp

@[wf_preprocess]
theorem Array.compareLex_unattach
  {P: α → Prop}
  (cmp: α → α → Ordering)
  (arr1 arr2 : Array (Subtype P))
  : Array.compareLex cmp arr1.unattach arr2.unattach =
    Array.compareLex (fun x1 x2 => cmp (wfParam x1.val) (wfParam x2.val)) arr1 arr2
:= by
  cases arr1; rename_i l1
  cases arr2; rename_i l2
  simp only [List.unattach_toArray, Array.compareLex_eq_compareLex_toList, wfParam]
  fun_induction List.compareLex (fun x1 x2 => cmp x1.val x2.val) l1 l2
  · simp [List.compareLex]
  · unfold List.compareLex
    split <;> simp_all [List.unattach_eq_nil]
  · unfold List.compareLex
    split <;> simp_all [List.unattach_eq_nil]
  · unfold List.compareLex
    split <;> simp_all
  · simp [List.compareLex]
    split <;> simp_all
  · unfold List.compareLex
    split <;> simp_all


/-
  Comparison function for BareContainer
-/
def BareContainer.compare
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  (x1 x2: BareContainer ctors)
  : Ordering
:=
  let {id := id1, data := data1, as := as1} := x1
  let {id := id2, data := data2, as := as2} := x2
  match h: Ord.compare id1 id2 with
  | .lt => .lt
  | .gt => .gt
  | .eq => by
    simp at h
    subst h
    exact (
      Ordering.then (Ord.compare data1 data2) (Array.compareLex BareContainer.compare as1 as2)
    )
termination_by max (sizeOf (self := BareContainer._sizeOf_inst ctors) x1) (sizeOf (self := BareContainer._sizeOf_inst ctors) x2)
decreasing_by
  simp_all
  grind

theorem List.compareLex.into_attachWithSize.aux
  {α: Type} [SizeOf α]
  (l1 l2: List α)
  (n: Nat)
  (h_n: max (sizeOf l1) (sizeOf l2) ≤ n)
  (cmp: α → α → Ordering)
  : List.compareLex cmp l1 l2 = List.compareLex (fun x y => cmp x.val y.val) (List.attachWithSize l1 n) (List.attachWithSize l2 n)
:= by
  unfold List.attachWithSize
  fun_induction List.compareLex
  <;> simp_all [List.compareLex]
  simp at h_n --?
  grind

def List.compareLex.into_attachWith
  {α: Type} [SizeOf α]
  (l1 l2: List α)
  (cmp: α → α → Ordering)
:=
  List.compareLex.into_attachWithSize.aux l1 l2 (max (sizeOf l1) (sizeOf l2)) (by grind) cmp

def List.compareLex.into_attachWith_flip
  {α: Type} [SizeOf α]
  (l1 l2: List α)
  (cmp: α → α → Ordering)
:=
  List.compareLex.into_attachWithSize.aux l1 l2 (max (sizeOf l2) (sizeOf l1)) (by grind) cmp

/-
  Theorems about List.compareLex, but without going through the typeclass instances.
-/

theorem List.compareLex.compare_self
  {α: Type}
  (cmp: α → α → Ordering)
  (h_cmp: ∀ x, cmp x x = .eq)
  (l: List α)
  : List.compareLex cmp l l = .eq
:= by
  refine Std.ReflCmp.compare_self (self := @List.instReflCmpCompareLex _ _ ?_)
  constructor
  grind

theorem List.compareLex.eq_of_compare
  {α: Type}
  (cmp: α → α → Ordering)
  (h_cmp1: ∀ x, cmp x x = .eq)
  (h_cmp2: ∀ x1 x2, cmp x1 x2 = .eq → x1 = x2)
  (l1 l2: List α)
  : List.compareLex cmp l1 l2 = .eq → l1 = l2
:= by
  refine Std.LawfulEqCmp.eq_of_compare (self := @List.instLawfulEqCmpCompareLex _ _ ?_)
  refine @Std.LawfulEqCmp.mk _ _ ?_ ?_
  · constructor
    grind
  grind

theorem List.compareLex.eq_swap
  {α: Type}
  (cmp: α → α → Ordering)
  (h_cmp: ∀ x1 x2, cmp x1 x2 = (cmp x2 x1).swap)
  (l1 l2: List α)
  : List.compareLex cmp l1 l2 = (List.compareLex cmp l2 l1).swap
:= by
  refine Std.OrientedCmp.eq_swap (self := @List.instOrientedCmpCompareLex _ _ ?_)
  constructor
  grind

theorem List.compareLex.isLE_trans
  {α: Type}
  (cmp: α → α → Ordering)
  (h_cmp1: ∀ x1 x2, cmp x1 x2 = (cmp x2 x1).swap)
  (h_cmp2: ∀ x1 x2 x3, (cmp x1 x2).isLE → (cmp x2 x3).isLE → (cmp x1 x3).isLE)
  (l1 l2 l3: List α)
  : (List.compareLex cmp l1 l2).isLE → (List.compareLex cmp l2 l3).isLE → (List.compareLex cmp l1 l3).isLE
:= by
  refine Std.TransCmp.isLE_trans (self := @List.instTransCmpCompareLex _ _ ?_)
  refine @Std.TransCmp.mk _ _ ?_ ?_
  · constructor
    grind
  grind

/-
  Theorems on BareContainer.compare
-/

theorem BareContainer.compare.compare_self
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.ReflOrd (ctors id).Data]
  (x: BareContainer ctors)
  : compare x x = .eq
:= by
  let {id, data, as} := x
  unfold BareContainer.compare
  simp only
  have id_refl: Ord.compare id id = .eq := by simp
  rewrite [id_refl]
  dsimp only
  simp only [Std.compare_self, Ordering.eq_then]
  rewrite [Array.compareLex_eq_compareLex_toList, List.compareLex.into_attachWith]
  apply List.compareLex.compare_self
  intro
  apply BareContainer.compare.compare_self
decreasing_by
  rename_i x
  cases as
  cases x
  simp
  grind

theorem BareContainer.compare.lawful_eq.attachWith_eq
  {α: Type} [SizeOf α]
  (l1 l2: List α)
  (h1: ∀ x, x ∈ l1 → sizeOf x < max (sizeOf l1) (sizeOf l2))
  (h2: ∀ x, x ∈ l2 → sizeOf x < max (sizeOf l1) (sizeOf l2))
  : (l1.attachWith _ h1 = l2.attachWith _ h2) = (l1 = l2)
:= by
  grind [List.unattach_attachWith]

theorem BareContainer.compare.eq_of_compare
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.LawfulEqOrd (ctors id).Data]
  (x1 x2: BareContainer ctors)
  : compare x1 x2 = .eq → x1 = x2
:= by
  let {id := id1, data := data1, as := { toList := l1 }} := x1
  let {id := id2, data := data2, as := { toList := l2 }} := x2
  simp only [BareContainer.compare, BareContainer.mk.injEq]
  split
  · simp
  · simp
  rename_i heq
  have heq := Std.LawfulEqOrd.eq_of_compare heq
  subst heq
  dsimp only [Ordering.then]
  split
  · rename_i heq
    have := Std.LawfulEqOrd.eq_of_compare heq
    simp_all only [Std.compare_self, heq_eq_eq, true_and]
    rewrite [Array.compareLex_eq_compareLex_toList, List.compareLex.into_attachWith]
    simp only [Array.mk.injEq]
    rewrite [←BareContainer.compare.lawful_eq.attachWith_eq l1 l2]
    apply List.compareLex.eq_of_compare
    · intro
      apply BareContainer.compare.compare_self
    · intro ⟨a, h_a⟩ ⟨b, h_b⟩
      simp only [Subtype.mk.injEq]
      apply BareContainer.compare.eq_of_compare
    all_goals
    intro x h_x
    have := List.sizeOf_lt_of_mem h_x
    grind [List.sizeOf_lt_of_mem]
  · grind
termination_by max (sizeOf x1) (sizeOf x2)
decreasing_by
  simp
  grind

theorem BareContainer.compare.eq_swap
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [Std.OrientedOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.OrientedOrd (ctors id).Data]
  (x1 x2: BareContainer ctors)
  : compare x1 x2 = (compare x2 x1).swap
:= by
  let {id := id1, data := data1, as := { toList := l1 }} := x1
  let {id := id2, data := data2, as := { toList := l2 }} := x2
  simp only [BareContainer.compare]
  have id_swap: Ord.compare id1 id2 = (Ord.compare id2 id1).swap := Std.OrientedOrd.eq_swap
  split
  · grind
  · grind
  rename_i heq
  have heq := Std.LawfulEqOrd.eq_of_compare heq
  subst heq
  dsimp only [Ordering.then]
  have data_swap: Ord.compare data1 data2 = (Ord.compare data2 data1).swap := Std.OrientedOrd.eq_swap
  split
  · simp only [Array.compareLex_eq_compareLex_toList]
    rewrite (occs := [2]) [List.compareLex.into_attachWith_flip]
    rewrite (occs := [1]) [List.compareLex.into_attachWith]
    have := List.compareLex.eq_swap (fun x y => x.val.compare y.val) (by
      intro ⟨a, h_a⟩ ⟨b, h_b⟩
      dsimp only
      apply BareContainer.compare.eq_swap
    ) (List.attachWithSize l1 (max (sizeOf l1) (sizeOf l2))) (List.attachWithSize l2 (max (sizeOf l1) (sizeOf l2)))
    split
    · grind
    · grind
    split
    · grind
    · simp [Ordering.swap] at data_swap
      grind
  · grind
termination_by max (sizeOf x1) (sizeOf x2)
decreasing_by
  simp
  grind

theorem transLtToLe
  {a: Type u}
  (r: a → a → Ordering)
  (h_lawful: ∀ x y, (r x y) = .eq → x = y)
  (x y z: a)
  (h_translt: (r x y) = .lt → (r y z) = .lt → (r x z) = .lt)
  : (r x y).isLE → (r y z).isLE → (r x z).isLE
:= by
  simp only [Ordering.isLE]
  grind [cases Ordering]

theorem transLeToLt
  {a: Type u}
  (r: a → a → Ordering)
  (h_lawful: ∀ x y, (r x y) = .eq → x = y)
  (h_swap: ∀ x y, (r x y) = (r y x).swap)
  (x y z: a)
  (h_transle: (r x y).isLE → (r y z).isLE → (r x z).isLE)
  : (r x y) = .lt → (r y z) = .lt → (r x z) = .lt
:= by
  unfold Ordering.swap at h_swap
  unfold Ordering.isLE at h_transle
  grind [cases Ordering]

theorem BareContainer.compare.isLE_trans
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [Std.TransOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.LawfulEqOrd (ctors id).Data]
  [∀ id, Std.TransOrd (ctors id).Data]
  (x1 x2 x3: BareContainer ctors)
  : (compare x1 x2).isLE → (compare x2 x3).isLE → (compare x1 x3).isLE
:= by
  apply transLtToLe
  · apply BareContainer.compare.eq_of_compare
  let {id := id1, data := data1, as := { toList := l1} } := x1
  let {id := id2, data := data2, as := { toList := l2} } := x2
  let {id := id3, data := data3, as := { toList := l3} } := x3
  simp only [BareContainer.compare, Ordering.then]
  intro h12 h23
  split at h12 <;> rename_i h_id12
  · split at h23 <;> rename_i h_id23
    · have := Std.TransCmp.lt_trans h_id12 h_id23
      grind
    · contradiction
    · grind
  · contradiction
  split at h23 <;> rename_i h_id23
  · grind
  · contradiction
  have h_id12_eq := Std.LawfulEqOrd.eq_of_compare h_id12
  have h_id23_eq := Std.LawfulEqOrd.eq_of_compare h_id23
  subst h_id12_eq
  subst h_id23_eq
  dsimp only at *
  rewrite [h_id12]
  dsimp only
  split at h12 <;> rename_i h_data12
  · split at h23 <;> rename_i h_data23
    · have h_data12_eq := Std.LawfulEqOrd.eq_of_compare h_data12
      have h_data23_eq := Std.LawfulEqOrd.eq_of_compare h_data23
      subst h_data12_eq
      subst h_data23_eq
      simp only [h_data12]
      revert h12 h23
      simp only [Array.compareLex_eq_compareLex_toList]
      apply transLeToLt
      · apply List.compareLex.eq_of_compare
        · apply BareContainer.compare.compare_self
        · apply BareContainer.compare.eq_of_compare
      · apply List.compareLex.eq_swap
        apply BareContainer.compare.eq_swap
      simp only [List.compareLex.into_attachWithSize.aux l1 l2 (max (max (sizeOf l1) (sizeOf l2)) (sizeOf l3)) (by grind) BareContainer.compare]
      simp only [List.compareLex.into_attachWithSize.aux l2 l3 (max (max (sizeOf l1) (sizeOf l2)) (sizeOf l3)) (by grind) BareContainer.compare]
      simp only [List.compareLex.into_attachWithSize.aux l1 l3 (max (max (sizeOf l1) (sizeOf l2)) (sizeOf l3)) (by grind) BareContainer.compare]
      apply List.compareLex.isLE_trans
      · intro ⟨a, h_a⟩ ⟨b, h_b⟩
        dsimp only
        apply BareContainer.compare.eq_swap
      intro ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨c, h_c⟩
      dsimp only
      apply BareContainer.compare.isLE_trans
    · grind
  · split at h23 <;> rename_i h_data23
    · grind
    · have := Std.TransCmp.lt_trans h12 h23
      grind
termination_by (max (max (sizeOf x1) (sizeOf x2)) (sizeOf x3))
decreasing_by
  simp_all
  grind

/-
  Comparison function for BareContainer
-/

public
def Container.compare
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  (x1 x2: Container ctors)
  : Ordering
:=
  BareContainer.compare x1.val x2.val

/-
  Theorems on Container.compare
-/

public
theorem Container.compare.compare_self
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.ReflOrd (ctors id).Data]
  (x: Container ctors)
  : compare x x = .eq
:= by
  cases x
  simp [Container.compare]
  apply BareContainer.compare.compare_self

public
theorem Container.compare.eq_of_compare
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.LawfulEqOrd (ctors id).Data]
  (x1 x2: Container ctors)
  : compare x1 x2 = .eq → x1 = x2
:= by
  cases x1; cases x2
  rewrite [Subtype.mk.injEq]
  simp [Container.compare]
  apply BareContainer.compare.eq_of_compare

public
theorem Container.compare.eq_swap
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [Std.OrientedOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.OrientedOrd (ctors id).Data]
  (x1 x2: Container ctors)
  : compare x1 x2 = (compare x2 x1).swap
:= by
  cases x1; cases x2
  simp [Container.compare]
  apply BareContainer.compare.eq_swap

public
theorem Container.compare.isLE_trans
  {CtorId} {ctors: Ctors CtorId}
  [Ord CtorId] [Std.LawfulEqOrd CtorId]
  [Std.TransOrd CtorId]
  [∀ id, Ord (ctors id).Data]
  [∀ id, Std.LawfulEqOrd (ctors id).Data]
  [∀ id, Std.TransOrd (ctors id).Data]
  (x1 x2 x3: Container ctors)
  : (compare x1 x2).isLE → (compare x2 x3).isLE → (compare x1 x3).isLE
:= by
  cases x1; cases x2; cases x3
  simp [Container.compare]
  apply BareContainer.compare.isLE_trans

public
class RepresentableOrd (f: Type → Type) [FunctorSizeOf f] [Representable f] where
  ctoridOrd: Ord (Representable.CtorId f) := by
    simp only [ALaCarte.Representable.CtorId]
    infer_instance
  ctoridOrd_lawfulEq: Std.LawfulEqOrd (Representable.CtorId f) := by
    simp only [ALaCarte.Representable.CtorId]
    dsimp +instances
    infer_instance
  ctoridOrd_trans: Std.TransOrd (Representable.CtorId f) := by
    simp only [ALaCarte.Representable.CtorId]
    dsimp +instances
    infer_instance

  ctorDataOrd: ∀ id, Ord (Representable.ctors (f := f) id).Data := by
    intro id
    simp only [ALaCarte.Representable.ctors]
    cases id
    all_goals
      infer_instance
  ctorDataOrd_lawfulEq: ∀ id, Std.LawfulEqOrd (Representable.ctors (f := f) id).Data := by
    intro id
    simp only [ALaCarte.Representable.ctors]
    cases id
    all_goals
      dsimp +instances
      infer_instance
  ctorDataOrd_trans: ∀ id, Std.TransOrd (Representable.ctors (f := f) id).Data := by
    intro id
    simp only [ALaCarte.Representable.ctors]
    cases id
    all_goals
      dsimp +instances
      infer_instance

section FunctorUnionOrd

public local instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [inst: RepresentableOrd f]: Ord (Representable.CtorId f) := inst.ctoridOrd
public local instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [inst: RepresentableOrd f]: Std.LawfulEqOrd (Representable.CtorId f) := inst.ctoridOrd_lawfulEq
local instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [inst: RepresentableOrd f]: Std.TransOrd (Representable.CtorId f) := inst.ctoridOrd_trans

public local instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [inst: RepresentableOrd f] (id: Representable.CtorId f): Ord (Representable.ctors (f := f) id).Data := inst.ctorDataOrd id
local instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [inst: RepresentableOrd f] (id: Representable.CtorId f): Std.LawfulEqOrd (Representable.ctors (f := f) id).Data := inst.ctorDataOrd_lawfulEq id
local instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [inst: RepresentableOrd f] (id: Representable.CtorId f): Std.TransOrd (Representable.ctors (f := f) id).Data := inst.ctorDataOrd_trans id

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableOrd f]: Ord (ContainerFor f) where
  compare := Container.compare

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableOrd f]: Std.ReflOrd (ContainerFor f) where
  compare_self {x} := Container.compare.compare_self x

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableOrd f]: Std.LawfulEqOrd (ContainerFor f) where
  eq_of_compare {x1} {x2} := Container.compare.eq_of_compare x1 x2

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableOrd f]: Std.OrientedOrd (ContainerFor f) where
  eq_swap {x1} {x2} := Container.compare.eq_swap x1 x2

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableOrd f]: Std.TransOrd (ContainerFor f) where
  isLE_trans {x1} {x2} {x3} := Container.compare.isLE_trans x1 x2 x3

public
def FunctorUnion.CtorId.compare
  {a: Type}
  [Ord a] [Std.LawfulEqOrd a]
  {fs: a → Type → Type}
  [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableOrd (fs id)]
  (x1 x2: FunctorUnion.CtorId fs)
  : Ordering
:=
  let { idHead := idHead1, idTail := idTail1 } := x1
  let { idHead := idHead2, idTail := idTail2 } := x2
  match h: Ord.compare idHead1 idHead2 with
  | .lt => .lt
  | .gt => .gt
  | .eq => by
    simp at h
    subst h
    exact (Ord.compare idTail1 idTail2)

public
theorem FunctorUnion.CtorId.compare.compare_self
  {a: Type}
  [Ord a] [Std.LawfulEqOrd a]
  {fs: a → Type → Type}
  [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableOrd (fs id)]
  (x: FunctorUnion.CtorId fs)
  : compare x x = .eq
:= by
  let {idHead, idTail} := x
  simp only [compare]
  have idHead_refl: Ord.compare idHead idHead = .eq := by simp
  rewrite [idHead_refl]
  simp

public
theorem FunctorUnion.CtorId.compare.eq_of_compare
  {a: Type}
  [Ord a] [Std.LawfulEqOrd a]
  {fs: a → Type → Type}
  [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableOrd (fs id)]
  (x1 x2: FunctorUnion.CtorId fs)
  : compare x1 x2 = .eq → x1 = x2
:= by
  let { idHead := idHead1, idTail := idTail1 } := x1
  let { idHead := idHead2, idTail := idTail2 } := x2
  simp only [compare]
  split
  · grind
  · grind
  · have : idHead1 = idHead2 := by grind
    subst this
    grind

public
theorem FunctorUnion.CtorId.compare.eq_swap
  {a: Type}
  [Ord a] [Std.LawfulEqOrd a] [Std.OrientedOrd a]
  {fs: a → Type → Type}
  [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableOrd (fs id)]
  (x1 x2: FunctorUnion.CtorId fs)
  : compare x1 x2 = (compare x2 x1).swap
:= by
  let { idHead := idHead1, idTail := idTail1 } := x1
  let { idHead := idHead2, idTail := idTail2 } := x2
  simp only [compare]
  have idHead_swap: Ord.compare idHead1 idHead2 = (Ord.compare idHead2 idHead1).swap := Std.OrientedOrd.eq_swap
  split
  · split <;> grind
  · split <;> grind
  have heq: idHead1 = idHead2 := by grind
  subst heq
  dsimp only
  have idTail_swap: Ord.compare idTail1 idTail2 = (Ord.compare idTail2 idTail1).swap := Std.OrientedOrd.eq_swap
  split <;> grind

public
theorem FunctorUnion.CtorId.compare.isLE_trans
  {a: Type}
  [Ord a] [Std.LawfulEqOrd a] [Std.TransOrd a]
  {fs: a → Type → Type}
  [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableOrd (fs id)]
  (x1 x2 x3: FunctorUnion.CtorId fs)
  : (compare x1 x2).isLE → (compare x2 x3).isLE → (compare x1 x3).isLE
:= by
  let { idHead := idHead1, idTail := idTail1 } := x1
  let { idHead := idHead2, idTail := idTail2 } := x2
  let { idHead := idHead3, idTail := idTail3 } := x3
  apply transLtToLe
  · apply FunctorUnion.CtorId.compare.eq_of_compare
  simp only [compare]
  intro h12 h23
  split at h12 <;> rename_i h_idHead12
  · split at h23 <;> rename_i h_idHead23
    · have := Std.TransCmp.lt_trans h_idHead12 h_idHead23
      grind
    · contradiction
    · grind
  · contradiction
  · split at h23 <;> rename_i h_idHead23
    · grind
    · contradiction
    · have h_idHead12_eq := Std.LawfulEqOrd.eq_of_compare h_idHead12
      have h_idHead23_eq := Std.LawfulEqOrd.eq_of_compare h_idHead23
      subst h_idHead12_eq
      subst h_idHead23_eq
      dsimp only at *
      rewrite [h_idHead12]
      dsimp only
      exact Std.TransCmp.lt_trans h12 h23

public
instance {a: Type} [Ord a] [Std.LawfulEqOrd a] [Std.TransOrd a] (fs: a → Type → Type) [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableOrd (fs id)]: RepresentableOrd (FunctorUnion fs) where
  ctoridOrd := {
    compare := FunctorUnion.CtorId.compare
  }
  ctoridOrd_lawfulEq := {
    compare_self {x} := FunctorUnion.CtorId.compare.compare_self x
    eq_of_compare {x1 x2} := FunctorUnion.CtorId.compare.eq_of_compare x1 x2
  }
  ctoridOrd_trans := {
    eq_swap {x1 x2} := FunctorUnion.CtorId.compare.eq_swap x1 x2
    isLE_trans {x1 x2 x3} := FunctorUnion.CtorId.compare.isLE_trans x1 x2 x3
  }

  ctorDataOrd id := (RepresentableOrd.ctorDataOrd (f := fs id.idHead)) id.idTail
  ctorDataOrd_lawfulEq id := (RepresentableOrd.ctorDataOrd_lawfulEq (f := fs id.idHead)) id.idTail
  ctorDataOrd_trans id := (RepresentableOrd.ctorDataOrd_trans (f := fs id.idHead)) id.idTail

end FunctorUnionOrd

end DY.ALaCarte
