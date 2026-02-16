/-
  This module allows to derive `DecidableEq`
  on inductives defined modularly through the "à la carte" system
-/

module

public import DY.ALaCarte.Basic

namespace DY.ALaCarte

theorem BareContainer.decideEquality.aux
  {α: Type} [SizeOf α]
  (l1 l2: Array α)
  (h1: ∀ x, x ∈ l1 → sizeOf x < max (sizeOf l1) (sizeOf l2))
  (h2: ∀ x, x ∈ l2 → sizeOf x < max (sizeOf l1) (sizeOf l2))
  : (l1.attachWith _ h1 = l2.attachWith _ h2) = (l1 = l2)
:= by
  grind [Array.unattach_attachWith]

def BareContainer.decideEquality
  {CtorId} {ctors: Ctors CtorId}
  [DecidableEq CtorId]
  [∀ id, DecidableEq (ctors id).Data]
  (x1 x2: BareContainer ctors)
  : Decidable (x1 = x2)
:= by
  let { id := id1, data := data1, as := as1 } := x1
  let { id := id2, data := data2, as := as2 } := x2
  simp only [BareContainer.mk.injEq]
  by_cases (decide (id1 = id2)) <;> rename_i h_id
  · simp only [decide_eq_true_eq] at h_id
    subst h_id
    simp only [heq_eq_eq, true_and]
    by_cases (decide (data1 = data2)) <;> rename_i h_data
    · simp only [decide_eq_true_eq] at h_data
      subst h_data
      simp only [true_and]
      rewrite [← BareContainer.decideEquality.aux]
      · refine @Array.instDecidableEq _ ?_ _ _
        intro ⟨x1, h_x1⟩ ⟨x2, h_x2⟩
        simp only [Subtype.mk.injEq]
        apply BareContainer.decideEquality
      all_goals
      intro x h_x
      have := Array.sizeOf_lt_of_mem h_x
      grind
    · left
      simp_all
  · left
    simp_all
termination_by max (sizeOf x1) (sizeOf x2)

public
def Container.decideEquality
  {CtorId} {ctors: Ctors CtorId}
  [DecidableEq CtorId]
  [∀ id, DecidableEq (ctors id).Data]
  (x1 x2: Container ctors)
  : Decidable (x1 = x2)
:= by
  cases x1
  cases x2
  rewrite [Subtype.mk.injEq]
  apply BareContainer.decideEquality

public
class RepresentableDecidableEq (f: Type → Type) [FunctorSizeOf f] [Representable f] where
  ctorid_deq: DecidableEq (Representable.CtorId f) := by
    simp only [DY.ALaCarte.Representable.CtorId]
    exact inferInstance
  ctor_data_deq: ∀ id, DecidableEq (Representable.ctors (f := f) id).Data := by
    intro id
    simp only [DY.ALaCarte.Representable.ctors]
    cases id <;>
    exact inferInstance

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableDecidableEq f]: DecidableEq (ContainerFor f)
  := @Container.decideEquality _ _ (RepresentableDecidableEq.ctorid_deq (f := f)) (RepresentableDecidableEq.ctor_data_deq (f := f))

public
instance {a: Type} [DecidableEq a] (fs: a → Type → Type) [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableDecidableEq (fs id)]: RepresentableDecidableEq (FunctorUnion fs) where
  ctorid_deq := by
    intro { idHead := idHead1, idTail := idTail1 } { idHead := idHead2, idTail := idTail2 }
    by_cases decide (idHead1 = idHead2) <;> rename_i h_idHead
    · simp only [decide_eq_true_eq] at h_idHead
      subst h_idHead
      have := RepresentableDecidableEq.ctorid_deq (f := fs idHead1)
      by_cases (decide (idTail1 = idTail2))
      · right
        grind
      · left
        grind
    · left
      grind
  ctor_data_deq id := (RepresentableDecidableEq.ctor_data_deq (f := fs id.idHead)) id.idTail

end DY.ALaCarte
