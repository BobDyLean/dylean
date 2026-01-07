import DY.Bytes.Type
import DY.Kleene

namespace DY

structure AttackerKnowledge {CtorId} [BytesCtors CtorId] where
  pred: (Bytes → Prop) → Bytes → Prop
  pred_scott_continuous: DY.Kleene.IsScottContinuous pred

structure EquationalTheory where
  ctors: List BytesCtor
  attackerKnowledge:
    {CtorId: Type} → [DecidableEq CtorId] →
    [BytesCtors CtorId] → [Ord Bytes] →
    [Bytes.HasCtors ctors] →
    List AttackerKnowledge

-- This typeclass is useful in the following situation:
-- def myEqThy: EquationalTheory where
--   ctors := myCtors
--   attackerKnowledge := ...
-- Then there is a mismatch between
--   Bytes.HasCtors myCtors
-- (typeclass needed by functions before we define equational theories)
-- and
--   Bytes.HasCtors myEqThy.ctors
-- (through the instance of HasEquationalTheory myEqThy)
class EquationalTheory.CtorsEq (theory: semiOutParam EquationalTheory) (ctors: List BytesCtor) where
  pf (theory ctors): theory.ctors = ctors

instance: EquationalTheory.CtorsEq theory theory.ctors where
  pf := rfl

class EquationalTheories where
  theories: List EquationalTheory

abbrev TheoryId [EquationalTheories]: Type := Fin (EquationalTheories.theories.length)

structure CtorId [EquationalTheories] where
  idThy: TheoryId
  idCtor: Fin EquationalTheories.theories[idThy].ctors.length
deriving DecidableEq

instance [EquationalTheories]: Ord CtorId where
  compare id1 id2 :=
    let {idThy := idThy1, idCtor := idCtor1} := id1
    let {idThy := idThy2, idCtor := idCtor2} := id2
    match h: compare idThy1 idThy2 with
    | .lt => .lt
    | .gt => .gt
    | .eq => by
      simp at h
      subst h
      exact (
        compare idCtor1 idCtor2
      )

instance [EquationalTheories]: Std.ReflOrd CtorId where
  compare_self {id} := by
    let {idThy, idCtor} := id
    unfold compare instOrdCtorId; simp only
    have: compare idThy idThy = .eq := by simp
    rewrite [this]
    simp

instance [EquationalTheories]: Std.LawfulEqOrd CtorId where
  eq_of_compare {id1 id2} := by
    let {idThy := idThy1, idCtor := idCtor1} := id1
    let {idThy := idThy2, idCtor := idCtor2} := id2
    unfold compare instOrdCtorId; simp only
    split
    · grind
    · grind
    · have : idThy1 = idThy2 := by grind
      subst this
      simp

instance [EquationalTheories]: Std.OrientedOrd CtorId where
  eq_swap {id1 id2} := by
    let {idThy := idThy1, idCtor := idCtor1} := id1
    let {idThy := idThy2, idCtor := idCtor2} := id2
    unfold compare instOrdCtorId; simp only
    have idThy_swap: compare idThy1 idThy2 = (compare idThy2 idThy1).swap := Std.OrientedOrd.eq_swap
    split
    · split <;> grind
    · split <;> grind
    have heq: idThy1 = idThy2 := by grind
    subst heq
    dsimp only
    have idCtor_swap: compare idCtor1 idCtor2 = (compare idCtor2 idCtor1).swap := Std.OrientedOrd.eq_swap
    split <;> grind

instance [EquationalTheories]: Std.TransOrd CtorId where
  isLE_trans := by
    apply mkTransitive
    · simp
    intro id1 id2 id3
    let {idThy := idThy1, idCtor := idCtor1} := id1
    let {idThy := idThy2, idCtor := idCtor2} := id2
    let {idThy := idThy3, idCtor := idCtor3} := id3
    unfold compare instOrdCtorId; simp only
    intro h12 h23
    split at h12 <;> rename_i h_idThy12
    · split at h23 <;> rename_i h_idThy23
      · have := Std.TransCmp.lt_trans h_idThy12 h_idThy23
        grind
      · contradiction
      · grind
    · contradiction
    · split at h23 <;> rename_i h_idThy23
      · grind
      · contradiction
      · have h_idThy12_eq := Std.LawfulEqOrd.eq_of_compare h_idThy12
        have h_idThy23_eq := Std.LawfulEqOrd.eq_of_compare h_idThy23
        subst h_idThy12_eq
        subst h_idThy23_eq
        dsimp only at *
        rewrite [h_idThy12]
        dsimp only
        exact Std.TransCmp.lt_trans h12 h23

instance [EquationalTheories]: BytesCtors CtorId where
  ctors id := EquationalTheories.theories[id.idThy].ctors[id.idCtor]

class HasEquationalTheory [EquationalTheories] (theory: EquationalTheory) where
  id: TheoryId
  pf (theory): EquationalTheories.theories[id] = theory

instance [EquationalTheories] (id: TheoryId): HasEquationalTheory (EquationalTheories.theories[id]) where
  id := id
  pf := rfl

theorem HasEquationalTheory.ext
  [EquationalTheories]
  (theory1 theory2: EquationalTheory)
  [inst1: HasEquationalTheory theory1]
  [inst2: HasEquationalTheory theory2]
  :
    inst1.id = inst2.id →
    inst1 ≍ inst2
  := by
    cases inst1
    cases inst2
    grind

def EquationalTheory.into_theory_id
  [EquationalTheories]
  {theory: EquationalTheory}
  [inst: HasEquationalTheory theory]
  {P: (theory: EquationalTheory) → [HasEquationalTheory theory] → Sort u}
  (x: P EquationalTheories.theories[inst.id])
  : P theory
  := by
    suffices h : P EquationalTheories.theories[inst.id] = P theory by
      rewrite [← h]
      exact x
    have := inst.pf
    congr
    apply HasEquationalTheory.ext
    simp [HasEquationalTheory.id]

instance [EquationalTheories] (theory: EquationalTheory) [HasEquationalTheory theory] [theory.CtorsEq ctors]: Bytes.HasCtors ctors where
  tc idCtor := {
    id := {
      idThy := HasEquationalTheory.id theory,
      idCtor := Fin.mk idCtor.val (by simp [HasEquationalTheory.pf theory, EquationalTheory.CtorsEq.pf theory ctors])
      }
    pf := by
      simp [BytesCtors.ctors, HasEquationalTheory.pf theory, EquationalTheory.CtorsEq.pf theory ctors]
  }

-- TODO: is the following useful?

def EquationalTheory.toGlobalIndex
  [EquationalTheories]
  (theory: EquationalTheory) [HasEquationalTheory theory]
  (idCtor: Fin theory.ctors.length)
  : CtorId
  where
    idThy := HasEquationalTheory.id theory
    idCtor := Fin.mk idCtor.val (by simp [HasEquationalTheory.pf theory])

def EquationalTheory.toGlobalIndex_correct
  [EquationalTheories]
  (theory: EquationalTheory) [HasEquationalTheory theory]
  (id: Fin theory.ctors.length)
  : BytesCtors.ctors (theory.toGlobalIndex id) = theory.ctors[id]
  := by
    simp [BytesCtors.ctors, EquationalTheory.toGlobalIndex, HasEquationalTheory.pf theory]

instance
  [EquationalTheories]
  (theory: EquationalTheory) [HasEquationalTheory theory]
  (id: Fin theory.ctors.length)
  : theory.ctors[id].HasCtorAt (theory.toGlobalIndex id)
  where
    pf := by simp [EquationalTheory.toGlobalIndex_correct]

end DY
