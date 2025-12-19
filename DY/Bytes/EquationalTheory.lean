import DY.Bytes.Type
import DY.Kleene

namespace DY

structure AttackerKnowledge [BytesCtors] where
  pred: (Bytes → Prop) → Bytes → Prop
  pred_scott_continuous: DY.Kleene.IsScottContinuous pred

structure EquationalTheory where
  ctors: List BytesCtor
  attackerKnowledge:
    [BytesCtors] → [Bytes.HasCtors ctors] →
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
  pf: theory.ctors = ctors

instance: EquationalTheory.CtorsEq theory theory.ctors where
  pf := rfl

class EquationalTheories where
  theories: List EquationalTheory

abbrev TheoryId [EquationalTheories]: Type := Fin (EquationalTheories.theories.length)

def BytesCtors.ofList (ctorsList: List BytesCtor): BytesCtors where
  n := ctorsList.length
  ctors i := ctorsList[i]

instance [EquationalTheories]: BytesCtors := BytesCtors.ofList (EquationalTheories.theories.flatMap EquationalTheory.ctors)

def computeCtorIndex (l: List EquationalTheory) (i: Nat): Nat :=
  match l, i with
  | [], _ => 0
  | _, 0 => 0
  | h::t, i+1 =>
    h.ctors.length + computeCtorIndex t i

theorem computeCtorIndex_in_bounds (l: List EquationalTheory) (i: Nat) (j: Nat) (h_i: i < l.length) (h_j: j < l[i].ctors.length):
  computeCtorIndex l i + j < (l.flatMap EquationalTheory.ctors).length
  := by
    induction l generalizing i with
    | nil => grind
    | cons h t ih =>
      cases i with
      | zero =>
        simp [computeCtorIndex]
        grind
      | succ i =>
        have := ih i (by grind) (by grind)
        simp [computeCtorIndex]
        simp_all +arith

theorem computeCtorIndex_getElem (l: List EquationalTheory) (i: Nat) (j: Nat) (h_i: i < l.length) (h_j: j < l[i].ctors.length):
  (l.flatMap EquationalTheory.ctors)[computeCtorIndex l i + j]'(computeCtorIndex_in_bounds l i j h_i h_j) = l[i].ctors[j]
  := by
    induction l generalizing i with
    | nil => grind
    | cons h t ih =>
      cases i with
      | zero =>
        simp [computeCtorIndex]
        grind
      | succ i =>
        have := ih i (by grind) (by grind)
        simp [computeCtorIndex]
        grind


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
  (theory: EquationalTheory)
  [inst: HasEquationalTheory theory]
  (P: (theory: EquationalTheory) → [HasEquationalTheory theory] → Sort u)
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

def EquationalTheory.toGlobalIndex [EquationalTheories] (theory: EquationalTheory) [HasEquationalTheory theory] (id: Fin theory.ctors.length): Fin BytesCtors.n :=
  Fin.mk (computeCtorIndex EquationalTheories.theories (HasEquationalTheory.id theory) + (id.val)) (by
      have := computeCtorIndex_in_bounds EquationalTheories.theories (HasEquationalTheory.id theory) (id.val) (by grind) (by
        have := HasEquationalTheory.pf theory
        simp_all
      )
      unfold BytesCtors.n instBytesCtorsOfEquationalTheories BytesCtors.ofList
      assumption
    )

def EquationalTheory.toGlobalIndex_correct [EquationalTheories] (theory: EquationalTheory) [HasEquationalTheory theory] (id: Fin theory.ctors.length):
  BytesCtors.ctors (theory.toGlobalIndex id) = theory.ctors[id]
  := by
    have := computeCtorIndex_getElem EquationalTheories.theories (HasEquationalTheory.id theory) (id.val) (by grind) (by
      have := HasEquationalTheory.pf theory
      simp_all
    )
    unfold BytesCtors.ctors instBytesCtorsOfEquationalTheories BytesCtors.ofList EquationalTheory.toGlobalIndex
    have := HasEquationalTheory.pf theory
    simp_all

structure EquationalTheories.CtorId [EquationalTheories] where
  idThy: TheoryId
  idCtor: Fin (EquationalTheories.theories[idThy].ctors.length)

def fromGlobalIndexAux (l: List EquationalTheory) (id: Nat): Nat × Nat :=
  match l with
  | [] => (0, 0) -- unreachable
  | h::t =>
    if id < h.ctors.length then (0, id)
    else
      let (x, y) := fromGlobalIndexAux t (id - h.ctors.length)
      (x+1, y)

def fromGlobalIndexAux_in_bounds_1 (l: List EquationalTheory) (id: Nat)
  (h_id: id < (BytesCtors.ofList (l.flatMap EquationalTheory.ctors)).n)
  :
  (fromGlobalIndexAux l id).1 < l.length
  := by
    fun_induction fromGlobalIndexAux <;>
    grind [BytesCtors.n, BytesCtors.ofList]

def fromGlobalIndexAux_in_bounds_2 (l: List EquationalTheory) (id: Nat)
  (h_id: id < (BytesCtors.ofList (l.flatMap EquationalTheory.ctors)).n)
  :
  (fromGlobalIndexAux l id).2 < (l[(fromGlobalIndexAux l id).1]'(fromGlobalIndexAux_in_bounds_1 l id h_id)).ctors.length
  := by
    fun_induction fromGlobalIndexAux <;>
    grind [fromGlobalIndexAux, BytesCtors.n, BytesCtors.ofList]

def fromGlobalIndex [EquationalTheories] (id: CtorId): EquationalTheories.CtorId where
  idThy := Fin.mk (fromGlobalIndexAux EquationalTheories.theories id).1 (fromGlobalIndexAux_in_bounds_1 EquationalTheories.theories id.val id.isLt)
  idCtor := Fin.mk (fromGlobalIndexAux EquationalTheories.theories id).2 (fromGlobalIndexAux_in_bounds_2 EquationalTheories.theories id.val id.isLt)

theorem fromGlobalIndexAux_correct
  (l: List EquationalTheory) (id: Nat)
  (h_id: id < (BytesCtors.ofList (l.flatMap EquationalTheory.ctors)).n)
  : (l[(fromGlobalIndexAux l id).1]'(fromGlobalIndexAux_in_bounds_1 l id h_id)).ctors[(fromGlobalIndexAux l id).2]'(fromGlobalIndexAux_in_bounds_2 l id h_id) = (BytesCtors.ofList (l.flatMap EquationalTheory.ctors)).ctors (Fin.mk id h_id)
  := by
    fun_induction fromGlobalIndexAux
    · grind [fromGlobalIndexAux, BytesCtors.n, BytesCtors.ofList]
    · simp_all [fromGlobalIndexAux, BytesCtors.n, BytesCtors.ofList]
    · simp only [BytesCtors.ofList, List.flatMap_cons, BytesCtors.n] at h_id
      simp_all [fromGlobalIndexAux, BytesCtors.n, BytesCtors.ofList]
      grind

theorem fromGlobalIndex_correct
  [EquationalTheories]
  (id: CtorId)
  : EquationalTheories.theories[(fromGlobalIndex id).idThy].ctors[(fromGlobalIndex id).idCtor] = (BytesCtors.ctors id)
  := by
    apply fromGlobalIndexAux_correct EquationalTheories.theories id.val id.isLt

theorem fromGlobalIndexAux_roundtrip
  (l: List EquationalTheory)
  (idThy: Nat) (idCtor: Nat)
  (h_idThy: idThy < l.length)
  (h_idCtor: idCtor < l[idThy].ctors.length)
  : (fromGlobalIndexAux l ((computeCtorIndex l idThy) + idCtor)) = (idThy, idCtor)
  := by
    fun_induction computeCtorIndex
    · unfold List.length at h_idThy
      simp_all
    · unfold fromGlobalIndexAux
      grind
    · simp_all [fromGlobalIndexAux]
      grind

theorem fromGlobalIndex_roundtrip
  [EquationalTheories]
  (idThy: TheoryId) (idCtor: Fin (EquationalTheories.theories[idThy].ctors.length))
  : (fromGlobalIndex (EquationalTheories.theories[idThy].toGlobalIndex idCtor)) = {idThy, idCtor}
  := by
    unfold fromGlobalIndex EquationalTheory.toGlobalIndex
    have := fromGlobalIndexAux_roundtrip EquationalTheories.theories idThy.val idCtor.val idThy.isLt idCtor.isLt
    simp_all [HasEquationalTheory.id]
    obtain ⟨ idCtor, h_idCtor ⟩ := idCtor
    grind

instance [EquationalTheories] (theory: EquationalTheory) [HasEquationalTheory theory] [theory.CtorsEq ctors]: Bytes.HasCtors ctors where
  tc id_thy := {
    id := theory.toGlobalIndex (EquationalTheory.CtorsEq.pf (theory := theory) (ctors := ctors) ▸ id_thy)
    pf := EquationalTheory.CtorsEq.pf (theory := theory) (ctors := ctors) ▸ theory.toGlobalIndex_correct (EquationalTheory.CtorsEq.pf (theory := theory) (ctors := ctors) ▸ id_thy)
  }

instance
  [EquationalTheories]
  (theory: EquationalTheory) [HasEquationalTheory theory]
  (id: Fin theory.ctors.length)
  : theory.ctors[id].HasCtorAt (theory.toGlobalIndex id)
  where
    pf := theory.toGlobalIndex_correct id

end DY
