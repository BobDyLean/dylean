import DY.Bytes.Invariants
import DY.Bytes.EquationalTheory
import DY.Bytes.AttackerKnowledge

namespace DY

def AttackerKnowledge.PreservesPublishability [BytesCtors] [BytesCtorsInvariants] (attKnows: AttackerKnowledge) :=
  ∀ out tr,
    attKnows.pred (Bytes.Publishable · tr) out →
    Bytes.Publishable out tr

structure EquationalTheory.PreservesPublishability [EquationalTheories] [BytesCtorsInvariants] (theory: EquationalTheory) [HasEquationalTheory theory] where
  pf: ∀ attKnows, attKnows ∈ theory.attackerKnowledge → attKnows.PreservesPublishability

structure EquationalTheoryInvariants [EquationalTheories] (theory: EquationalTheory) where
  invariant: (id: Fin theory.ctors.length) → BytesCtorInvariants.Internal theory.ctors[id]

class EquationalTheoryInvariants.Has [EquationalTheories] [BytesCtorsInvariants] {theory: EquationalTheory} [HasEquationalTheory theory] (eqInvs: EquationalTheoryInvariants theory) where
  pf: ∀ id, eqInvs.invariant id = (theory.toGlobalIndex_correct id) ▸ (BytesCtorsInvariants.funs (theory.toGlobalIndex id))

class EquationalTheories.Invariants [EquationalTheories] where
  invariants: (id: TheoryId) → EquationalTheoryInvariants EquationalTheories.theories[id]

instance [EquationalTheories] [EquationalTheories.Invariants]: BytesCtorsInvariants where
  funs id :=
    let idEqThy := fromGlobalIndex id
    let res: BytesCtorInvariants.Internal (BytesCtors.ctors id) := (fromGlobalIndex_correct id ▸ (EquationalTheories.Invariants.invariants idEqThy.idThy).invariant idEqThy.idCtor)
    res

instance [EquationalTheories] [EquationalTheories.Invariants] (idThy: TheoryId): (EquationalTheories.Invariants.invariants idThy).Has where
  pf idCtor := by
    unfold BytesCtorsInvariants.funs instBytesCtorsInvariantsOfInvariants
    have := fromGlobalIndex_roundtrip idThy
    grind

def EquationalTheoryInvariants.mkHasBytesInvariants
  [EquationalTheories] [EquationalTheories.Invariants]
  {theory: EquationalTheory} [HasEquationalTheory theory]
  (invariants: EquationalTheoryInvariants theory)
  [inst: invariants.Has]
  (id: Fin theory.ctors.length)
  : HasBytesInvariants (theory.toGlobalIndex id) (invariants.invariant id)
  where
    pf := by
      simp [BytesCtorsInvariants.funs, inst.pf id]
      simp [BytesCtorInvariants.into]
      sorry

class EquationalTheories.PreservesPublishability [EquationalTheories] [EquationalTheories.Invariants] where
  pf: (id: TheoryId) → EquationalTheories.theories[id].PreservesPublishability

theorem attacker_only_knows_publishable_values
  [EquationalTheories] [EquationalTheories.Invariants] [EquationalTheories.PreservesPublishability]
  (b: Bytes) (tr: ProofTrace)
  :
    b.AttackerKnows tr →
    b.Publishable tr
  := by
    apply Bytes.AttackerKnows.is_least_fixpoint (Bytes.Publishable · tr)
    intro id att out h_att h_out
    exact (EquationalTheories.PreservesPublishability.pf id).pf att h_att out tr h_out

end DY
