import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.EquationalTheoryInvariants
import DY.Bytes.AttackerKnowledge
import DY.Misc

namespace DY.Hash

class CanHash (Bytes: Type u) where
  hash: Bytes → Bytes

export CanHash (hash)

-- Constructors

def Hash.ctor: BytesCtor where
  data := Unit
  nBytes := 1

def Hash.View [BytesCtors] [Hash.ctor.HasCtor] := BytesView Hash.ctor.id

instance [BytesCtors] [Hash.ctor.HasCtor]: CanHash Bytes where
  hash inp :=
    ({
      data := (),
      dataBytes := V[inp]
    } : Hash.View).pack

theorem hash_inj
  [BytesCtors] [Hash.ctor.HasCtor]
  (inp1 inp2: Bytes)
  :
    hash inp1 = hash inp2 →
    inp1 = inp2
  := by
    simp only [hash]
    grind

def ctors := [Hash.ctor]

instance [BytesCtors] [tc: Bytes.HasCtors ctors]: Hash.ctor.HasCtor := tc.tc (Fin.mk 0 (by simp [ctors]))

-- Equational theory

def attKnowsHash [BytesCtors] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ inp,
      out = hash inp ∧
      p inp
  pred_scott_continuous := by
    sorry

def equationalTheory: EquationalTheory where
  ctors := ctors
  attackerKnowledge := [attKnowsHash]

instance: EquationalTheory.CtorsEq equationalTheory ctors where pf := rfl

instance: NeZero equationalTheory.ctors.length where
  out := by simp [equationalTheory, ctors]

theorem attacker_knows_hash
  [EquationalTheories]
  [HasEquationalTheory equationalTheory]
  (inp: Bytes) (tr: Trace α)
  :
    inp.AttackerKnows tr →
    (hash inp).AttackerKnows tr
  := by
    intro h_inp
    apply Bytes.AttackerKnows.prove equationalTheory attKnowsHash
    · simp [equationalTheory]
    simp only [attKnowsHash]
    grind

-- Invariants

def Hash.invariants [BytesCtors]: BytesCtorInvariants.Internal Hash.ctor where
  well_formed := {
    func := fun () V[inp] rec tr =>
      rec inp tr
  }
  well_formed_later data dataBytes rec_wf := by
    let V[inp] := dataBytes
    simp_all +arith [BytesWellFormedLaterT]
    grind

  usage := {
    func data dataBytes rec tr := Usage.nothing
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func := fun () V[inp] rec tr =>
      rec inp tr
  }
  label_later data dataBytes rec_wf rec_usg := by
    let V[inp] := dataBytes
    simp_all +arith [GetLabelLaterT]
    grind

  invariant := {
    func := fun () V[inp] rec tr =>
      rec inp tr
  }
  invariant_implies_wellformed data dataBytes rec_inv rec_wf := by
    let V[inp] := dataBytes
    simp_all +arith [BytesInvariantImpliesBytesWellFormedT]
  invariant_later data dataBytes rec := by
    let V[inp] := dataBytes
    simp_all +arith [BytesInvariantLaterT]
    grind

class abbrev Hash.HasInvariants [BytesCtors] [Hash.ctor.HasCtor] [BytesCtorsInvariants] := HasBytesInvariants (Hash.ctor.id) Hash.invariants

@[simp]
theorem hash.WellFormed
  [BytesCtors] [BytesCtorsInvariants]
  [Hash.ctor.HasCtor] [Hash.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).WellFormed tr = inp.WellFormed tr
  := by
    simp [hash, Bytes.WellFormed.eq, Hash.invariants]

@[simp]
theorem hash.label
  [BytesCtors] [BytesCtorsInvariants]
  [Hash.ctor.HasCtor] [Hash.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  : (hash inp).label tr = inp.label tr
  := by
    simp [hash, Bytes.label.eq, Hash.invariants]

@[simp]
theorem hash.Invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Hash.ctor.HasCtor] [Hash.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).Invariant tr =
    inp.Invariant tr
  := by
    simp [hash, Bytes.Invariant.eq, Hash.invariants]

def EquationalTheoryInvariant [EquationalTheories]: EquationalTheoryInvariants equationalTheory where
  invariant
    | 0 => Hash.invariants

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory] [EquationalTheoryInvariant.Has]
  : HasBytesInvariants Hash.ctor.id Hash.invariants :=
  EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 0 (by simp [equationalTheory, ctors]))

-- Preserve publishability

def attKnowsHash.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Hash.HasInvariants]: attKnowsHash.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsHash]
    intro out tr ⟨inp, ⟨ h_out, h_inp ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

def PreservesPublishability
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory]
  [EquationalTheoryInvariant.Has]
  : EquationalTheory.PreservesPublishability equationalTheory where
  pf := by
    unfold equationalTheory
    simp
    exact attKnowsHash.preserves_publishability

end DY.Hash
