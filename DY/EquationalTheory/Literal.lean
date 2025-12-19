import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.EquationalTheoryInvariants
import DY.Bytes.AttackerKnowledge

namespace DY.Literal

class CanMkLiteral (Bytes: Type u) where
  literalToBytes: Nat → Bytes
  bytesToLiteral: Bytes → Option Nat

export CanMkLiteral (literalToBytes)
export CanMkLiteral (bytesToLiteral)

-- Constructors

def Literal.ctor: BytesCtor where
  data := Nat
  nBytes := 0

def Literal.View [BytesCtors] [Literal.ctor.HasCtor] := BytesView Literal.ctor.id

instance [BytesCtors] [Literal.ctor.HasCtor]: CanMkLiteral Bytes where
  literalToBytes lit :=
    ({
      data := lit,
      dataBytes := V[]
    } : Literal.View).pack

  bytesToLiteral buf :=
    match buf.view? Literal.ctor.id with
    | some { data := lit, dataBytes := V[] } =>
      some lit
    | none => none

theorem bytesToLiteral_literalToBytes
  [BytesCtors] [Literal.ctor.HasCtor]
  (lit: Nat)
  : bytesToLiteral (literalToBytes lit: Bytes) = some lit
  := by
    simp only [bytesToLiteral, literalToBytes]
    grind

theorem literalToBytes_bytesToLiteral
  [BytesCtors] [Literal.ctor.HasCtor]
  (buf: Bytes)
  :
    match bytesToLiteral buf with
    | none => True
    | some lit =>
      buf = literalToBytes lit
  := by
    simp only [bytesToLiteral, literalToBytes]
    grind

def ctors := [Literal.ctor]

instance [BytesCtors] [tc: Bytes.HasCtors ctors]: Literal.ctor.HasCtor := tc.tc (Fin.mk 0 (by simp [ctors]))

-- Equational theory

def attKnowsLit [BytesCtors] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ lit,
      out = literalToBytes lit
  pred_scott_continuous := by
    unfold Kleene.IsScottContinuous
    intro chain h_chain
    funext out
    simp [Kleene.Chain.union, Kleene.Chain.map]

def equationalTheory: EquationalTheory where
  ctors := ctors
  attackerKnowledge := [attKnowsLit]

instance: EquationalTheory.CtorsEq equationalTheory ctors where pf := rfl

instance: NeZero equationalTheory.ctors.length where
  out := by simp [equationalTheory, ctors]

theorem Literal.attacker_knows_literalToBytes
  [EquationalTheories]
  [HasEquationalTheory equationalTheory]
  (lit: Nat) (tr: Trace α)
  : (literalToBytes lit: Bytes).AttackerKnows tr
  := by
    apply Bytes.AttackerKnows.prove equationalTheory attKnowsLit
    · simp [equationalTheory]
    simp only [attKnowsLit]
    exists lit

-- Invariants

def Literal.invariants [BytesCtors]: BytesCtorInvariants.Internal Literal.ctor where
  well_formed := {
    func data dataBytes rec tr := True
    func_wf := by grind
  }
  well_formed_later data dataBytes rec_wf := by
    let V[] := dataBytes
    simp_all +arith [BytesWellFormedLaterT]

  usage := {
    func data dataBytes rec tr := Usage.nothing
    func_wf := by grind
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func data dataBytes rec tr := Label.pub
    func_wf := by grind
  }
  label_later data dataBytes rec_wf rec_usg := by grind [GetLabelLaterT]

  invariant := {
    func data dataBytes rec tr := True
    func_wf := by grind
  }
  invariant_implies_wellformed data dataBytes rec_inv rec_wf := by grind [BytesInvariantImpliesBytesWellFormedT]
  invariant_later data dataBytes rec := by grind [BytesInvariantLaterT]

class abbrev Literal.HasInvariants [BytesCtors] [BytesCtorsInvariants] [Literal.ctor.HasCtor] := HasBytesInvariants Literal.ctor.id Literal.invariants

@[simp]
theorem literalToBytes.WellFormed
  [BytesCtors] [BytesCtorsInvariants]
  [Literal.ctor.HasCtor] [Literal.HasInvariants]
  (lit: Nat) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).WellFormed tr
  := by
    simp [literalToBytes, Bytes.WellFormed.eq, Literal.invariants]

@[simp]
theorem literalToBytes.label
  [BytesCtors] [BytesCtorsInvariants]
  [Literal.ctor.HasCtor] [Literal.HasInvariants]
  (lit: Nat) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).label tr = Label.pub
  := by
    simp [literalToBytes, Bytes.label.eq, Literal.invariants]

@[simp]
theorem literalToBytes.Invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Literal.ctor.HasCtor] [Literal.HasInvariants]
  (lit: Nat) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).Invariant tr
  := by
    simp [literalToBytes, Bytes.Invariant.eq, Literal.invariants]

def EquationalTheoryInvariant [EquationalTheories]: EquationalTheoryInvariants equationalTheory where
  invariant
    | 0 => Literal.invariants

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory] [EquationalTheoryInvariant.Has]
  : HasBytesInvariants Literal.ctor.id Literal.invariants :=
  EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 0 (by simp [equationalTheory, ctors]))

-- Preserve publishability

def attKnowsLit.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Literal.HasInvariants]: attKnowsLit.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsLit]
    intro out tr ⟨lit, h_out⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

def Literal.PreservesPublishability
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory]
  [EquationalTheoryInvariant.Has]
  : EquationalTheory.PreservesPublishability equationalTheory where
  pf := by
    unfold equationalTheory
    simp
    exact attKnowsLit.preserves_publishability

end DY.Literal
