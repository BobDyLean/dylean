import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.Invariants
import DY.Bytes.AttackerKnowledge
import DY.Bytes.AttackerKnowledgeTheorem
import DY.Misc

namespace DY.Literal

class CanMkLiteral (Bytes: Type u) where
  literalToBytes: ByteArray → Bytes
  bytesToLiteral: Bytes → Option ByteArray

export CanMkLiteral (literalToBytes)
export CanMkLiteral (bytesToLiteral)

-- Constructors

section Constructors

structure Literal (Bytes: Type) where
  lit: ByteArray

instance: ALaCarte.FunctorSizeOf Literal where
  sizeOf | {lit := _} => 0

instance: ALaCarte.Representable Literal where
  CtorId := Unit
  ctors | () => { Data := ByteArray, nRec := 0 }

  toRepr | {lit} => {
    id := ()
    data := lit
    as := #v[]
  }
  fromRepr
  | {id, data := lit, as} =>
    { lit }
  from_to | {lit} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {lit := _} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

instance: ALaCarte.RepresentableDecidableEq Literal where
instance: ALaCarte.RepresentableOrd Literal where
instance: SubBytesFunctor Literal where

abbrev SubF := Literal

def Literal.length [BytesFunctor]: Bytes.PartialLength Literal :=
  fun { lit := lit } _ =>
    lit.size

abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF := Literal.length

abbrev Literal.pack [BytesFunctor] [BytesFunctor.Has SubF] (x: Literal Bytes) := BytesView.pack x

instance [BytesFunctor] [BytesFunctor.Has SubF]: CanMkLiteral Bytes where
  literalToBytes lit :=
    ({ lit }: Literal Bytes).pack

  bytesToLiteral buf :=
    match buf.view? Literal with
    | some { lit } =>
      some lit
    | none => none

theorem bytesToLiteral_literalToBytes
  [BytesFunctor] [BytesFunctor.Has SubF]
  (lit: ByteArray)
  : bytesToLiteral (literalToBytes lit: Bytes) = some lit
  := by
    simp only [bytesToLiteral, literalToBytes]
    grind

theorem literalToBytes_bytesToLiteral
  [BytesFunctor] [BytesFunctor.Has SubF]
  (buf: Bytes)
  :
    match bytesToLiteral buf with
    | none => True
    | some lit =>
      buf = literalToBytes lit
  := by
    simp only [bytesToLiteral, literalToBytes]
    grind

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]

def attKnowsLit: SubAttackerKnowledge Literal where
  pred p out :=
    ∃ lit,
      out = literalToBytes lit

abbrev attackerKnowledge := attKnowsLit

variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

theorem attacker_knows_literalToBytes
  (lit: ByteArray) (tr: Trace α)
  : (literalToBytes lit: Bytes).AttackerKnows tr
  := by
    apply Bytes.AttackerKnows.prove attKnowsLit
    simp only [attKnowsLit]
    exists lit

end AttackerKnowledge

section Invariants

variable [BytesFunctor] [BytesFunctor.Has SubF]

def Literal.invariants: Bytes.PartialInvariants Literal where
  well_formed := fun {lit := _} rec tr =>
    True

  usage := fun {lit := _} rec tr => Usage.nothing

  label := fun {lit := _} rec tr =>
    Label.pub

  invariant := fun {lit := _} rec tr =>
    True

abbrev invariants: Bytes.PartialInvariants SubF := Literal.Literal.invariants

def Literal.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Literal.invariants where

abbrev invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs invariants := Literal.Literal.invariantsProofs

variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
theorem literalToBytes.WellFormed
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).WellFormed tr
  := by
    simp [literalToBytes, Bytes.WellFormed.eq, Literal.invariants]

@[simp]
theorem literalToBytes.label
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).label tr = Label.pub
  := by
    simp [literalToBytes, Bytes.label.eq, Literal.invariants]

@[simp]
theorem literalToBytes.Invariant
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).Invariant tr
  := by
    simp [literalToBytes, Bytes.Invariant.eq, Literal.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

instance: SubAttackerKnowledgeTheorem attKnowsLit where
  pf := by
    simp only [attKnowsLit]
    intro out tr h_tr ⟨lit, h_out⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

example: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstance

end AttackerKnowledgeTheorem

end DY.Literal
