module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.Literal

public
class CanMkLiteral (Bytes: Type u) where
  literalToBytes: ByteArray → Bytes
  bytesToLiteral: Bytes → Option ByteArray

export CanMkLiteral (literalToBytes)
export CanMkLiteral (bytesToLiteral)

-- Constructors

section Constructors

public
structure Literal (Bytes: Type) where
  lit: ByteArray

public
instance: ALaCarte.FunctorSizeOf Literal where
  sizeOf | {lit := _} => 0

public
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

public instance: ALaCarte.RepresentableDecidableEq Literal where
public instance: ALaCarte.RepresentableOrd Literal where

public instance: SubBytesFunctor Literal where

public
abbrev SubF := Literal

public
def Literal.length [BytesFunctor]: Bytes.PartialLength Literal :=
  fun { lit := lit } _ =>
    lit.size

public
abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF := Literal.length

public
abbrev Literal.pack [BytesFunctor] [BytesFunctor.Has SubF] (x: Literal Bytes) := BytesView.pack x

public
instance [BytesFunctor] [BytesFunctor.Has SubF]: CanMkLiteral Bytes where
  literalToBytes lit :=
    ({ lit }: Literal Bytes).pack

  bytesToLiteral buf :=
    match buf.view? Literal with
    | some { lit } =>
      some lit
    | none => none

public
theorem bytesToLiteral_literalToBytes
  [BytesFunctor] [BytesFunctor.Has SubF]
  (lit: ByteArray)
  : bytesToLiteral (literalToBytes lit: Bytes) = some lit
:= by
  simp only [bytesToLiteral, literalToBytes]
  grind

public
theorem literalToBytes_bytesToLiteral
  [BytesFunctor] [BytesFunctor.Has SubF]
  (buf: Bytes)
  : match bytesToLiteral buf with
    | none => True
    | some lit =>
      buf = literalToBytes lit
:= by
  simp only [bytesToLiteral, literalToBytes]
  grind

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def attKnowsLit: SubAttackerKnowledge Literal where
  pred p out :=
    ∃ lit,
      out = literalToBytes lit

public
abbrev attackerKnowledge := attKnowsLit

variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_literalToBytes
  (lit: ByteArray) (tr: Trace α)
  : (literalToBytes lit: Bytes).AttackerKnows tr
:= by
  apply Bytes.AttackerKnows.prove attKnowsLit
  simp only [attKnowsLit]
  exists lit

end AttackerKnowledge

section Invariants

variable [TraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def Literal.invariants: Bytes.PartialInvariants Literal where
  well_formed := fun {lit := _} _rec _tr =>
    True

  usage := fun {lit := _} _rec _tr => Usage.nothing

  label := fun {lit := _} _rec _tr =>
    Label.pub

  invariant := fun {lit := _} _rec _tr =>
    True

public
abbrev invariants: Bytes.PartialInvariants SubF := Literal.Literal.invariants

public
def Literal.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Literal.invariants where

public
abbrev invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs invariants := Literal.Literal.invariantsProofs

variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
public
theorem literalToBytes.WellFormed
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).WellFormed tr
:= by
  simp [literalToBytes, Bytes.WellFormed.eq, Literal.invariants]

@[simp]
public
theorem literalToBytes.label
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).label tr = Label.pub
:= by
  simp [literalToBytes, Bytes.label.eq, Literal.invariants]

@[simp]
public
theorem literalToBytes.Invariant
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).Invariant tr
:= by
  simp [literalToBytes, Bytes.Invariant.eq, Literal.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

public
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
