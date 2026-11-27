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

namespace Literal

public
structure BytesPart.Functor (Bytes: Type) where
  lit: ByteArray

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {lit := _} => 0

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where

public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun { lit := lit } _ =>
    lit.size


end Literal

#combine into Bytes, Bytes.length from
  Literal,

public
abbrev Literal.BytesPart.Functor.pack [Bytes.Def] [Bytes has% Literal] (x: Literal.BytesPart.Functor Bytes) := BytesView.pack x

public
instance [Bytes.Def] [Bytes has% DY.Literal]: CanMkLiteral Bytes where
  literalToBytes lit :=
    ({ lit }: Literal.BytesPart.Functor Bytes).pack

  bytesToLiteral buf :=
    match buf.view? Literal.BytesPart.Functor with
    | some { lit } =>
      some lit
    | none => none

public
theorem bytesToLiteral_literalToBytes
  [Bytes.Def] [Bytes has% DY.Literal]
  (lit: ByteArray)
  : bytesToLiteral (literalToBytes lit: Bytes) = some lit
:= by
  simp only [bytesToLiteral, literalToBytes]
  grind

public
theorem literalToBytes_bytesToLiteral
  [Bytes.Def] [Bytes has% DY.Literal]
  (buf: Bytes)
  : match bytesToLiteral buf with
    | none => True
    | some lit =>
      buf = literalToBytes lit
:= by
  simp only [bytesToLiteral, literalToBytes]
  grind

@[simp]
public
theorem length_literalToBytes
  [Bytes.Def] [Bytes.length.Def]
  [Bytes has% DY.Literal] [Bytes.length has% DY.Literal]
  (buf: ByteArray)
  : Bytes.length (literalToBytes buf) = buf.size
:= by
  simp only [literalToBytes]
  grind [Literal.BytesPart.length]

end Constructors

section AttackerKnowledge

public
def literalToBytes.attackerKnows [Bytes.Def] [Bytes has% DY.Literal]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ lit,
      out = literalToBytes lit

#combine [Bytes has% DY.Literal] into Bytes.AttackerKnows.merge from
  literalToBytes,

variable [Bytes.Def] [Bytes has% DY.Literal]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows has% DY.Literal]

public
theorem attacker_knows_literalToBytes
  (lit: ByteArray) (tr: ExecTrace)
  : (literalToBytes lit: Bytes).AttackerKnows tr
:= by
  apply Bytes.AttackerKnows.prove literalToBytes.attackerKnows
  simp only [literalToBytes.attackerKnows]
  exists lit

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]

public
def Literal.BytesPart.invariants: Bytes.Invariants.Part Literal.BytesPart.Functor where
  well_formed := fun {lit := _} _rec _tr =>
    True

  usage := fun {lit := _} _rec _tr => Usage.nothing

  label := fun {lit := _} _rec _tr =>
    Label.pub

  invariant := fun {lit := _} _rec _tr =>
    True

public
theorem Literal.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful Literal.BytesPart.invariants where

end Definition

#combine into
  Bytes.Invariants,
  Bytes.Invariants.Lawful
from
  Literal,

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes has% DY.Literal]

@[simp]
public
theorem literalToBytes.WellFormed
  [Bytes.WellFormed.Def] [Bytes.WellFormed has% Literal]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).WellFormed tr
:= by
  simp [literalToBytes, Bytes.WellFormed.eq, Literal.BytesPart.invariants]

@[simp]
public
theorem literalToBytes.label
  [Bytes.Invariants.Def] [Bytes.Invariants has% DY.Literal]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).label tr = Label.pub
:= by
  simp [literalToBytes, Bytes.label.eq, Literal.BytesPart.invariants]

@[simp]
public
theorem literalToBytes.Invariant
  [Bytes.Invariants.Def] [Bytes.Invariants has% DY.Literal]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).Invariant tr
:= by
  simp [literalToBytes, Bytes.Invariant.eq, Literal.BytesPart.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes has% DY.Literal]
variable [Bytes.Invariants has% DY.Literal]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part literalToBytes.attackerKnows where
  pf := by
    simp only [literalToBytes.attackerKnows]
    intro out tr h_tr ⟨lit, h_out⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [Bytes has% DY.Literal] [Bytes.Invariants has% DY.Literal] into Bytes.AttackerKnows_implies_Publishable.merge from
  literalToBytes,

end AttackerKnowledgeTheorem

end DY.Literal
