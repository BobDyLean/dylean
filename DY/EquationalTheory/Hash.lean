module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation -- HoareTriplePure

namespace DY.Hash

public
class CanHash (Bytes: Type u) where
  hash: (msg: Bytes) → Bytes

export CanHash (hash)

public
def hashLength := 32

@[simp]
public
theorem hashLength_neq_0
  : hashLength ≠ 0
:= by
  simp [hashLength]

section Constructors

namespace Hash

public
structure BytesPart.Functor (Bytes: Type) where
  input: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {input} => sizeOf input

public
instance: ALaCarte.Representable BytesPart.Functor where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {input} => {
    id := ()
    data := ()
    as := #v[input]
  }
  fromRepr
  | {id, data, as} =>
    let input := as[0]
    { input }
  from_to | {input} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {input} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    hashLength

end Hash

#combine into Bytes, Bytes.length from
  Hash,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

public
abbrev Hash.BytesPart.Functor.pack (x: Hash.BytesPart.Functor Bytes) := BytesView.pack x

public
instance: CanHash Bytes where
  hash input := ({input}: Hash.BytesPart.Functor Bytes).pack

public
theorem hash_inj
  (inp1 inp2: Bytes)
  :
    hash inp1 = hash inp2 →
    inp1 = inp2
:= by
  simp only [hash]
  grind

@[simp]
public
theorem length_hash
  [Bytes.length.Def] [Bytes.length.Has BytesPart.length]
  (inp: Bytes)
  : Bytes.length (hash inp) = hashLength
:= by
  simp only [hash]
  grind [Hash.BytesPart.length]

end Constructors

section AttackerKnowledge

public
def hash.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ inp,
      out = hash inp ∧
      p inp

#combine [Bytes.Has BytesPart.Functor] into Bytes.AttackerKnows.merge from
  hash,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows.Has attackerKnows]

public
theorem attacker_knows_hash
  (inp: Bytes) (tr: ExecTrace)
  : inp.AttackerKnows tr →
    (hash inp).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove hash.attackerKnows
  simp only [hash.attackerKnows]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]

public
def Hash.BytesPart.invariants: Bytes.Invariants.Part Hash.BytesPart.Functor where
  well_formed := fun {input := input} rec tr =>
    (rec input) tr

  usage := fun {input := input} rec tr => Usage.nothing

  label := fun {input := input} rec tr =>
    (rec input) tr

  invariant := fun {input := input} rec tr =>
    (rec input) tr

public
theorem Hash.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful Hash.BytesPart.invariants where

end Definition

#combine into
  Bytes.Invariants,
  Bytes.Invariants.Lawful
from
  Hash,

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]

@[simp]
public
theorem hash.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).WellFormed tr = inp.WellFormed tr
:= by
  simp [hash, Bytes.WellFormed.eq, Hash.BytesPart.invariants]

@[simp]
public
theorem hash.label
  (inp: Bytes) (tr: ProofTrace)
  : (hash inp).label tr = inp.label tr
:= by
  simp [hash, Bytes.label.eq, Hash.BytesPart.invariants]

@[simp]
public
theorem hash.Invariant
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).Invariant tr =
    inp.Invariant tr
:= by
  simp [hash, Bytes.Invariant.eq, Hash.BytesPart.invariants]

end Invariants

section HoareTriples

public
instance
  [Bytes.Def] [Bytes.Has BytesPart.Functor]
  [ExecTrace.Def] [ProofTrace.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (b: Bytes)
  : HoareTriplePure
    (hash b)
    (fun tr => b.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = b.label tr
    )
where
  pf := by
    simp

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes.Has BytesPart.Functor]
variable [Bytes.Invariants.Has BytesPart.invariants]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part hash.attackerKnows where
  pf := by
    simp only [hash.attackerKnows]
    intro out tr h_tr ⟨inp, ⟨ h_out, h_inp ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [Bytes.Has BytesPart.Functor] [Bytes.Invariants.Has BytesPart.invariants] into Bytes.AttackerKnows_implies_Publishable.merge from
  hash,

end AttackerKnowledgeTheorem

end DY.Hash
