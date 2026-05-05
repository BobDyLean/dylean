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

section Constructors

namespace Hash

public
structure SubF (Bytes: Type) where
  input: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {input} => sizeOf input

public
instance: ALaCarte.Representable SubF where
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

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end Hash

#combine into BytesFunctor, BytesLength from
  Hash,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev Hash.SubF.pack (x: Hash.SubF Bytes) := BytesView.pack x

public
instance: CanHash Bytes where
  hash input := ({input}: Hash.SubF Bytes).pack

public
theorem hash_inj
  (inp1 inp2: Bytes)
  :
    hash inp1 = hash inp2 →
    inp1 = inp2
:= by
  simp only [hash]
  grind

end Constructors

section AttackerKnowledge

public
def hash.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ inp,
      out = hash inp ∧
      p inp

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  hash,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_hash
  (inp: Bytes) (tr: ExecTrace)
  : inp.AttackerKnows tr →
    (hash inp).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove hash.attackerKnowledge
  simp only [hash.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def Hash.invariants: Bytes.PartialInvariants Hash.SubF where
  well_formed := fun {input := input} rec tr =>
    (rec input) tr

  usage := fun {input := input} rec tr => Usage.nothing

  label := fun {input := input} rec tr =>
    (rec input) tr

  invariant := fun {input := input} rec tr =>
    (rec input) tr

public
def Hash.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Hash.invariants where

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  Hash,

variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
public
theorem hash.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).WellFormed tr = inp.WellFormed tr
:= by
  simp [hash, Bytes.WellFormed.eq, Hash.invariants]

@[simp]
public
theorem hash.label
  (inp: Bytes) (tr: ProofTrace)
  : (hash inp).label tr = inp.label tr
:= by
  simp [hash, Bytes.label.eq, Hash.invariants]

@[simp]
public
theorem hash.Invariant
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).Invariant tr =
    inp.Invariant tr
:= by
  simp [hash, Bytes.Invariant.eq, Hash.invariants]

end Invariants

section HoareTriples

public
instance
  [BytesFunctor] [BytesFunctor.Has SubF]
  [ExecTraceTypes] [ProofTraceTypes]
  [BytesInvariants] [BytesInvariants.Has invariants]
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

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem hash.attackerKnowledge where
  pf := by
    simp only [hash.attackerKnowledge]
    intro out tr h_tr ⟨inp, ⟨ h_out, h_inp ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  hash,

end AttackerKnowledgeTheorem

end DY.Hash
