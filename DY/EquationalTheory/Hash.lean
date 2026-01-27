import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.Invariants
import DY.Bytes.AttackerKnowledge
import DY.Bytes.AttackerKnowledgeTheorem
import DY.Misc

namespace DY.Hash

class CanHash (Bytes: Type u) where
  hash: Bytes → Bytes

export CanHash (hash)

-- Constructors

section Constructors

structure Hash (Bytes: Type) where
  input: Bytes

instance: ALaCarte.FunctorSizeOf Hash where
  sizeOf | {input} => sizeOf input

instance: ALaCarte.Representable Hash where
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

instance: ALaCarte.RepresentableDecidableEq Hash where
instance: ALaCarte.RepresentableOrd Hash where
instance: SubBytesFunctor Hash where

variable [BytesFunctor] [BytesFunctor.Has Hash]

abbrev Hash.pack (x: Hash Bytes) := BytesView.pack x

instance: CanHash Bytes where
  hash input := ({input}: Hash Bytes).pack

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

variable [BytesFunctor] [BytesFunctor.Has Hash]

def attKnowsHash: SubAttackerKnowledge Hash where
  pred p out :=
    ∃ inp,
      out = hash inp ∧
      p inp

abbrev Hash.attackerKnowledge := attKnowsHash

theorem attacker_knows_hash
  [AttackerKnowledge]
  [AttackerKnowledge.Has Hash.attackerKnowledge]
  (inp: Bytes) (tr: Trace α)
  :
    inp.AttackerKnows tr →
    (hash inp).AttackerKnows tr
  := by
    intro h_inp
    apply Bytes.AttackerKnows.prove attKnowsHash
    simp only [attKnowsHash]
    grind

end AttackerKnowledge

section Invariants

variable [BytesFunctor] [BytesFunctor.Has Hash]

def Hash.invariants: Bytes.PartialInvariants Hash where
  well_formed := fun {input := input} rec tr =>
    (rec input) tr

  usage := fun {input := input} rec tr => Usage.nothing

  label := fun {input := input} rec tr =>
    (rec input) tr

  invariant := fun {input := input} rec tr =>
    (rec input) tr

variable [BytesInvariants] [BytesInvariants.Has Hash.invariants]

@[simp]
theorem hash.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).WellFormed tr = inp.WellFormed tr
  := by
    simp [hash, Bytes.WellFormed.eq, Hash.invariants]

@[simp]
theorem hash.label
  (inp: Bytes) (tr: ProofTrace)
  : (hash inp).label tr = inp.label tr
  := by
    simp [hash, Bytes.label.eq, Hash.invariants]

@[simp]
theorem hash.Invariant
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).Invariant tr =
    inp.Invariant tr
  := by
    simp [hash, Bytes.Invariant.eq, Hash.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has Hash]
variable [BytesInvariants.Has Hash.invariants]

instance: SubAttackerKnowledgeTheorem attKnowsHash where
  pf := by
    simp only [attKnowsHash]
    intro out tr h_tr ⟨inp, ⟨ h_out, h_inp ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

example: SubAttackerKnowledgeTheorem Hash.attackerKnowledge := inferInstance

end AttackerKnowledgeTheorem

end DY.Hash
