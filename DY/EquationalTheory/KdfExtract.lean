module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.KdfExtract

public
class CanKdfExtract (Bytes: Type u) where
  kdfExtract: (salt: Bytes) → (ikm: Bytes) → Bytes

export CanKdfExtract (kdfExtract)

section Constructors

namespace KdfExtract

public
structure SubF (Bytes: Type) where
  salt: Bytes
  ikm: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {salt, ikm} => sizeOf salt + sizeOf ikm

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {salt, ikm} => {
    id := ()
    data := ()
    as := #v[salt, ikm]
  }
  fromRepr
  | {id, data, as} =>
    let salt := as[0]
    let ikm := as[1]
    { salt, ikm }
  from_to | {salt, ikm} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {salt, ikm} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end KdfExtract

#combine into BytesFunctor, BytesLength from
  KdfExtract,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev KdfExtract.SubF.pack (x: KdfExtract.SubF Bytes) := BytesView.pack x

public
instance: CanKdfExtract Bytes where
  kdfExtract salt ikm := ({salt, ikm}: KdfExtract.SubF Bytes).pack

end Constructors

section AttackerKnowledge

public
def kdfExtract.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ salt ikm,
      out = kdfExtract salt ikm ∧
      DY.Kleene.Forall p [salt, ikm]

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kdfExtract,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_kdfExtract
  (salt ikm: Bytes) (tr: ExecTrace)
  : salt.AttackerKnows tr →
    ikm.AttackerKnows tr →
    (kdfExtract salt ikm).AttackerKnows tr
:= by
  intro h_salt h_ikm
  apply Bytes.AttackerKnows.prove kdfExtract.attackerKnowledge
  simp only [kdfExtract.attackerKnowledge, Kleene.Forall]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def KdfExtract.invariants: Bytes.PartialInvariants KdfExtract.SubF where
  well_formed := fun {salt, ikm} rec tr =>
    (rec salt) tr ∧ (rec ikm) tr

  usage := fun {salt, ikm} rec tr => Usage.nothing

  label := fun {salt, ikm} rec tr =>
    Label.meet ((rec salt) tr) ((rec ikm) tr)

  invariant := fun {salt, ikm} rec tr =>
    (rec salt) tr ∧ (rec ikm) tr

public
theorem KdfExtract.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs KdfExtract.invariants where

end Definition

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  KdfExtract,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

@[simp]
public
theorem kdfExtract.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has KdfExtract.invariants.well_formed]
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).WellFormed tr = (salt.WellFormed tr ∧ ikm.WellFormed tr)
:= by
  simp [kdfExtract, Bytes.WellFormed.eq, KdfExtract.invariants]

@[simp]
public
theorem kdfExtract.label
  [BytesInvariants] [BytesInvariants.Has invariants]
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).label tr = Label.meet (salt.label tr) (ikm.label tr)
:= by
  simp [kdfExtract, Bytes.label.eq, KdfExtract.invariants]

@[simp]
public
theorem kdfExtract.Invariant
  [BytesInvariants] [BytesInvariants.Has invariants]
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).Invariant tr = (salt.Invariant tr ∧ ikm.Invariant tr)
:= by
  simp [kdfExtract, Bytes.Invariant.eq, KdfExtract.invariants]

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesInvariants] [BytesInvariants.Has invariants]

public
instance
  (salt ikm: Bytes)
  : HoareTriplePure
    (kdfExtract salt ikm)
    (fun tr =>
      salt.Invariant tr ∧
      ikm.Invariant tr
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = (salt.label tr).meet (ikm.label tr)
      -- and usage
    )
where
  pf := by
    grind [kdfExtract.Invariant, kdfExtract.label]

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem kdfExtract.attackerKnowledge where
  pf := by
    simp only [kdfExtract.attackerKnowledge]
    intro out tr h_tr ⟨salt, ikm, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kdfExtract,

end AttackerKnowledgeTheorem

end DY.KdfExtract
