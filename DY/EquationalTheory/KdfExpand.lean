module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.KdfExpand

public
class CanKdfExpand (Bytes: Type u) where
  kdfExpand: (prk: Bytes) → (info: Bytes) → (len: Nat) → Bytes

export CanKdfExpand (kdfExpand)

section Constructors

namespace KdfExpand

public
structure SubF (Bytes: Type) where
  prk: Bytes
  info: Bytes
  len: Nat

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {prk, info, ..} => sizeOf prk + sizeOf info

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Nat, nRec := 2 }

  toRepr | {prk, info, len} => {
    id := ()
    data := len
    as := #v[prk, info]
  }
  fromRepr
  | {id, data, as} =>
    let prk := as[0]
    let info := as[1]
    let len := data
    { prk, info, len }
  from_to | {prk, info, len} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {prk, info, len} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { len, .. } _ =>
    len

end KdfExpand

#combine into BytesFunctor, BytesLength from
  KdfExpand,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev KdfExpand.SubF.pack (x: KdfExpand.SubF Bytes) := BytesView.pack x

public
instance: CanKdfExpand Bytes where
  kdfExpand prk info len := ({prk, info, len}: KdfExpand.SubF Bytes).pack

end Constructors

section AttackerKnowledge

public
def kdfExpand.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ prk info len,
      out = kdfExpand prk info len ∧
      DY.Kleene.Forall p [prk, info]

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kdfExpand,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_kdfExpand
  (prk info: Bytes) (len: Nat) (tr: ExecTrace)
  : prk.AttackerKnows tr →
    info.AttackerKnows tr →
    (kdfExpand prk info len).AttackerKnows tr
:= by
  intro h_prk h_info
  apply Bytes.AttackerKnows.prove kdfExpand.attackerKnowledge
  simp only [kdfExpand.attackerKnowledge, Kleene.Forall]
  grind

end AttackerKnowledge

section Invariants

section Definition
public
class KdfExpandInvariant [ExecTraceTypes] [BytesFunctor] where
  usage (prkUsage: Usage) (info: Bytes): Usage
  label (prkUsage: Usage) (prkLabel: Label) (info: Bytes): Label
  label_sound (prkUsage: Usage) (prkLabel: Label) (info: Bytes)
    : ∀ tr, (label prkUsage prkLabel info).canFlow prkLabel tr
    := by grind

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def KdfExpand.invariants [KdfExpandInvariant] : Bytes.PartialInvariants KdfExpand.SubF where
  well_formed := fun {prk, info, len} rec tr =>
    (rec prk) tr ∧ (rec info) tr

  usage := fun {prk, info, len} rec tr =>
    KdfExpandInvariant.usage ((rec prk) tr) info

  label := fun {prk, info, len} rec tr =>
    KdfExpandInvariant.label (prk.usage tr) ((rec prk) tr) info

  invariant := fun {prk, info, len} rec tr =>
    (rec prk) tr ∧ (rec info) tr

public
theorem KdfExpand.invariantsProofs [BytesInvariants] [KdfExpandInvariant]: Bytes.PartialInvariantsProofs KdfExpand.invariants where

end Definition

#combine [KdfExpandInvariant] into
  BytesInvariants,
  BytesInvariantsProofs
from
  KdfExpand,

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

@[simp]
public
theorem kdfExpand.WellFormed
  [KdfExpandInvariant]
  [BytesWellFormed] [BytesWellFormed.Has KdfExpand.invariants.well_formed]
  (prk info: Bytes) (len: Nat) (tr: ProofTrace)
  : (kdfExpand prk info len).WellFormed tr = (prk.WellFormed tr ∧ info.WellFormed tr)
:= by
  simp [kdfExpand, Bytes.WellFormed.eq, KdfExpand.invariants]

@[simp]
public
theorem kdfExpand.HasUsage
  [KdfExpandInvariant]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (prk info: Bytes) (len: Nat) (prkUsage: Usage) (tr: ProofTrace)
  : prk.HasUsage prkUsage tr →
    (kdfExpand prk info len).HasUsage (KdfExpandInvariant.usage prkUsage info) tr
:= by
  have := KdfExpandInvariant.label_sound (prk.usage tr) (prk.label tr) info tr.erase
  simp [kdfExpand, Bytes.HasUsage, Bytes.usage.eq, KdfExpand.invariants]
  grind [canFlowTrans]

@[simp]
public
theorem kdfExpand.label
  [KdfExpandInvariant]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (prk info: Bytes) (len: Nat) (prkUsage: Usage) (tr: ProofTrace)
  : prk.HasUsage prkUsage tr →
    ((kdfExpand prk info len).label tr).equivalent (KdfExpandInvariant.label prkUsage (prk.label tr) info) tr.erase
:= by
  have := KdfExpandInvariant.label_sound (prk.usage tr) (prk.label tr) info tr.erase
  have := KdfExpandInvariant.label_sound prkUsage (prk.label tr) info tr.erase
  simp [kdfExpand, Bytes.label.eq, KdfExpand.invariants, Bytes.HasUsage]
  grind [canFlowTrans]

@[simp]
public
theorem kdfExpand.Invariant
  [KdfExpandInvariant]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (prk info: Bytes) (len: Nat) (tr: ProofTrace)
  : (kdfExpand prk info len).Invariant tr = (prk.Invariant tr ∧ info.Invariant tr)
:= by
  simp [kdfExpand, Bytes.Invariant.eq, KdfExpand.invariants]

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [KdfExpandInvariant]
variable [BytesInvariants] [BytesInvariants.Has invariants]

public
instance
  (prk info: Bytes) (len: Nat)
  : HasGhostArgumentType (kdfExpand prk info len) Usage
where
  dummy := ()

public
instance
  (prk info: Bytes) (len: Nat) (prkUsage: Usage)
  : HoareTriplePureGhost
    (kdfExpand prk info len)
    (prkUsage)
    (fun tr =>
      prk.Invariant tr ∧
      prk.HasUsage prkUsage tr ∧
      info.Publishable tr
    )
    (fun res tr =>
      res.Invariant tr ∧
      (res.label tr).equivalent (KdfExpandInvariant.label prkUsage (prk.label tr) info) tr.erase ∧
      res.HasUsage (KdfExpandInvariant.usage prkUsage info) tr
    )
where
  pf := by
    grind [kdfExpand.Invariant, kdfExpand.label, kdfExpand.HasUsage]

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [KdfExpandInvariant]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem kdfExpand.attackerKnowledge where
  pf := by
    simp only [kdfExpand.attackerKnowledge]
    intro out tr h_tr ⟨prk, info, len, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have: prk.HasUsage (prk.usage tr) tr := by simp [Bytes.HasUsage]
    have := KdfExpandInvariant.label_sound (prk.usage tr) (prk.label tr) info tr.erase
    have := kdfExpand.label prk info len (prk.usage tr) tr
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [KdfExpandInvariant] [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kdfExpand,

end AttackerKnowledgeTheorem

end DY.KdfExpand
