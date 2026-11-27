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
structure BytesPart.Functor (Bytes: Type) where
  prk: Bytes
  info: Bytes
  len: Nat

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {prk, info, ..} => sizeOf prk + sizeOf info

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun { len, .. } _ =>
    len

end KdfExpand

#combine into Bytes, Bytes.length from
  KdfExpand,

public
abbrev KdfExpand.BytesPart.Functor.pack [Bytes.Def] [Bytes has% KdfExpand] (x: KdfExpand.BytesPart.Functor Bytes) := BytesView.pack x

variable [Bytes.Def] [Bytes has% DY.KdfExpand]

public
instance: CanKdfExpand Bytes where
  kdfExpand prk info len := ({prk, info, len}: KdfExpand.BytesPart.Functor Bytes).pack

end Constructors

section AttackerKnowledge

public
def kdfExpand.attackerKnows [Bytes.Def] [Bytes has% DY.KdfExpand]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ prk info len,
      out = kdfExpand prk info len ∧
      p prk ∧
      p info

#combine [Bytes has% DY.KdfExpand] into Bytes.AttackerKnows.merge from
  kdfExpand,

variable [Bytes.Def] [Bytes has% DY.KdfExpand]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows has% DY.KdfExpand]

public
theorem attacker_knows_kdfExpand
  (prk info: Bytes) (len: Nat) (tr: ExecTrace)
  : prk.AttackerKnows tr →
    info.AttackerKnows tr →
    (kdfExpand prk info len).AttackerKnows tr
:= by
  intro h_prk h_info
  apply Bytes.AttackerKnows.prove kdfExpand.attackerKnows
  simp only [kdfExpand.attackerKnows]
  grind

end AttackerKnowledge

section Invariants

section Definition
public
class KdfExpandInvariant [ExecTrace.Def] [Bytes.Def] where
  usage (prkUsage: Usage) (info: Bytes): Usage
  label (prkUsage: Usage) (prkLabel: Label) (info: Bytes): Label
  label_sound (prkUsage: Usage) (prkLabel: Label) (info: Bytes)
    : ∀ tr, (label prkUsage prkLabel info).canFlow prkLabel tr
    := by grind

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]

public
def KdfExpand.BytesPart.invariants [KdfExpandInvariant] : Bytes.Invariants.Part KdfExpand.BytesPart.Functor where
  well_formed := fun {prk, info, len} rec tr =>
    (rec prk) tr ∧ (rec info) tr

  usage := fun {prk, info, len} rec tr =>
    KdfExpandInvariant.usage ((rec prk) tr) info

  label := fun {prk, info, len} rec tr =>
    KdfExpandInvariant.label (prk.usage tr) ((rec prk) tr) info

  invariant := fun {prk, info, len} rec tr =>
    (rec prk) tr ∧ (rec info) tr

public
theorem KdfExpand.BytesPart.invariantsLawful [Bytes.Invariants.Def] [KdfExpandInvariant]: Bytes.Invariants.Part.Lawful KdfExpand.BytesPart.invariants where

end Definition

#combine [KdfExpandInvariant] into
  Bytes.Invariants,
  Bytes.Invariants.Lawful
from
  KdfExpand,

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes has% DY.KdfExpand]

@[simp]
public
theorem kdfExpand.WellFormed
  [KdfExpandInvariant]
  [Bytes.WellFormed.Def] [Bytes.WellFormed has% KdfExpand]
  (prk info: Bytes) (len: Nat) (tr: ProofTrace)
  : (kdfExpand prk info len).WellFormed tr = (prk.WellFormed tr ∧ info.WellFormed tr)
:= by
  simp [kdfExpand, Bytes.WellFormed.eq, KdfExpand.BytesPart.invariants]

@[simp]
public
theorem kdfExpand.HasUsage
  [KdfExpandInvariant]
  [Bytes.Invariants.Def] [Bytes.Invariants has% DY.KdfExpand]
  (prk info: Bytes) (len: Nat) (prkUsage: Usage) (tr: ProofTrace)
  : prk.HasUsage prkUsage tr →
    (kdfExpand prk info len).HasUsage (KdfExpandInvariant.usage prkUsage info) tr
:= by
  have := KdfExpandInvariant.label_sound (prk.usage tr) (prk.label tr) info tr.erase
  simp [kdfExpand, Bytes.HasUsage, Bytes.usage.eq, KdfExpand.BytesPart.invariants]
  grind [canFlowTrans]

@[simp]
public
theorem kdfExpand.label
  [KdfExpandInvariant]
  [Bytes.Invariants.Def] [Bytes.Invariants has% DY.KdfExpand]
  (prk info: Bytes) (len: Nat) (prkUsage: Usage) (tr: ProofTrace)
  : prk.HasUsage prkUsage tr →
    ((kdfExpand prk info len).label tr).equivalent (KdfExpandInvariant.label prkUsage (prk.label tr) info) tr.erase
:= by
  have := KdfExpandInvariant.label_sound (prk.usage tr) (prk.label tr) info tr.erase
  have := KdfExpandInvariant.label_sound prkUsage (prk.label tr) info tr.erase
  simp [kdfExpand, Bytes.label.eq, KdfExpand.BytesPart.invariants, Bytes.HasUsage]
  grind [canFlowTrans]

@[simp]
public
theorem kdfExpand.Invariant
  [KdfExpandInvariant]
  [Bytes.Invariants.Def] [Bytes.Invariants has% DY.KdfExpand]
  (prk info: Bytes) (len: Nat) (tr: ProofTrace)
  : (kdfExpand prk info len).Invariant tr = (prk.Invariant tr ∧ info.Invariant tr)
:= by
  simp [kdfExpand, Bytes.Invariant.eq, KdfExpand.BytesPart.invariants]

end Invariants

section HoareTriples

variable [Bytes.Def] [Bytes has% DY.KdfExpand]
variable [ExecTrace.Def] [ProofTrace.Def]
variable [KdfExpandInvariant]
variable [Bytes.Invariants.Def] [Bytes.Invariants has% DY.KdfExpand]

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

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes has% DY.KdfExpand]
variable [KdfExpandInvariant]
variable [Bytes.Invariants has% DY.KdfExpand]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part kdfExpand.attackerKnows where
  pf := by
    simp only [kdfExpand.attackerKnows]
    intro out tr h_tr ⟨prk, info, len, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    have: prk.HasUsage (prk.usage tr) tr := by simp [Bytes.HasUsage]
    have := KdfExpandInvariant.label_sound (prk.usage tr) (prk.label tr) info tr.erase
    have := kdfExpand.label prk info len (prk.usage tr) tr
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [KdfExpandInvariant] [Bytes has% DY.KdfExpand] [Bytes.Invariants has% DY.KdfExpand] into Bytes.AttackerKnows_implies_Publishable.merge from
  kdfExpand,

end AttackerKnowledgeTheorem

end DY.KdfExpand
