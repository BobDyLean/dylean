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
structure BytesPart.Functor (Bytes: Type) where
  salt: Bytes
  ikm: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {salt, ikm} => sizeOf salt + sizeOf ikm

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    32

end KdfExtract

#combine into Bytes, Bytes.length from
  KdfExtract,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

public
abbrev KdfExtract.BytesPart.Functor.pack (x: KdfExtract.BytesPart.Functor Bytes) := BytesView.pack x

public
instance: CanKdfExtract Bytes where
  kdfExtract salt ikm := ({salt, ikm}: KdfExtract.BytesPart.Functor Bytes).pack

end Constructors

section AttackerKnowledge

public
def kdfExtract.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ salt ikm,
      out = kdfExtract salt ikm ∧
      p salt ∧
      p ikm

#combine [Bytes.Has BytesPart.Functor] into Bytes.AttackerKnows.merge from
  kdfExtract,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows.Has attackerKnows]

public
theorem attacker_knows_kdfExtract
  (salt ikm: Bytes) (tr: ExecTrace)
  : salt.AttackerKnows tr →
    ikm.AttackerKnows tr →
    (kdfExtract salt ikm).AttackerKnows tr
:= by
  intro h_salt h_ikm
  apply Bytes.AttackerKnows.prove kdfExtract.attackerKnows
  simp only [kdfExtract.attackerKnows]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]

public
def KdfExtract.BytesPart.invariants: Bytes.Invariants.Part KdfExtract.BytesPart.Functor where
  well_formed := fun {salt, ikm} rec tr =>
    (rec salt) tr ∧ (rec ikm) tr

  usage := fun {salt, ikm} rec tr => Usage.nothing

  label := fun {salt, ikm} rec tr =>
    Label.meet ((rec salt) tr) ((rec ikm) tr)

  invariant := fun {salt, ikm} rec tr =>
    (rec salt) tr ∧ (rec ikm) tr

public
theorem KdfExtract.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful KdfExtract.BytesPart.invariants where

end Definition

#combine into
  Bytes.Invariants,
  Bytes.Invariants.Lawful
from
  KdfExtract,

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

@[simp]
public
theorem kdfExtract.WellFormed
  [Bytes.WellFormed.Def] [Bytes.WellFormed.Has KdfExtract.BytesPart.invariants.well_formed]
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).WellFormed tr = (salt.WellFormed tr ∧ ikm.WellFormed tr)
:= by
  simp [kdfExtract, Bytes.WellFormed.eq, KdfExtract.BytesPart.invariants]

@[simp]
public
theorem kdfExtract.label
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).label tr = Label.meet (salt.label tr) (ikm.label tr)
:= by
  simp [kdfExtract, Bytes.label.eq, KdfExtract.BytesPart.invariants]

@[simp]
public
theorem kdfExtract.Invariant
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).Invariant tr = (salt.Invariant tr ∧ ikm.Invariant tr)
:= by
  simp [kdfExtract, Bytes.Invariant.eq, KdfExtract.BytesPart.invariants]

end Invariants

section HoareTriples

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]

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

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes.Has BytesPart.Functor]
variable [Bytes.Invariants.Has BytesPart.invariants]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part kdfExtract.attackerKnows where
  pf := by
    simp only [kdfExtract.attackerKnows]
    intro out tr h_tr ⟨salt, ikm, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [Bytes.Has BytesPart.Functor] [Bytes.Invariants.Has BytesPart.invariants] into Bytes.AttackerKnows_implies_Publishable.merge from
  kdfExtract,

end AttackerKnowledgeTheorem

end DY.KdfExtract
