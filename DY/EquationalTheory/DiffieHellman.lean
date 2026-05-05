module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation -- HoareTriplePure

namespace DY.DiffieHellman

public
class CanDH (Bytes: Type u) where
  -- TODO: naming convention
  dh_pk: (sk: Bytes) → Bytes
  dh: (pk: Bytes) → (sk: Bytes) → Bytes

export CanDH (dh_pk)
export CanDH (dh)

section Constructors

namespace DhPk

public
structure SubF (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {sk} => {
    id := ()
    data := ()
    as := #v[sk]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    { sk }
  from_to | {sk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

-- workaround for lean4#11708
theorem SubF.sizeOf_eq
  [BytesFunctor]
  (x: BytesView SubF)
  : DY.ALaCarte.FunctorSizeOf.sizeOf x = sizeOf x.sk
:= by
  cases x
  simp [DY.ALaCarte.FunctorSizeOf.sizeOf]

grind_pattern SubF.sizeOf_eq => DY.ALaCarte.FunctorSizeOf.sizeOf x

end DhPk

namespace Dh

public
structure SubF (Bytes: Type) where
  pk: Bytes
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {pk, sk} => sizeOf pk + sizeOf sk

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {pk, sk} => {
    id := ()
    data := ()
    as := #v[pk, sk]
  }
  fromRepr
  | {id, data, as} =>
    let pk := as[0]
    let sk := as[1]
    { pk, sk }
  from_to | {pk, sk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pk, sk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end Dh

#combine into BytesFunctor, BytesLength from
  DhPk,
  Dh,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev DhPk.SubF.pack (x: DhPk.SubF Bytes) := BytesView.pack x

public
abbrev Dh.SubF.pack (x: Dh.SubF Bytes) := BytesView.pack x

public
instance: CanDH Bytes where
  dh_pk sk :=
    ({sk}: DhPk.SubF Bytes).pack

  dh pk sk :=
    match pk.view? DhPk.SubF with
    | some { sk := sk2 } =>
      if sk ≤ sk2 then
        ({sk := sk, pk := ({sk := sk2}: DhPk.SubF Bytes).pack}: Dh.SubF Bytes).pack
      else
        ({sk := sk2, pk := ({sk := sk}: DhPk.SubF Bytes).pack}: Dh.SubF Bytes).pack
    | none =>
      ({sk, pk}: Dh.SubF Bytes).pack

public
theorem dh_commutes
  (sk1 sk2: Bytes)
  : dh (dh_pk sk1) sk2 = dh (dh_pk sk2) sk1
:= by
  simp only [dh_pk, dh, BytesView.view_pack]
  grind

grind_pattern dh_commutes => dh (dh_pk sk1) sk2, dh (dh_pk sk2) sk1

end Constructors

section AttackerKnowledge

public
def dh_pk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = dh_pk sk ∧
      p sk

public
def dh.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk sk,
      out = dh pk sk ∧
      Kleene.Forall p [pk, sk]

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  dh_pk,
  dh,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_dh_pk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (dh_pk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove dh_pk.attackerKnowledge
  simp only [dh_pk.attackerKnowledge]
  grind

public
theorem attacker_knows_dh
  (pk sk: Bytes) (tr: ExecTrace)
  : pk.AttackerKnows tr →
    sk.AttackerKnows tr →
    (dh pk sk).AttackerKnows tr
:= by
  intro h_pk h_sk
  apply Bytes.AttackerKnows.prove dh.attackerKnowledge
  simp only [dh.attackerKnowledge, Kleene.Forall]
  grind

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has DiffieHellman.SubF]

public
def DhPk.invariants: Bytes.PartialInvariants DhPk.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := sk} rec tr =>
    Usage.nothing

  label := fun {sk := sk} rec tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
def DhPk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs DhPk.invariants where

section DhPkLemmas

variable [BytesInvariants] [BytesInvariants.Has DhPk.invariants]

@[simp]
public
theorem dh_pk.WellFormed
  (sk: Bytes) (tr: ProofTrace)
  :
    (dh_pk sk).WellFormed tr = sk.WellFormed tr
:= by
  simp [dh_pk, Bytes.WellFormed.eq, DhPk.invariants]

@[simp]
public
theorem dh_pk.label
  (sk: Bytes) (tr: ProofTrace)
  : (dh_pk sk).label tr = Label.pub
:= by
  simp [dh_pk, Bytes.label.eq, DhPk.invariants]

@[simp]
public
theorem dh_pk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  :
    sk.Invariant tr →
    (dh_pk sk).Invariant tr
:= by
  simp [dh_pk, Bytes.Invariant.eq, DhPk.invariants]

end DhPkLemmas

public
def Dh.invariants: Bytes.PartialInvariants Dh.SubF where
  well_formed := fun {pk, sk} rec tr =>
      (rec pk) tr ∧
      (rec sk) tr

  usage := fun {pk, sk} rec tr =>
    Usage.nothing

  label := fun {pk, sk} rec tr =>
    match _: pk.view? DhPk.SubF with
    | none => Label.pub
    | some {sk := sk2} =>
      Label.join ((rec sk) tr) ((rec sk2) tr)

  invariant := fun {pk, sk} rec tr =>
      (rec pk) tr ∧
      (rec sk) tr

public
def Dh.invariantsProofs [BytesInvariants] [BytesInvariants.Has DhPk.invariants]: Bytes.PartialInvariantsProofs Dh.invariants where
  label_later := by
    intro _ x rec tr1 tr2
    cases x
    simp_all [DhPk.invariants, invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetLabelLaterT] <;> grind

#combine [BytesFunctor.Has SubF] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has DhPk.invariants]
from
  DhPk,
  Dh,

end Invariants

-- Temporarly close the namespace to define Bytes.dhSkLabel
end DiffieHellman

section ExtractDhSk

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]
variable [BytesFunctor.Has DiffieHellman.SubF]

noncomputable
def DiffieHellman.extractDhSk (pk: Bytes): Option Bytes :=
  match pk.view? DiffieHellman.DhPk.SubF with
  | some { sk } =>
    some sk
  | none => none

theorem DiffieHellman.dh_pk_extractDhSk (b: Bytes):
  match extractDhSk b with
  | none => True
  | some sk => b = DiffieHellman.dh_pk sk
:= by
  simp [extractDhSk, DiffieHellman.dh_pk]
  grind

theorem DiffieHellman.extractDhSk.preserves_WellFormed
  [BytesInvariants] [BytesInvariants.Has DiffieHellman.invariants]
: ExtractPreservesWellFormed extractDhSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [DiffieHellman.dh_pk_extractDhSk, DiffieHellman.dh_pk.WellFormed]

public
noncomputable
def Bytes.dhSkLabel
  [BytesInvariants]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel DiffieHellman.extractDhSk pk tr

public
theorem Bytes.dhSkLabel_dh_pk
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman.invariants]
  (sk: Bytes) (tr: ProofTrace)
  : (DiffieHellman.dh_pk sk).dhSkLabel tr = sk.label tr
:= by
  simp [Bytes.dhSkLabel, Bytes.xxxLabel, DiffieHellman.extractDhSk, DiffieHellman.dh_pk]
  grind

grind_pattern Bytes.dhSkLabel_dh_pk => (DiffieHellman.dh_pk sk).dhSkLabel tr

public
theorem Bytes.dhSkLabel_later
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman.invariants]
  [GetLabelLater]
  (b: Bytes) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.dhSkLabel tr1 = b.dhSkLabel tr2
:= by
  simp [Bytes.dhSkLabel]
  apply Bytes.xxxLabel_later DiffieHellman.extractDhSk DiffieHellman.extractDhSk.preserves_WellFormed

grind_pattern Bytes.dhSkLabel_later => tr1 ≤ tr2, b.dhSkLabel tr1

public
theorem Bytes.dhSkLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DiffieHellman.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  :
    b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.dhSkLabel tr1 = b.dhSkLabel tr2
:= by grind

grind_pattern [grind_later] Bytes.dhSkLabel_later_fast => tr1 ≤ tr2, b.dhSkLabel tr1

end ExtractDhSk

namespace DiffieHellman
section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
public
theorem dh.WellFormed
  (pk sk: Bytes) (tr: ProofTrace)
  : (dh pk sk).WellFormed tr = (pk.WellFormed tr ∧ sk.WellFormed tr)
:= by
  simp only [dh]
  split
  · rename_i sk2 heq
    have: pk = dh_pk sk2 := by simp_all [dh_pk]; grind [dh_pk]
    split
    all_goals
      simp [Dh.invariants, DhPk.invariants]
      grind [dh_pk.WellFormed]
  · simp [Dh.invariants]

@[simp]
public
theorem dh.label
  (pk sk: Bytes) (tr: ProofTrace)
  : (dh pk sk).label tr = Label.join (pk.dhSkLabel tr) (sk.label tr)
:= by
  simp only [dh]
  split
  · split
    all_goals
      simp only [Bytes.label.eq, Dh.invariants, Bytes.dhSkLabel, Bytes.xxxLabel, extractDhSk]
      grind
  · simp only [Bytes.label.eq, Dh.invariants, Bytes.dhSkLabel, Bytes.xxxLabel, extractDhSk]
    grind

@[simp]
public
theorem dh.Invariant
  (pk sk: Bytes) (tr: ProofTrace)
  : (
      pk.Invariant tr ∧
      sk.Invariant tr
    ) → (
      (dh pk sk).Invariant tr
    )
:= by
  simp only [dh]
  split
  · rename_i sk2 heq
    have h_pk: pk = ({ sk := sk2 }: BytesView DhPk.SubF).pack := by grind
    subst h_pk
    split
    · simp [Dh.invariants, DhPk.invariants]
    · simp [Dh.invariants, DhPk.invariants]
      grind
  · simp [Dh.invariants]

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesInvariants] [BytesInvariants.Has invariants]

public
instance
  (sk: Bytes)
  : HoareTriplePure
    (dh_pk sk)
    (fun tr => sk.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
  where
    pf := by
      grind [dh_pk.Invariant, dh_pk.label]

public
instance
  (pk sk: Bytes)
  : HoareTriplePure
    (dh pk sk)
    (fun tr =>
      sk.Invariant tr ∧
      pk.Publishable tr
      -- and usage
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.join (sk.label tr) (pk.dhSkLabel tr)
      -- and usage
    )
  where
    pf := by
      grind [dh.Invariant, dh.label]

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem dh_pk.attackerKnowledge where
  pf := by
    simp only [dh_pk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

public
instance: SubAttackerKnowledgeTheorem dh.attackerKnowledge where
  pf := by
    simp only [dh.attackerKnowledge]
    intro out tr h_tr ⟨pk, sk, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable, Kleene.Forall]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  dh_pk,
  dh

end AttackerKnowledgeTheorem

end DY.DiffieHellman
