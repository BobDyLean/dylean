module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.DiffieHellman

public
class CanDH (Bytes: Type u) where
  -- TODO: naming convention
  dh_pk: (sk: Bytes) → Bytes
  dh: (pk: Bytes) → (sk: Bytes) → Bytes

export CanDH (dh_pk)
export CanDH (dh)

section Constructors

public
structure DhPk (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf DhPk where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable DhPk where
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

public instance: ALaCarte.RepresentableDecidableEq DhPk where
public instance: ALaCarte.RepresentableOrd DhPk where
public instance: SubBytesFunctor DhPk where

public
def DhPk.length [BytesFunctor]: Bytes.PartialLength DhPk :=
  fun _ _ =>
    32

-- workaround for lean4#11708
theorem DhPk.sizeOf_eq
  [BytesFunctor]
  (x: BytesView DhPk)
  : DY.ALaCarte.FunctorSizeOf.sizeOf x = sizeOf x.sk
:= by
  cases x
  simp [DY.ALaCarte.FunctorSizeOf.sizeOf]

grind_pattern DhPk.sizeOf_eq => DY.ALaCarte.FunctorSizeOf.sizeOf x

public
structure Dh (Bytes: Type) where
  pk: Bytes
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf Dh where
  sizeOf | {pk, sk} => sizeOf pk + sizeOf sk

public
instance: ALaCarte.Representable Dh where
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

public instance: ALaCarte.RepresentableDecidableEq Dh where
public instance: ALaCarte.RepresentableOrd Dh where
public instance: SubBytesFunctor Dh where

public
def Dh.length [BytesFunctor]: Bytes.PartialLength Dh :=
  fun _ _ =>
    32

public
abbrev SubF.internal (id: Fin 2): Type → Type :=
  match id with
  | 0 => DhPk
  | 1 => Dh

public
abbrev SubF := BytesFunctor.combine SubF.internal

public
instance: ∀ id, SubBytesFunctor (SubF.internal id)
  | 0 => inferInstanceAs (SubBytesFunctor DhPk)
  | 1 => inferInstanceAs (SubBytesFunctor Dh)

public
instance: SubBytesFunctor SubF := inferInstanceAs (SubBytesFunctor (BytesFunctor.combine SubF.internal))

public instance: BytesFunctor.HasStep DhPk SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 0) SubF)
public instance: BytesFunctor.HasStep Dh SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 1) SubF)

public
def SubF.length.internal [BytesFunctor]: ∀ id, Bytes.PartialLength (SubF.internal id)
  | 0 => DhPk.length
  | 1 => Dh.length

public
abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  Bytes.PartialLength.combine SubF.length.internal

public instance [BytesFunctor] [BytesLength]: BytesLength.HasStep DhPk.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 0) SubF.length)
public instance [BytesFunctor] [BytesLength]: BytesLength.HasStep Dh.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 1) SubF.length)

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev DhPk.pack (x: DhPk Bytes) := BytesView.pack x

public
abbrev Dh.pack (x: Dh Bytes) := BytesView.pack x

public
instance: CanDH Bytes where
  dh_pk sk :=
    ({sk}: DhPk Bytes).pack

  dh pk sk :=
    match pk.view? DhPk with
    | some { sk := sk2 } =>
      if sk ≤ sk2 then
        ({sk := sk, pk := ({sk := sk2}: DhPk Bytes).pack}: Dh Bytes).pack
      else
        ({sk := sk2, pk := ({sk := sk}: DhPk Bytes).pack}: Dh Bytes).pack
    | none =>
      ({sk, pk}: Dh Bytes).pack

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

variable [BytesFunctor] [BytesFunctor.Has SubF]

def attKnowsDhPk: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = dh_pk sk ∧
      p sk

def attKnowsDh: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk sk,
      out = dh pk sk ∧
      Kleene.Forall p [pk, sk]

def attackerKnowledge.internal (id: Fin 2): SubAttackerKnowledge SubF :=
  match id with
  | 0 => attKnowsDhPk
  | 1 => attKnowsDh

public
def attackerKnowledge: SubAttackerKnowledge SubF :=
  SubAttackerKnowledge.combine' attackerKnowledge.internal

instance: AttackerKnowledge.HasStep attKnowsDhPk attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine' attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep attKnowsDh attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine' attackerKnowledge.internal))

variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_dh_pk
  (sk: Bytes) (tr: Trace α)
  : sk.AttackerKnows tr →
    (dh_pk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove attKnowsDhPk
  simp only [attKnowsDhPk]
  grind

public
theorem attacker_knows_dh
  (pk sk: Bytes) (tr: Trace α)
  : pk.AttackerKnows tr →
    sk.AttackerKnows tr →
    (dh pk sk).AttackerKnows tr
:= by
  intro h_pk h_sk
  apply Bytes.AttackerKnows.prove attKnowsDh
  simp only [attKnowsDh, Kleene.Forall]
  grind

end AttackerKnowledge

section Invariants

variable [TraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def DhPk.invariants: Bytes.PartialInvariants DhPk where
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
def Dh.invariants: Bytes.PartialInvariants Dh where
  well_formed := fun {pk, sk} rec tr =>
      (rec pk) tr ∧
      (rec sk) tr

  usage := fun {pk, sk} rec tr =>
    Usage.nothing

  label := fun {pk, sk} rec tr =>
    match _: pk.view? DhPk with
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

public
def invariants.internal: (id: Fin 2) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => DhPk.invariants
  | 1 => Dh.invariants

public
abbrev invariants: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

public instance [BytesInvariants]: BytesInvariants.HasStep DhPk.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
public instance [BytesInvariants]: BytesInvariants.HasStep Dh.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)

def invariantsProofs.internal [BytesInvariants] [BytesInvariants.Has invariants]: (id: Fin 2) → Bytes.PartialInvariantsProofs (invariants.internal id)
  | 0 => DhPk.invariantsProofs
  | 1 => Dh.invariantsProofs

public
def invariantsProofs [BytesInvariants] [BytesInvariants.Has invariants]: Bytes.PartialInvariantsProofs invariants :=
  Bytes.PartialInvariantsProofs.combine invariantsProofs.internal

end Invariants

-- Temporarly close the namespace to define Bytes.dhSkLabel
end DiffieHellman

section ExtractDhSk

variable [TraceTypes]
variable [BytesFunctor]
variable [BytesFunctor.Has DiffieHellman.SubF]

noncomputable
def DiffieHellman.extractDhSk (pk: Bytes): Option Bytes :=
  match pk.view? DiffieHellman.DhPk with
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

end ExtractDhSk

namespace DiffieHellman
section Invariants

variable [TraceTypes]
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
    have h_pk: pk = ({ sk := sk2 }: BytesView DhPk).pack := by grind
    subst h_pk
    split
    · simp [Dh.invariants, DhPk.invariants]
    · simp [Dh.invariants, DhPk.invariants]
      grind
  · simp [Dh.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

instance: SubAttackerKnowledgeTheorem attKnowsDhPk where
  pf := by
    simp only [attKnowsDhPk]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

instance: SubAttackerKnowledgeTheorem attKnowsDh where
  pf := by
    simp only [attKnowsDh]
    intro out tr h_tr ⟨pk, sk, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable, Kleene.Forall]
    grind

instance: ∀ id, SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsDhPk)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsDh)

public
instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' attackerKnowledge.internal))

end AttackerKnowledgeTheorem

end DY.DiffieHellman
