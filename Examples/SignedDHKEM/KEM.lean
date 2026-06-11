module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation
public import DY.Actions.ProtocolEvent
public import DY.Actions.Network
public import DY.Meta

namespace DY.KEM

public
class CanKem (Bytes: Type u) where
  kemPk: (sk: Bytes) → Bytes
  kemEncap: (pk: Bytes) → (entropy: Bytes) → Bytes × Bytes
  kemDecap: (sk: Bytes) → (cipher: Bytes) → Err Bytes

export CanKem (kemPk)
export CanKem (kemEncap)
export CanKem (kemDecap)

section Constructors

namespace Pk

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
    800 -- ML-KEM-512

end Pk

namespace Encap

public
structure SubF (Bytes: Type) where
  pk: Bytes
  entropy: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {pk, entropy} => sizeOf pk + sizeOf entropy

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {pk, entropy} => {
    id := ()
    data := ()
    as := #v[pk, entropy]
  }
  fromRepr
  | {id, data, as} =>
    let pk := as[0]
    let entropy := as[1]
    { pk, entropy }
  from_to | {pk, entropy} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pk, entropy} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    768 -- ML-KEM-512

end Encap

namespace SharedSecret

public
structure SubF (Bytes: Type) where
  entropy: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {entropy} => sizeOf entropy

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {entropy} => {
    id := ()
    data := ()
    as := #v[entropy]
  }
  fromRepr
  | {id, data, as} =>
    let entropy := as[0]
    { entropy }
  from_to | {entropy} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {entropy} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32 -- ML-KEM-512

end SharedSecret

#combine into BytesFunctor, BytesLength from
  Pk,
  Encap,
  SharedSecret,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Pk.SubF.pack (x: Pk.SubF Bytes) := BytesView.pack x
public abbrev Encap.SubF.pack (x: Encap.SubF Bytes) := BytesView.pack x
public abbrev SharedSecret.SubF.pack (x: SharedSecret.SubF Bytes) := BytesView.pack x

public
instance: CanKem Bytes where
  kemPk sk :=
    ({sk}: Pk.SubF Bytes).pack

  kemEncap pk entropy :=
    (({pk, entropy}: Encap.SubF Bytes).pack, ({ entropy }: SharedSecret.SubF Bytes).pack)

  kemDecap sk cipher :=
    match cipher.view? Encap.SubF with
    | some { pk, entropy } =>
      match pk.view? Pk.SubF with
      | some { sk := sk' } =>
        if sk = sk' then
          some ({ entropy }: SharedSecret.SubF Bytes).pack
        else
          none
      | none => none
    | none => none

public
theorem kemDecap_kemEncap
  (sk entropy: Bytes)
  : let (cipher, ss) := kemEncap (kemPk sk) entropy
    kemDecap sk cipher = some ss
:= by
  simp only [kemPk, kemEncap, kemDecap]
  grind

-- not exposed to the attacker through attacker knowledge,
-- but through a Traceful function
public
def kemPkInvert (pk: Bytes): Err Bytes :=
  match pk.view? Pk.SubF with
  | some { sk } => some sk
  | none => none

public
theorem kemPkInvert_kemPk
  (sk: Bytes)
  : kemPkInvert (kemPk sk) = some sk
:= by
  simp only [kemPk, kemPkInvert]
  grind

public
theorem kemPk_kemPkInvert
  (pk: Bytes)
  : match kemPkInvert pk with
    | none => True
    | some sk => kemPk sk = pk
:= by
  simp only [kemPk, kemPkInvert]
  grind

end Constructors

section AttackerKnowledge

public
def kemPk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = kemPk sk ∧
      p sk

public
def kemEncapCipher.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk entropy rhs,
      (out, rhs) = kemEncap pk entropy ∧
      Kleene.Forall p [pk, entropy]

public
def kemEncapSS.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk entropy lhs,
      (lhs, out) = kemEncap pk entropy ∧
      Kleene.Forall p [pk, entropy]

public
def kemDecap.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk cipher,
      some out = kemDecap sk cipher ∧
      Kleene.Forall p [sk, cipher]

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem kemPk.attacker_knows
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (kemPk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove kemPk.attackerKnowledge
  simp only [kemPk.attackerKnowledge]
  grind

public
theorem kemEncap.attacker_knows
  (pk entropy: Bytes) (tr: ExecTrace)
  : pk.AttackerKnows tr →
    entropy.AttackerKnows tr →
    (kemEncap pk entropy).fst.AttackerKnows tr ∧
    (kemEncap pk entropy).snd.AttackerKnows tr
:= by
  intro h_pk h_entropy
  apply And.intro
  · apply Bytes.AttackerKnows.prove kemEncapCipher.attackerKnowledge
    simp only [kemEncapCipher.attackerKnowledge, Kleene.Forall]
    grind
  · apply Bytes.AttackerKnows.prove kemEncapSS.attackerKnowledge
    simp only [kemEncapSS.attackerKnowledge, Kleene.Forall]
    grind

public
theorem kemDecap.attacker_knows
  (sk cipher: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    cipher.AttackerKnows tr →
    match kemDecap sk cipher with
    | none => True
    | some ss => ss.AttackerKnows tr
:= by
  intro h_sk h_cipher
  split
  · grind
  apply Bytes.AttackerKnows.prove kemDecap.attackerKnowledge
  simp only [kemDecap.attackerKnowledge, Kleene.Forall]
  grind

end AttackerKnowledge

namespace Broken

variable [BytesFunctor]

public
structure BrokenKemEvent where
  brokenPk: Bytes

#combine into ExecEntryT, baseAttackerKnowledge from ProtocolEvent BrokenKemEvent

variable [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]

public
def ThisKemPkHasBeenBroken (brokenPk: Bytes) (tr: ExecTrace): Prop :=
  tr.EventLogged ({brokenPk}: BrokenKemEvent)

theorem ThisKemPkHasBeenBroken_later
  (brokenPk: Bytes) (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ThisKemPkHasBeenBroken brokenPk tr1 →
    ThisKemPkHasBeenBroken brokenPk tr2
:= by
  simp only [ThisKemPkHasBeenBroken]
  grind

grind_pattern ThisKemPkHasBeenBroken_later => tr1 ≤ tr2, ThisKemPkHasBeenBroken brokenPk tr1

public
def OneKemPkHasBeenBroken (tr: ExecTrace): Prop :=
  ∃ brokenPk, ThisKemPkHasBeenBroken brokenPk tr

theorem OneKemPkHasBeenBroken_later
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    OneKemPkHasBeenBroken tr1 →
    OneKemPkHasBeenBroken tr2
:= by
  simp only [OneKemPkHasBeenBroken]
  grind

grind_pattern OneKemPkHasBeenBroken_later => tr1 ≤ tr2, OneKemPkHasBeenBroken tr1

@[expose]
public
def label (brokenPk: Bytes): Label where
  isCorrupt tr := ThisKemPkHasBeenBroken brokenPk tr

variable [BytesFunctor.Has KEM.SubF]
variable [ExecTraceTypes.Has Network.ExecEntryT]

public
def breakKemPk (msgHandle: Nat): Traceful Nat := do
  let pk ← Network.receiveMessage msgHandle
  ProtocolEvent.logEvent ({brokenPk := pk}: BrokenKemEvent)
  let sk ← kemPkInvert pk
  let handle ← Network.sendMessage sk
  return handle

@[expose]
public
def breakKemPk.reachability: ReachabilityConfig := .make (fun handle => breakKemPk handle)

end Broken

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has KEM.SubF]
variable [ExecTraceTypes.Has Broken.ExecEntryT]

public
def Pk.invariants: Bytes.PartialInvariants Pk.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := sk} rec tr =>
    Usage.nothing

  label := fun {sk := sk} rec tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (sk.label tr).canFlow (Broken.label (kemPk sk)) tr.erase ∧
    (rec sk) tr

public
def Pk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Pk.invariants where

section PkLemmas

variable [BytesInvariants] [BytesInvariants.Has Pk.invariants]

@[simp]
public
theorem kemPk.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  : (kemPk inp).WellFormed tr = inp.WellFormed tr
:= by
  simp [kemPk, Bytes.WellFormed.eq, Pk.invariants]

@[simp]
public
theorem kemPk.label
  (inp: Bytes) (tr: ProofTrace)
  : (kemPk inp).label tr = Label.pub
:= by
  simp [kemPk, Bytes.label.eq, Pk.invariants]

@[simp]
public
theorem kemPk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    (sk.label tr).canFlow (Broken.label (kemPk sk)) tr.erase →
    (kemPk sk).Invariant tr
:= by
  simp [kemPk, Bytes.Invariant.eq, Pk.invariants]
  grind

end PkLemmas

end Invariants

-- Temporarly close the namespace to define Bytes.SignkeyHasUsage and Bytes.signkeyLabel
end KEM

section ExtractKemPk

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]
variable [BytesFunctor.Has KEM.SubF]
variable [ExecTraceTypes.Has KEM.Broken.ExecEntryT]

noncomputable
def KEM.extractKemSk (pk: Bytes): Option Bytes :=
  match pk.view? KEM.Pk.SubF with
  | some { sk } =>
    some sk
  | none => none

theorem KEM.kemPk_extractKemSk (b: Bytes):
  match extractKemSk b with
  | none => True
  | some sk => b = KEM.kemPk sk
:= by
  simp [extractKemSk, KEM.kemPk]
  grind

theorem KEM.extractKemSk.preserves_WellFormed
  [BytesInvariants] [BytesInvariants.Has KEM.Pk.invariants]
: ExtractPreservesWellFormed KEM.extractKemSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [KEM.kemPk_extractKemSk, KEM.kemPk.WellFormed]

public
def Bytes.KemSkHasUsage
  [BytesInvariants]
  (pk: Bytes) (skUsg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage KEM.extractKemSk pk skUsg tr

public
theorem Bytes.KemSkHasUsage_kemPk
  [BytesInvariants]
  (sk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : (KEM.kemPk sk).KemSkHasUsage skUsg tr = sk.HasUsage skUsg tr
:= by
  simp [Bytes.KemSkHasUsage, Bytes.XXXHasUsage, KEM.extractKemSk, KEM.kemPk]
  grind

grind_pattern Bytes.KemSkHasUsage_kemPk => (KEM.kemPk sk).KemSkHasUsage skUsg tr

public
theorem Bytes.KemSkHasUsage_later
  [BytesInvariants]
  [BytesInvariants.Has KEM.Pk.invariants]
  [GetUsageLater] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.KemSkHasUsage usg tr1 →
    b.KemSkHasUsage usg tr2
:= by
  simp [Bytes.KemSkHasUsage]
  apply Bytes.XXXHasUsage_later KEM.extractKemSk KEM.extractKemSk.preserves_WellFormed

grind_pattern Bytes.KemSkHasUsage_later => tr1 ≤ tr2, b.KemSkHasUsage usg tr1

public
theorem Bytes.KemSkHasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has KEM.Pk.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.KemSkHasUsage usg tr1 →
    b.KemSkHasUsage usg tr2
:= by grind

grind_pattern [grind_later] Bytes.KemSkHasUsage_later_fast => tr1 ≤ tr2, b.KemSkHasUsage usg tr1

public
noncomputable
def Bytes.kemSkLabel
  [GetLabel]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel KEM.extractKemSk pk tr

public
theorem Bytes.kemSkLabel_kemPk
  [BytesInvariants]
  [BytesInvariants.Has KEM.Pk.invariants]
  (sk: Bytes) (tr: ProofTrace)
  : (KEM.kemPk sk).kemSkLabel tr = sk.label tr
:= by
  simp [Bytes.kemSkLabel, Bytes.xxxLabel, KEM.extractKemSk, KEM.kemPk]
  grind

grind_pattern Bytes.kemSkLabel_kemPk => (KEM.kemPk sk).kemSkLabel tr

public
theorem Bytes.kemSkLabel_later
  [BytesInvariants]
  [BytesInvariants.Has KEM.Pk.invariants]
  [GetLabelLater]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by
  simp [Bytes.kemSkLabel]
  apply Bytes.xxxLabel_later KEM.extractKemSk KEM.extractKemSk.preserves_WellFormed

grind_pattern Bytes.kemSkLabel_later => tr1 ≤ tr2, b.kemSkLabel tr1

public
theorem Bytes.kemSkLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has KEM.Pk.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by grind

grind_pattern [grind_later] Bytes.kemSkLabel_later_fast => tr1 ≤ tr2, b.kemSkLabel tr1

end ExtractKemPk

namespace KEM

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has KEM.SubF]

public
def Encap.invariants: Bytes.PartialInvariants Encap.SubF where
  well_formed := fun {pk, entropy} rec tr =>
      (rec pk) tr ∧
      (rec entropy) tr

  usage := fun {pk, entropy} rec tr =>
    Usage.nothing

  label := fun {pk, entropy} rec tr =>
    Label.pub

  invariant := fun {pk, entropy} rec tr =>
      (rec pk) tr ∧
      (rec entropy) tr ∧
      (
        (entropy.label tr).canFlow (pk.kemSkLabel tr) tr.erase ∧
        True -- TODO usage
        -- (
        --   pk `has_kem_sk_usage tr` KemKey usg /\
        --   (get_label tr nonce) `can_flow tr` (get_kem_sk_label tr pk)
        -- ) \/ (
        --   (get_label tr nonce) `can_flow tr` public
        -- )
      )

public
def Encap.invariantsProofs [BytesInvariants] [ExecTraceTypes.Has Broken.ExecEntryT] [BytesInvariants.Has Pk.invariants]: Bytes.PartialInvariantsProofs Encap.invariants where

public
def SharedSecret.invariants: Bytes.PartialInvariants SharedSecret.SubF where
  well_formed := fun {entropy := entropy} rec tr =>
    (rec entropy) tr

  usage := fun {entropy := entropy} rec tr =>
    Usage.nothing -- TODO

  label := fun {entropy := entropy} rec tr =>
    (rec entropy) tr

  invariant := fun {entropy := entropy} rec tr =>
    (rec entropy) tr

public
def SharedSecret.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs SharedSecret.invariants where

#combine [BytesFunctor.Has SubF] [ExecTraceTypes.Has Broken.ExecEntryT] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has Pk.invariants]
from
  Pk,
  Encap,
  SharedSecret,

section EncapLemmas

variable [ExecTraceTypes.Has Broken.ExecEntryT]
variable [BytesInvariants] [BytesInvariants.Has KEM.invariants]

public
theorem kemEncap.WellFormed
  (pk entropy: Bytes) (tr: ProofTrace)
  : let (cipher, ss) := kemEncap pk entropy
    cipher.WellFormed tr = (pk.WellFormed tr ∧ entropy.WellFormed tr) ∧
    ss.WellFormed tr = entropy.WellFormed tr
:= by
  simp [kemEncap, Bytes.WellFormed.eq, Encap.invariants, SharedSecret.invariants]

public
theorem kemEncap.ss_label
  (pk entropy: Bytes) (tr: ProofTrace)
  : let (_, ss) := kemEncap pk entropy
    ss.label tr = entropy.label tr
:= by
  simp [kemEncap, SharedSecret.invariants]

end EncapLemmas

section DecapLemmas

variable [ExecTraceTypes.Has Broken.ExecEntryT]
variable [BytesInvariants] [BytesInvariants.Has KEM.invariants]

public
theorem kemDecap.WellFormed
  (sk cipher: Bytes) (tr: ProofTrace)
  : match kemDecap sk cipher with
    | none => True
    | some ss => (sk.WellFormed tr ∧ ss.WellFormed tr) = cipher.WellFormed tr
:= by
  split
  · grind
  rename_i ss heq
  simp only [kemDecap] at heq
  split at heq
  · rename_i pk entropy _
    split at heq
    · rename_i sk' _
      split at heq
      · have := Bytes.pack_view? Encap.SubF cipher
        have := Bytes.pack_view? Pk.SubF pk
        simp_all only
        subst_eqs
        simp_all [Bytes.WellFormed.eq, Pk.invariants, Encap.invariants, SharedSecret.invariants]
      · grind
    · grind
  · grind

end DecapLemmas

end Invariants

section HoareTriples

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has KEM.SubF]
variable [ExecTraceTypes.Has Broken.ExecEntryT]
variable [BytesInvariants] [BytesInvariants.Has KEM.invariants]

public
instance kemPk_hoareTriple
  (sk: Bytes)
  : HoareTriplePure
    (kemPk sk)
    (fun tr =>
      sk.Invariant tr ∧
      (sk.label tr).canFlow (Broken.label (kemPk sk)) tr.erase
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
where
  pf := by
    grind [kemPk.Invariant, kemPk.label]

public
instance kemEncap_hoareTriple
  (pk entropy: Bytes)
  : HoareTriplePure
    (kemEncap pk entropy)
    (fun tr =>
      pk.Invariant tr ∧
      entropy.Invariant tr ∧
      (entropy.label tr).canFlow (pk.kemSkLabel tr) tr.erase
      -- nonce `has_usage tr` KemNonce usg /\
      -- (
      --   (
      --     pk `has_kem_sk_usage tr` KemKey usg /\
      --     (get_label tr nonce) `can_flow tr` (get_kem_sk_label tr pk)
      --   ) \/ (
      --     (get_label tr nonce) `can_flow tr` public
      --   )
      -- )
    )
    (fun (cipher, ss) tr =>
      cipher.Publishable tr ∧
      ss.Invariant tr ∧
      ss.label tr = entropy.label tr
      -- TODO usage
    )
where
  pf := by
    simp [kemEncap, Bytes.Publishable, Bytes.Invariant.eq, Encap.invariants, SharedSecret.invariants]
    grind

public
instance kemDecap_hoareTriple
  [TraceInvariant]
  (sk cipher: Bytes)
  : HoareTriple
    (kemDecap sk cipher)
    (fun tr =>
      sk.Invariant tr ∧
      cipher.Invariant tr
      -- sk usage
    )
    (fun ss tr =>
      kemDecap sk cipher = some ss ∧
      ss.Invariant tr ∧
      (ss.label tr).canFlow (sk.label tr) tr.erase
      -- TODO usage
    )
where
  pf := by
    simp only [hoareTriple, wp, OptionT.run, kemDecap]
    intro tr h_pre h_inv
    split
    · grind
    rename_i ss heq
    split at heq
    · rename_i pk entropy _
      split at heq
      · rename_i sk' _
        split at heq
        · have := Bytes.pack_view? Encap.SubF cipher
          have := Bytes.pack_view? Pk.SubF pk
          have := Bytes.kemSkLabel_kemPk sk tr
          simp only [kemPk] at this
          simp_all only
          subst_eqs
          simp_all [Pk.invariants, Encap.invariants, SharedSecret.invariants]
        · grind
      · grind
    · grind

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has KEM.SubF]
variable [ExecTraceTypes.Has Broken.ExecEntryT]
variable [BytesInvariants.Has KEM.invariants]

-- Preserve publishability

public
instance: SubAttackerKnowledgeTheorem kemPk.attackerKnowledge where
  pf := by
    simp only [kemPk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind [kemPk.Invariant, canFlowTrans]

public
instance: SubAttackerKnowledgeTheorem kemEncapCipher.attackerKnowledge where
  pf := by
    simp only [kemEncapCipher.attackerKnowledge]
    intro out tr h_tr ⟨pk, entropy, rhs, ⟨ h_out, h_inputs ⟩⟩
    simp_all [kemEncap, Kleene.Forall, Bytes.Publishable, Bytes.Publishable, Bytes.Invariant.eq, Encap.invariants]
    grind [canFlowTrans]

public
instance: SubAttackerKnowledgeTheorem kemEncapSS.attackerKnowledge where
  pf := by
    simp only [kemEncapSS.attackerKnowledge]
    intro out tr h_tr ⟨pk, entropy, lhs, ⟨ h_out, h_inputs ⟩⟩
    simp_all [kemEncap, Kleene.Forall, Bytes.Publishable, Bytes.Publishable, Bytes.Invariant.eq, SharedSecret.invariants]

public
instance: SubAttackerKnowledgeTheorem kemDecap.attackerKnowledge where
  pf := by
    simp only [kemDecap.attackerKnowledge]
    intro out tr h_tr ⟨sk, cipher, ⟨ h_out, h_inputs ⟩⟩
    have := (kemDecap_hoareTriple sk cipher).pf
    simp only [hoareTriple, wp, OptionT.run, ← h_out] at this
    simp [Kleene.Forall] at h_inputs
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [ExecTraceTypes.Has Broken.ExecEntryT] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,

end AttackerKnowledgeTheorem

namespace Broken

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
variable [BytesFunctor.Has KEM.SubF]
variable [ExecTraceTypes.Has Broken.ExecEntryT]
variable [BytesInvariants.Has KEM.invariants]

@[instance]
theorem kemPkInvert.spec (pk: Bytes)
  : HoareTriple
    (kemPkInvert pk)
    (fun tr => tr.erase.EventLogged ({brokenPk := pk}: Broken.BrokenKemEvent) ∧ pk.Publishable tr)
    (fun sk tr => sk.Publishable tr)
:= by
  apply HoareTriple.mk
  dsimp only [hoareTriple, wp, OptionT.run]
  intro tr h_pk h_tr
  split
  · grind
  rename_i sk _
  have: pk = kemPk sk := by grind [kemPk_kemPkInvert pk]
  have h: (kemPk sk).Publishable tr := by grind
  simp only [kemPk, Bytes.Publishable] at h
  simp only [Bytes.Invariant.eq, KEM.Pk.invariants] at h
  simp only [Label.canFlow, Broken.label, Broken.ThisKemPkHasBeenBroken] at h
  simp only [Bytes.Publishable]
  grind

public
instance: ProtocolEvent.EventInv (BrokenKemEvent) where
  invariant _ _ := True

#combine into
  ProofEntryT,
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from ProtocolEvent Broken.BrokenKemEvent

variable [BytesInvariantsProofs]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ProofTraceTypes.Has Broken.ProofEntryT] [ProofTraceTypes.Has Network.ProofEntryT]
variable [TraceInvariant.Has Network.ProofEntryT]
variable [TraceInvariant.Has Broken.ProofEntryT]

@[instance]
theorem breakKemPk.spec (msgHandle: Nat)
  : HoareTriple
    (breakKemPk msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold breakKemPk
  step
  step by simp [ProtocolEvent.EventInv.invariant]
  step
  step
  step
  grind

public instance: ReachableImpliesInvariant breakKemPk.reachability := .mk (fun (msgHandle) => breakKemPk.spec msgHandle)

end Broken

end DY.KEM
