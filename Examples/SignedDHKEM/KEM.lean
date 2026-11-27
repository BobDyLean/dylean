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
structure BytesPart.Functor (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    800 -- ML-KEM-512

end Pk

namespace Encap

public
structure BytesPart.Functor (Bytes: Type) where
  pk: Bytes
  entropy: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {pk, entropy} => sizeOf pk + sizeOf entropy

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    768 -- ML-KEM-512

end Encap

namespace SharedSecret

public
structure BytesPart.Functor (Bytes: Type) where
  entropy: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {entropy} => sizeOf entropy

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    32 -- ML-KEM-512

end SharedSecret

#combine into Bytes, Bytes.length from
  Pk,
  Encap,
  SharedSecret,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

public abbrev Pk.BytesPart.Functor.pack (x: Pk.BytesPart.Functor Bytes) := BytesView.pack x
public abbrev Encap.BytesPart.Functor.pack (x: Encap.BytesPart.Functor Bytes) := BytesView.pack x
public abbrev SharedSecret.BytesPart.Functor.pack (x: SharedSecret.BytesPart.Functor Bytes) := BytesView.pack x

public
instance: CanKem Bytes where
  kemPk sk :=
    ({sk}: Pk.BytesPart.Functor Bytes).pack

  kemEncap pk entropy :=
    (({pk, entropy}: Encap.BytesPart.Functor Bytes).pack, ({ entropy }: SharedSecret.BytesPart.Functor Bytes).pack)

  kemDecap sk cipher :=
    match cipher.view? Encap.BytesPart.Functor with
    | some { pk, entropy } =>
      match pk.view? Pk.BytesPart.Functor with
      | some { sk := sk' } =>
        if sk = sk' then
          some ({ entropy }: SharedSecret.BytesPart.Functor Bytes).pack
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
  match pk.view? Pk.BytesPart.Functor with
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
def kemPk.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ sk,
      out = kemPk sk ∧
      p sk

public
def kemEncapCipher.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ pk entropy rhs,
      (out, rhs) = kemEncap pk entropy ∧
      p pk ∧
      p entropy

public
def kemEncapSS.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ pk entropy lhs,
      (lhs, out) = kemEncap pk entropy ∧
      p pk ∧
      p entropy

public
def kemDecap.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ sk cipher,
      some out = kemDecap sk cipher ∧
      p sk ∧
      p cipher

#combine [Bytes.Has BytesPart.Functor] into Bytes.AttackerKnows.merge from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows.Has attackerKnows]

public
theorem kemPk.attacker_knows
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (kemPk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove kemPk.attackerKnows
  simp only [kemPk.attackerKnows]
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
  · apply Bytes.AttackerKnows.prove kemEncapCipher.attackerKnows
    simp only [kemEncapCipher.attackerKnows]
    grind
  · apply Bytes.AttackerKnows.prove kemEncapSS.attackerKnows
    simp only [kemEncapSS.attackerKnows]
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
  apply Bytes.AttackerKnows.prove kemDecap.attackerKnows
  simp only [kemDecap.attackerKnows]
  grind

end AttackerKnowledge

namespace Broken

variable [Bytes.Def]

public
structure BrokenKemEvent where
  brokenPk: Bytes

#combine into ExecTrace, Trace.BaseAttackerKnows from ProtocolEvent BrokenKemEvent

variable [ExecTrace.Def] [ExecTrace.Has TracePart.Exec]

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

variable [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Network.TracePart.Exec]

public
def breakKemPk (msgHandle: Nat): Traceful Nat := do
  let pk ← Network.receiveMessage msgHandle
  ProtocolEvent.logEvent ({brokenPk := pk}: BrokenKemEvent)
  let sk ← kemPkInvert pk
  let handle ← Network.sendMessage sk
  return handle

@[expose]
public
def breakKemPk.transitionSystem: TransitionSystem := .make (fun handle => breakKemPk handle)

end Broken

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]

public
def Pk.BytesPart.invariants: Bytes.Invariants.Part Pk.BytesPart.Functor where
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
theorem Pk.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful Pk.BytesPart.invariants where

end Definition

section PkLemmas

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has Pk.BytesPart.invariants]

@[simp]
public
theorem kemPk.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  : (kemPk inp).WellFormed tr = inp.WellFormed tr
:= by
  simp [kemPk, Bytes.WellFormed.eq, Pk.BytesPart.invariants]

@[simp]
public
theorem kemPk.label
  (inp: Bytes) (tr: ProofTrace)
  : (kemPk inp).label tr = Label.pub
:= by
  simp [kemPk, Bytes.label.eq, Pk.BytesPart.invariants]

@[simp]
public
theorem kemPk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    (sk.label tr).canFlow (Broken.label (kemPk sk)) tr.erase →
    (kemPk sk).Invariant tr
:= by
  simp [kemPk, Bytes.Invariant.eq, Pk.BytesPart.invariants]
  grind

end PkLemmas

end Invariants

-- Temporarly close the namespace to define Bytes.SignkeyHasUsage and Bytes.signkeyLabel
end KEM

section ExtractKemPk

variable [Bytes.Def] [Bytes.Has KEM.BytesPart.Functor]

noncomputable
def KEM.extractKemSk (pk: Bytes): Option Bytes :=
  match pk.view? KEM.Pk.BytesPart.Functor with
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

variable [ExecTrace.Def] [ProofTrace.Def]

theorem KEM.extractKemSk.preserves_WellFormed
  [ExecTrace.Has KEM.Broken.TracePart.Exec]
  [Bytes.Invariants.Def] [Bytes.Invariants.Has KEM.Pk.BytesPart.invariants]
: ExtractPreservesWellFormed KEM.extractKemSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [KEM.kemPk_extractKemSk, KEM.kemPk.WellFormed]

public
def Bytes.KemSkHasUsage
  [Bytes.Invariants.Def]
  (pk: Bytes) (skUsg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage KEM.extractKemSk pk skUsg tr

public
theorem Bytes.KemSkHasUsage_kemPk
  [Bytes.Invariants.Def]
  (sk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : (KEM.kemPk sk).KemSkHasUsage skUsg tr = sk.HasUsage skUsg tr
:= by
  simp [Bytes.KemSkHasUsage, Bytes.XXXHasUsage, KEM.extractKemSk, KEM.kemPk]
  grind

grind_pattern Bytes.KemSkHasUsage_kemPk => (KEM.kemPk sk).KemSkHasUsage skUsg tr

public
theorem Bytes.KemSkHasUsage_later
  [Bytes.Invariants.Def]
  [ExecTrace.Has KEM.Broken.TracePart.Exec]
  [Bytes.Invariants.Has KEM.Pk.BytesPart.invariants]
  [Bytes.usage_later.Proof] [Bytes.label_later.Proof]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [ExecTrace.Has KEM.Broken.TracePart.Exec]
  [Bytes.Invariants.Has KEM.Pk.BytesPart.invariants]
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
  [Bytes.label.Def]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel KEM.extractKemSk pk tr

public
theorem Bytes.kemSkLabel_kemPk
  [Bytes.Invariants.Def]
  [ExecTrace.Has KEM.Broken.TracePart.Exec]
  [Bytes.Invariants.Has KEM.Pk.BytesPart.invariants]
  (sk: Bytes) (tr: ProofTrace)
  : (KEM.kemPk sk).kemSkLabel tr = sk.label tr
:= by
  simp [Bytes.kemSkLabel, Bytes.xxxLabel, KEM.extractKemSk, KEM.kemPk]
  grind

grind_pattern Bytes.kemSkLabel_kemPk => (KEM.kemPk sk).kemSkLabel tr

public
theorem Bytes.kemSkLabel_later
  [Bytes.Invariants.Def]
  [ExecTrace.Has KEM.Broken.TracePart.Exec]
  [Bytes.Invariants.Has KEM.Pk.BytesPart.invariants]
  [Bytes.label_later.Proof]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [ExecTrace.Has KEM.Broken.TracePart.Exec]
  [Bytes.Invariants.Has KEM.Pk.BytesPart.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by grind

grind_pattern [grind_later] Bytes.kemSkLabel_later_fast => tr1 ≤ tr2, b.kemSkLabel tr1

end ExtractKemPk

namespace KEM

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]

public
def Encap.BytesPart.invariants [Bytes.Has KEM.BytesPart.Functor]: Bytes.Invariants.Part Encap.BytesPart.Functor where
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
theorem Encap.BytesPart.invariantsLawful [Bytes.Invariants.Def] [Bytes.Has KEM.BytesPart.Functor] [ExecTrace.Has Broken.TracePart.Exec] [Bytes.Invariants.Has Pk.BytesPart.invariants]: Bytes.Invariants.Part.Lawful Encap.BytesPart.invariants where

public
def SharedSecret.BytesPart.invariants: Bytes.Invariants.Part SharedSecret.BytesPart.Functor where
  well_formed := fun {entropy := entropy} rec tr =>
    (rec entropy) tr

  usage := fun {entropy := entropy} rec tr =>
    Usage.nothing -- TODO

  label := fun {entropy := entropy} rec tr =>
    (rec entropy) tr

  invariant := fun {entropy := entropy} rec tr =>
    (rec entropy) tr

public
theorem SharedSecret.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful SharedSecret.BytesPart.invariants where

end Definition

#combine [Bytes.Has BytesPart.Functor] [ExecTrace.Has Broken.TracePart.Exec] into
  Bytes.Invariants,
  Bytes.Invariants.Lawful [Bytes.Invariants.Has Pk.BytesPart.invariants]
from
  Pk,
  Encap,
  SharedSecret,

section EncapLemmas

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has KEM.BytesPart.invariants]

public
theorem kemEncap.WellFormed
  (pk entropy: Bytes) (tr: ProofTrace)
  : let (cipher, ss) := kemEncap pk entropy
    cipher.WellFormed tr = (pk.WellFormed tr ∧ entropy.WellFormed tr) ∧
    ss.WellFormed tr = entropy.WellFormed tr
:= by
  simp [kemEncap, Bytes.WellFormed.eq, Encap.BytesPart.invariants, SharedSecret.BytesPart.invariants]

public
theorem kemEncap.ss_label
  (pk entropy: Bytes) (tr: ProofTrace)
  : let (_, ss) := kemEncap pk entropy
    ss.label tr = entropy.label tr
:= by
  simp [kemEncap, SharedSecret.BytesPart.invariants]

end EncapLemmas

section DecapLemmas

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has KEM.BytesPart.invariants]

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
      · have := Bytes.pack_view? Encap.BytesPart.Functor cipher
        have := Bytes.pack_view? Pk.BytesPart.Functor pk
        simp_all only
        subst_eqs
        simp_all [Bytes.WellFormed.eq, Pk.BytesPart.invariants, Encap.BytesPart.invariants, SharedSecret.BytesPart.invariants]
      · grind
    · grind
  · grind

end DecapLemmas

end Invariants

section HoareTriples

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has KEM.BytesPart.invariants]

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
    simp [kemEncap, Bytes.Publishable, Bytes.Invariant.eq, Encap.BytesPart.invariants, SharedSecret.BytesPart.invariants]
    grind

public
instance kemDecap_hoareTriple
  [Trace.Invariant.Def]
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
        · have := Bytes.pack_view? Encap.BytesPart.Functor cipher
          have := Bytes.pack_view? Pk.BytesPart.Functor pk
          have := Bytes.kemSkLabel_kemPk sk tr
          simp only [kemPk] at this
          simp_all only
          subst_eqs
          simp_all [Pk.BytesPart.invariants, Encap.BytesPart.invariants, SharedSecret.BytesPart.invariants]
        · grind
      · grind
    · grind

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Has KEM.BytesPart.invariants]

-- Preserve publishability

public
instance: Bytes.AttackerKnows_implies_Publishable.Part kemPk.attackerKnows where
  pf := by
    simp only [kemPk.attackerKnows]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind [kemPk.Invariant, canFlowTrans]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part kemEncapCipher.attackerKnows where
  pf := by
    simp only [kemEncapCipher.attackerKnows]
    intro out tr h_tr ⟨pk, entropy, rhs, ⟨ h_out, h_inputs ⟩⟩
    simp_all [kemEncap, Bytes.Publishable, Bytes.Publishable, Bytes.Invariant.eq, Encap.BytesPart.invariants]
    grind [canFlowTrans]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part kemEncapSS.attackerKnows where
  pf := by
    simp only [kemEncapSS.attackerKnows]
    intro out tr h_tr ⟨pk, entropy, lhs, ⟨ h_out, h_inputs ⟩⟩
    simp_all [kemEncap, Bytes.Publishable, Bytes.Publishable, Bytes.Invariant.eq, SharedSecret.BytesPart.invariants]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part kemDecap.attackerKnows where
  pf := by
    simp only [kemDecap.attackerKnows]
    intro out tr h_tr ⟨sk, cipher, ⟨ h_out, h_inputs ⟩⟩
    have := (kemDecap_hoareTriple sk cipher).pf
    simp only [hoareTriple, wp, OptionT.run, ← h_out] at this
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [Bytes.Has BytesPart.Functor] [ExecTrace.Has Broken.TracePart.Exec] [Bytes.Invariants.Has BytesPart.invariants] into Bytes.AttackerKnows_implies_Publishable.merge from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,

end AttackerKnowledgeTheorem

namespace Broken

variable [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def] [Bytes.Invariants.Def]
variable [Bytes.Has KEM.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Has KEM.BytesPart.invariants]

@[instance]
theorem kemPkInvert.proof (pk: Bytes)
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
  simp only [Bytes.Invariant.eq, KEM.Pk.BytesPart.invariants] at h
  simp only [Label.canFlow, Broken.label, Broken.ThisKemPkHasBeenBroken] at h
  simp only [Bytes.Publishable]
  grind

public
instance: ProtocolEvent.EventInv (BrokenKemEvent) where
  invariant _ _ := True

#combine into
  ProofTrace,
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from ProtocolEvent Broken.BrokenKemEvent

variable [Bytes.Invariants.Lawful]
variable [ExecTrace.Has Network.TracePart.Exec]
variable [ProofTrace.Has Broken.TracePart.Proof] [ProofTrace.Has Network.TracePart.Proof]
variable [Trace.Invariant.Has Network.TracePart.Proof]
variable [Trace.Invariant.Has Broken.TracePart.Proof]

@[instance]
theorem breakKemPk.proof (msgHandle: Nat)
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
  grind

public instance: Trace.Reachable_implies_Invariant.Part breakKemPk.transitionSystem := .mk (fun (msgHandle) => breakKemPk.proof msgHandle)

end Broken

end DY.KEM
