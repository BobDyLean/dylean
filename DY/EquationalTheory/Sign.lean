module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.Signature

public
class CanSign (Bytes: Type u) where
  vk: (sk: Bytes) → Bytes
  sign: (sk: Bytes) → (nonce: Bytes) → (msg: Bytes) → Bytes
  verify: (vk: Bytes) → (msg: Bytes) → (sig: Bytes) → Bool

export CanSign (vk)
export CanSign (sign)
export CanSign (verify)

section Constructors

public
structure Vk (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf Vk where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable Vk where
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

public instance: ALaCarte.RepresentableDecidableEq Vk where
public instance: ALaCarte.RepresentableOrd Vk where
public instance: SubBytesFunctor Vk where

public
def Vk.length [BytesFunctor]: Bytes.PartialLength Vk :=
  fun _ _ =>
    32

public
structure Sign (Bytes: Type) where
  sk: Bytes
  nonce: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf Sign where
  sizeOf | {sk, nonce, msg} => sizeOf sk + sizeOf nonce + sizeOf msg

public
instance: ALaCarte.Representable Sign where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 3 }

  toRepr | {sk, nonce, msg} => {
    id := ()
    data := ()
    as := #v[sk, nonce, msg]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    let nonce := as[1]
    let msg := as[2]
    { sk, nonce, msg }
  from_to | {sk, nonce, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk, nonce, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq Sign where
public instance: ALaCarte.RepresentableOrd Sign where
public instance: SubBytesFunctor Sign where

public
def Sign.length [BytesFunctor]: Bytes.PartialLength Sign :=
  fun _ _ =>
    64

public
abbrev SubF.internal (id: Fin 2): Type → Type :=
  match id with
  | 0 => Vk
  | 1 => Sign

public
abbrev SubF := BytesFunctor.combine SubF.internal

public
instance: ∀ id, SubBytesFunctor (SubF.internal id)
  | 0 => inferInstance
  | 1 => inferInstance

public
instance: SubBytesFunctor SubF := inferInstance

public instance: BytesFunctor.HasStep Vk SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 0) SubF)
public instance: BytesFunctor.HasStep Sign SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 1) SubF)

public
def SubF.length.internal [BytesFunctor]: ∀ id, Bytes.PartialLength (SubF.internal id)
  | 0 => Vk.length
  | 1 => Sign.length

public
abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  Bytes.PartialLength.combine SubF.length.internal

public instance [BytesFunctor] [BytesLength]: BytesLength.HasStep Vk.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 0) SubF.length)
public instance [BytesFunctor] [BytesLength]: BytesLength.HasStep Sign.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 1) SubF.length)

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Vk.pack (x: Vk Bytes) := BytesView.pack x
public abbrev Sign.pack (x: Sign Bytes) := BytesView.pack x

public
instance: CanSign Bytes where
  vk sk :=
    ({sk}: Vk Bytes).pack

  sign sk nonce msg :=
    ({sk, nonce, msg}: Sign Bytes).pack

  verify vk msg sig :=
    match sig.view? Sign with
    | some { sk, nonce := _, msg := msg' } =>
      msg = msg' &&
      vk = ({sk} : Vk Bytes).pack
    | none => false

public
theorem verify_sign
  (sk nonce msg: Bytes)
  : verify (vk sk) msg (sign sk nonce msg) = true
:= by
  simp only [verify, vk, sign]
  grind

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]

def attKnowsVk: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = vk sk ∧
      p sk

def attKnowsSign: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk nonce msg,
      out = sign sk nonce msg ∧
      Kleene.Forall p [sk, nonce, msg]

def attackerKnowledge.internal (id: Fin 2): SubAttackerKnowledge SubF :=
  match id with
  | 0 => attKnowsVk
  | 1 => attKnowsSign

public
def attackerKnowledge: SubAttackerKnowledge SubF :=
  SubAttackerKnowledge.combine' attackerKnowledge.internal

instance: AttackerKnowledge.HasStep attKnowsVk attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine' attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep attKnowsSign attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine' attackerKnowledge.internal))

variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_vk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (vk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove attKnowsVk
  simp only [attKnowsVk]
  grind

public
theorem attacker_knows_sign
  (sk nonce msg: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    (sign sk nonce msg).AttackerKnows tr
:= by
  intro h_inp h_nonce h_msg
  apply Bytes.AttackerKnows.prove attKnowsSign
  simp only [attKnowsSign, Kleene.Forall]
  grind

end AttackerKnowledge

section Invariants

variable [TraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def Vk.invariants: Bytes.PartialInvariants Vk where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := sk} rec tr =>
    Usage.nothing

  label := fun {sk := sk} rec tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
def Vk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Vk.invariants where

section VkLemmas

variable [BytesInvariants] [BytesInvariants.Has Vk.invariants]

@[simp]
public
theorem vk.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  : (vk inp).WellFormed tr = inp.WellFormed tr
:= by
  simp [vk, Bytes.WellFormed.eq, Vk.invariants]

@[simp]
public
theorem vk.label
  (inp: Bytes) (tr: ProofTrace)
  : (vk inp).label tr = Label.pub
:= by
  simp [vk, Bytes.label.eq, Vk.invariants]

@[simp]
public
theorem vk.Invariant
  (inp: Bytes) (tr: ProofTrace)
  : inp.Invariant tr →
    (vk inp).Invariant tr
:= by
  simp [vk, Bytes.Invariant.eq, Vk.invariants]

end VkLemmas

public
class SignPred where
  pred: [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop

public
class SignPredProof [BytesInvariants] [SignPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ skUsg vk msg tr1 tr2,
      vk.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      SignPred.pred skUsg vk msg tr1 →
      SignPred.pred skUsg vk msg tr2

grind_pattern SignPredProof.pred_later => tr1 ≤ tr2, SignPred.pred skUsg vk msg tr1

public
def Sign.invariants [SignPred]: Bytes.PartialInvariants Sign where
  well_formed := fun {sk, nonce, msg} rec tr =>
      (rec sk) tr ∧
      (rec nonce) tr ∧
      (rec msg) tr

  usage := fun {sk, nonce, msg} rec tr =>
    Usage.nothing

  label := fun {sk, nonce, msg} rec tr =>
    (rec msg) tr

  invariant := fun {sk, nonce, msg} rec tr =>
      (rec sk) tr ∧
      (rec nonce) tr ∧
      (rec msg) tr ∧
      (
        (
          exists sk_usg,
          -- Honest case:
          -- - the key has the usage of signature key
          sk.HasUsage sk_usg tr ∧
          sk_usg.type = "SigKey" ∧
          -- - the custom (protocol-specific) invariant hold (authentication)
          SignPred.pred sk_usg (vk sk) msg tr ∧
          -- - the nonce is more secret than the signature key
          --   (this is because the standard EUF-CMA security assumption on signatures
          --   do not have any guarantees when the nonce is leaked to the attacker,
          --   in practice knowing the nonce used to sign a message
          --   can be used to obtain the private key,
          --   hence this restriction)
          (sk.label tr).canFlow (nonce.label tr) tr.erase ∧
          -- - the nonce has the correct usage (for the same reason as above)
          -- nonce `has_usage tr` SigNonce
          True
        ) ∨ (
          -- Attacker case:
          -- the attacker knows the signature key.
          -- The message is not required to be known by the attacker:
          -- the EUF-CMA security assumption on signatures doesn't guarantee
          -- that in case of signature forgeries.
          (sk.label tr).canFlow Label.pub tr.erase
        )
      )

public
def Sign.invariantsProofs [BytesInvariants] [BytesInvariants.Has Vk.invariants] [SignPred] [SignPredProof]: Bytes.PartialInvariantsProofs Sign.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    -- TODO: grind set
    grind [vk.WellFormed]

public
def invariants.internal [SignPred]: (id: Fin 2) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => Vk.invariants
  | 1 => Sign.invariants

public
abbrev invariants [SignPred]: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

public instance [BytesInvariants] [SignPred]: BytesInvariants.HasStep Vk.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
public instance [BytesInvariants] [SignPred]: BytesInvariants.HasStep Sign.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)

def invariantsProofs.internal [BytesInvariants] [BytesInvariants.Has Vk.invariants] [SignPred] [SignPredProof]: (id: Fin 2) → Bytes.PartialInvariantsProofs (invariants.internal id)
  | 0 => Vk.invariantsProofs
  | 1 => Sign.invariantsProofs

public
def invariantsProofs [BytesInvariants] [BytesInvariants.Has Vk.invariants] [SignPred] [SignPredProof]: Bytes.PartialInvariantsProofs invariants :=
  Bytes.PartialInvariantsProofs.combine invariantsProofs.internal

end Invariants

-- Temporarly close the namespace to define Bytes.SignkeyHasUsage and Bytes.signkeyLabel
end Signature

section ExtractSignKey

variable [TraceTypes]
variable [BytesFunctor]
variable [BytesFunctor.Has Signature.SubF]

noncomputable
def Signature.extractSignkey (vk: Bytes): Option Bytes :=
  match vk.view? Signature.Vk with
  | some { sk } =>
    some sk
  | none => none

theorem Signature.vk_extractSignkey (b: Bytes):
  match extractSignkey b with
  | none => True
  | some sk => b = Signature.vk sk
:= by
  simp [extractSignkey, Signature.vk]
  grind

theorem Signature.extractSignkey.preserves_WellFormed
  [BytesInvariants] [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
: ExtractPreservesWellFormed extractSignkey
:= by
  simp [ExtractPreservesWellFormed]
  grind [Signature.vk_extractSignkey, Signature.vk.WellFormed]

public
def Bytes.SignkeyHasUsage
  [BytesInvariants]
  (vk: Bytes) (skUsg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage Signature.extractSignkey vk skUsg tr

public
theorem Bytes.SignkeyHasUsage_vk
  [BytesInvariants]
  (sk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : (Signature.vk sk).SignkeyHasUsage skUsg tr = sk.HasUsage skUsg tr
:= by
  simp [Bytes.SignkeyHasUsage, Bytes.XXXHasUsage, Signature.extractSignkey, Signature.vk]
  grind

grind_pattern Bytes.SignkeyHasUsage_vk => (Signature.vk sk).SignkeyHasUsage skUsg tr

public
theorem Bytes.SignkeyHasUsage_later
  [BytesInvariants] [BytesInvariantsProofs]
  [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.SignkeyHasUsage usg tr1 →
    b.SignkeyHasUsage usg tr2
:= by
  simp [Bytes.SignkeyHasUsage]
  apply Bytes.XXXHasUsage_later Signature.extractSignkey Signature.extractSignkey.preserves_WellFormed

grind_pattern Bytes.SignkeyHasUsage_later => tr1 ≤ tr2, b.SignkeyHasUsage usg tr1

public
noncomputable
def Bytes.signkeyLabel
  [BytesInvariants]
  (vk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel Signature.extractSignkey vk tr

public
theorem Bytes.signkeyLabel_vk
  [BytesInvariants]
  [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
  (sk: Bytes) (tr: ProofTrace)
  : (Signature.vk sk).signkeyLabel tr = sk.label tr
:= by
  simp [Bytes.signkeyLabel, Bytes.xxxLabel, Signature.extractSignkey, Signature.vk]
  grind

grind_pattern Bytes.signkeyLabel_vk => (Signature.vk sk).signkeyLabel tr

public
theorem Bytes.signkeyLabel_later
  [BytesInvariants] [BytesInvariantsProofs]
  [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.signkeyLabel tr1 = b.signkeyLabel tr2
:= by
  simp [Bytes.signkeyLabel]
  apply Bytes.xxxLabel_later Signature.extractSignkey Signature.extractSignkey.preserves_WellFormed

grind_pattern Bytes.signkeyLabel_later => tr1 ≤ tr2, b.signkeyLabel tr1

end ExtractSignKey

namespace Signature

section Invariants

variable [TraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

variable [SignPred]
variable [BytesInvariants]
variable [BytesInvariants.Has invariants]

@[simp]
public
theorem sign.WellFormed
  (sk nonce msg: Bytes) (tr: ProofTrace)
  : (sign sk nonce msg).WellFormed tr = (
      sk.WellFormed tr ∧
      nonce.WellFormed tr ∧
      msg.WellFormed tr
    )
:= by
  simp [sign, Bytes.WellFormed.eq, Sign.invariants]

@[simp]
public
theorem sign.label
  (sk nonce msg: Bytes) (tr: ProofTrace)
  : (sign sk nonce msg).label tr = msg.label tr
:= by
  simp [sign, Bytes.label.eq, Sign.invariants]

@[simp]
public
theorem sign.Invariant
  (sk nonce msg: Bytes) (sk_usg: Usage) (tr: ProofTrace)
  : (
      sk.Invariant tr ∧
      nonce.Invariant tr ∧
      msg.Invariant tr ∧
      sk.HasUsage sk_usg tr ∧
      --nonce `has_usage tr` SigNonce /\
      (sk.label tr).canFlow (nonce.label tr) tr.erase ∧
      (
        (
          sk_usg.type = "SigKey" ∧
          SignPred.pred sk_usg (vk sk) msg tr
        ) ∨ (
          (sk.label tr).canFlow Label.pub tr.erase
        )
      )
    ) →
    (sign sk nonce msg).Invariant tr
:= by
  have := vk.WellFormed sk tr
  simp [sign, Bytes.Invariant.eq, Sign.invariants]
  grind

@[simp]
public
theorem verify.Invariant
  (vk msg sig: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : vk.Invariant tr →
    msg.Invariant tr →
    sig.Invariant tr →
    vk.SignkeyHasUsage skUsg tr →
    verify vk msg sig → (
      (
        skUsg.type = "SigKey" →
        SignPred.pred skUsg vk msg tr
      ) ∨ (
        (vk.signkeyLabel tr).canFlow Label.pub tr.erase
      )
    )
:= by
  simp [verify]
  split
  · rename_i sk nonce msg heq
    have := Bytes.pack_view? Sign sig
    simp only [heq] at this
    subst this
    have: ({sk}: Vk Bytes).pack = CanSign.vk sk := rfl
    have := Bytes.HasUsage_inj sk skUsg
    simp_all [Bytes.Invariant.eq, Sign.invariants]
    grind
  · simp

end Invariants

section AttackerKnowledgeTheorem

variable [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [SignPred]
variable [BytesInvariants.Has invariants]

-- Preserve publishability

instance: SubAttackerKnowledgeTheorem attKnowsVk where
  pf := by
    simp only [attKnowsVk]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

instance: SubAttackerKnowledgeTheorem attKnowsSign where
  pf := by
    simp only [attKnowsSign]
    intro out tr h_tr ⟨sk, nonce, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable, Kleene.Forall]
    simp [sign, Bytes.Invariant.eq, Sign.invariants]
    grind

instance: ∀ id, SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsVk)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsSign)

public instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' attackerKnowledge.internal))

end AttackerKnowledgeTheorem

end DY.Signature
