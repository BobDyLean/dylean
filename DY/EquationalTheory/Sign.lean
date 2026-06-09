module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation -- HoareTriplePure

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

namespace Vk

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

end Vk

namespace Sign

public
structure SubF (Bytes: Type) where
  sk: Bytes
  nonce: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk, nonce, msg} => sizeOf sk + sizeOf nonce + sizeOf msg

public
instance: ALaCarte.Representable SubF where
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

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    64

end Sign

#combine into BytesFunctor, BytesLength from
  Vk,
  Sign

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Vk.SubF.pack (x: Vk.SubF Bytes) := BytesView.pack x
public abbrev Sign.SubF.pack (x: Sign.SubF Bytes) := BytesView.pack x

public
instance: CanSign Bytes where
  vk sk :=
    ({sk}: Vk.SubF Bytes).pack

  sign sk nonce msg :=
    ({sk, nonce, msg}: Sign.SubF Bytes).pack

  verify vk msg sig :=
    match sig.view? Sign.SubF with
    | some { sk, nonce := _, msg := msg' } =>
      msg = msg' &&
      vk = ({sk} : Vk.SubF Bytes).pack
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

public
def vk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = vk sk ∧
      p sk

public
def sign.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk nonce msg,
      out = sign sk nonce msg ∧
      Kleene.Forall p [sk, nonce, msg]

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  vk,
  sign

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_vk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (vk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove vk.attackerKnowledge
  simp only [vk.attackerKnowledge]
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
  apply Bytes.AttackerKnows.prove sign.attackerKnowledge
  simp only [sign.attackerKnowledge, Kleene.Forall]
  grind

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has Signature.SubF]

public
def Vk.invariants: Bytes.PartialInvariants Vk.SubF where
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
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop

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
theorem SignPredProof.pred_later_fast
  [BytesInvariants] [SignPred] [SignPredProof] [BytesInvariantsProofs]
  (skUsg: Usage) (vk msg: Bytes) (tr1 tr2: ProofTrace)
  : vk.Invariant tr1 →
    msg.Invariant tr1 →
    tr1 ≤ tr2 →
    SignPred.pred skUsg vk msg tr1 →
    SignPred.pred skUsg vk msg tr2
:= by grind

grind_pattern [grind_later] SignPredProof.pred_later_fast => tr1 ≤ tr2, SignPred.pred skUsg vk msg tr1

public
def Sign.invariants [SignPred]: Bytes.PartialInvariants Sign.SubF where
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

#combine [BytesFunctor.Has SubF] [SignPred] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has Vk.invariants] [SignPredProof]
from
  Vk,
  Sign

end Invariants

-- Temporarly close the namespace to define Bytes.SignkeyHasUsage and Bytes.signkeyLabel
end Signature

section ExtractSignKey

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]
variable [BytesFunctor.Has Signature.SubF]

noncomputable
def Signature.extractSignkey (vk: Bytes): Option Bytes :=
  match vk.view? Signature.Vk.SubF with
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
theorem Bytes.SignkeyHasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.SignkeyHasUsage usg tr1 →
    b.SignkeyHasUsage usg tr2
:= by grind

grind_pattern [grind_later] Bytes.SignkeyHasUsage_later_fast => tr1 ≤ tr2, b.SignkeyHasUsage usg tr1

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

public
theorem Bytes.signkeyLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.signkeyLabel tr1 = b.signkeyLabel tr2
:= by grind

grind_pattern [grind_later] Bytes.signkeyLabel_later_fast => tr1 ≤ tr2, b.signkeyLabel tr1

end ExtractSignKey

namespace Signature

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
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
    have := Bytes.pack_view? Sign.SubF sig
    simp only [heq] at this
    subst this
    have: ({sk}: Vk.SubF Bytes).pack = CanSign.vk sk := rfl
    have := Bytes.HasUsage_inj sk skUsg
    simp_all [Bytes.Invariant.eq, Sign.invariants]
    grind
  · simp

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  [SignPred]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (sk: Bytes)
  : HoareTriplePure
    (vk sk)
    (fun tr =>
      sk.Invariant tr
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
where
  pf := by
    grind [vk.Invariant, vk.label]

public
instance
  (sk nonce msg: Bytes)
  : HasGhostArgumentType (sign sk nonce msg) Usage
where
  dummy := ()

public
def signMetaprog: GhostParameterFinder where
  findGhost mvar e :=
  Lean.withTraceNode `Step (fun _ => pure m!"signMetaprog") do
    let sk_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let nonce_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let msg_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let signToUnify ← Lean.Meta.mkAppM ``sign #[sk_mvar, nonce_mvar, msg_mvar]
    trace[Step] "gonna unify {e} and {signToUnify}"
    unless ← Lean.Meta.isDefEq e signToUnify do
      throwError "signMetaprog: cannot unify {e} and {signToUnify}"
    trace[Step] "got {signToUnify}"

    let usg_mvar: Lean.Expr := .mvar mvar
    let tr_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``ProofTrace #[none]))
    let hasUsageToUnify ← Lean.Meta.mkAppOptM ``Bytes.HasUsage #[none, none, none, none, sk_mvar, usg_mvar, tr_mvar]
    trace[Step] "gonna find {hasUsageToUnify} in assumptions"
    let .mvar hasUsageMvar ← Lean.Meta.mkFreshExprMVar hasUsageToUnify
      | throwError ""
    unless ← hasUsageMvar.assumptionCore do
      throwError "Cannot find `sk.HasUsage _ _` in the context, please supply usage manually using `with ⟨ ... ⟩`"
    pure ()

public
instance
  (sk nonce msg: Bytes)
  : HasGhostMetaprogram (sign sk nonce msg) signMetaprog
where
  dummy := ()

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  [SignPred]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (sk nonce msg: Bytes) (skUsg: Usage)
  : HoareTriplePureGhost
    (sign sk nonce msg)
    (skUsg)
    (fun tr =>
      sk.Invariant tr ∧
      nonce.Invariant tr ∧
      msg.Invariant tr ∧
      sk.HasUsage skUsg tr ∧
      --nonce `has_usage tr` SigNonce /\
      (sk.label tr).canFlow (nonce.label tr) tr.erase ∧
      (
        (
          skUsg.type = "SigKey" ∧
          SignPred.pred skUsg (vk sk) msg tr
        ) ∨ (
          (sk.label tr).canFlow Label.pub tr.erase
        )
      )
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = msg.label tr
    )
where
  pf := by
    simp only [sign.label]
    grind [sign.Invariant sk nonce msg skUsg]

public
instance
  (vkey msg sig: Bytes): HasGhostArgumentType (verify vkey msg sig) Usage
where
  dummy := ()

public
def verifyMetaprog: GhostParameterFinder where
  findGhost mvar e :=
  Lean.withTraceNode `Step (fun _ => pure m!"verifyMetaprog") do
    let vkey_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let msg_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let sig_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let verifyToUnify ← Lean.Meta.mkAppM ``verify #[vkey_mvar, msg_mvar, sig_mvar]
    trace[Step] "gonna unify {e} and {verifyToUnify}"
    unless ← Lean.Meta.isDefEq e verifyToUnify do
      throwError "verifyMetaprog: cannot unify {e} and {verifyToUnify}"
    trace[Step] "got {verifyToUnify}"

    let usg_mvar: Lean.Expr := .mvar mvar
    let tr_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``ProofTrace #[none]))
    let hasUsageToUnify ← Lean.Meta.mkAppOptM ``Bytes.SignkeyHasUsage #[none, none, none, none, vkey_mvar, usg_mvar, tr_mvar]
    trace[Step] "gonna find {hasUsageToUnify} in assumptions"
    let .mvar hasUsageMvar ← Lean.Meta.mkFreshExprMVar hasUsageToUnify
      | throwError ""
    unless ← hasUsageMvar.assumptionCore do
      throwError "Cannot find `vk.SignkeyHasUsage _ _` in the context, please supply usage manually using `with ⟨ ... ⟩`"

public
instance
  (vkey msg sig: Bytes): HasGhostMetaprogram (verify vkey msg sig) verifyMetaprog
where
  dummy := ()

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  [SignPred]
  [BytesInvariants] [BytesInvariants.Has invariants]
  (vkey msg sig: Bytes) (skUsg: Usage)
  : HoareTriplePureGhost
    (verify vkey msg sig)
    (skUsg: Usage)
    (fun tr =>
      vkey.Invariant tr ∧
      msg.Invariant tr ∧
      sig.Invariant tr ∧
      vkey.SignkeyHasUsage skUsg tr
    )
    (fun res tr =>
      res → (
        (
          skUsg.type = "SigKey" →
          SignPred.pred skUsg vkey msg tr
        ) ∨ (
          (vkey.signkeyLabel tr).canFlow Label.pub tr.erase
        )
      )
    )
where
  pf := by
    grind [verify.Invariant vkey msg sig skUsg]

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [SignPred]
variable [BytesInvariants.Has invariants]

-- Preserve publishability

public
instance: SubAttackerKnowledgeTheorem vk.attackerKnowledge where
  pf := by
    simp only [vk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

public
instance: SubAttackerKnowledgeTheorem sign.attackerKnowledge where
  pf := by
    simp only [sign.attackerKnowledge]
    intro out tr h_tr ⟨sk, nonce, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable, Kleene.Forall]
    simp [sign, Bytes.Invariant.eq, Sign.invariants]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [SignPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  vk,
  sign

end AttackerKnowledgeTheorem

end DY.Signature
