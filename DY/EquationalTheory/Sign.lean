import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.EquationalTheoryInvariants
import DY.Bytes.AttackerKnowledge

namespace DY.Signature

class CanSign (Bytes: Type u) where
  vk: Bytes → Bytes
  -- sk nonce msg
  sign: (sk: Bytes) → (nonce: Bytes) → (msg: Bytes) → Bytes
  -- vk msg sig
  verify: Bytes → Bytes → Bytes → Bool

export CanSign (vk)
export CanSign (sign)
export CanSign (verify)

instance: Ord Unit where
  compare _ _ := .eq

instance: Std.ReflOrd Unit where
  compare_self := by grind

instance: Std.LawfulEqOrd Unit where
  eq_of_compare := by grind

instance: Std.OrientedOrd Unit where
  eq_swap := by grind [Ordering.swap]

instance: Std.TransOrd Unit where
  isLE_trans := by grind

-- Constructors

abbrev Vk.ctor: BytesCtor where
  data := Unit
  nBytes := 1
  dataOrd := inferInstance
  dataReflOrd := inferInstance
  dataLawfulEqOrd := inferInstance
  dataOrientedOrd := inferInstance
  dataTransOrd := inferInstance

class abbrev Vk.HasCtor [BytesCtors] := Bytes.HasCtor Vk.ctor

abbrev Vk.id [BytesCtors] [Vk.HasCtor]: CtorId := Bytes.HasCtor.id Vk.ctor

abbrev Vk.View [BytesCtors] [Vk.HasCtor] := BytesView Vk.id

abbrev Sign.ctor: BytesCtor where
  data := Unit
  nBytes := 3
  dataOrd := inferInstance
  dataReflOrd := inferInstance
  dataLawfulEqOrd := inferInstance
  dataOrientedOrd := inferInstance
  dataTransOrd := inferInstance

class abbrev Sign.HasCtor [BytesCtors] := Bytes.HasCtor Sign.ctor

abbrev Sign.id [BytesCtors] [Sign.HasCtor]: CtorId := Bytes.HasCtor.id Sign.ctor

abbrev Sign.View [BytesCtors] [Sign.HasCtor] := BytesView Sign.id

instance [BytesCtors] [Vk.HasCtor] [Sign.HasCtor]: CanSign Bytes where
  vk sk :=
    ({
      data := (),
      dataBytes := V[sk]
    } : Vk.View).pack

  sign sk nonce msg :=
    ({
      data := (),
      dataBytes := V[sk, nonce, msg]
    } : Sign.View).pack

  verify vk msg sig :=
    match sig.view? Sign.id with
    | some { data := (), dataBytes := V[sk, _nonce, msg'] } =>
      msg = msg' &&
      vk = ({ data := (), dataBytes := V[sk] } : Vk.View).pack
    | none => false

theorem verify_sign
  [BytesCtors] [Vk.HasCtor] [Sign.HasCtor]
  (sk nonce msg: Bytes)
  :
    verify (vk sk) msg (sign sk nonce msg)
  := by
    simp only [verify, vk, sign]
    grind

def ctors := [Vk.ctor, Sign.ctor]

instance [BytesCtors] [tc: Bytes.HasCtors ctors]: Bytes.HasCtor Vk.ctor := tc.tc (Fin.mk 0 (by simp [ctors]))
instance [BytesCtors] [tc: Bytes.HasCtors ctors]: Bytes.HasCtor Sign.ctor := tc.tc (Fin.mk 1 (by simp [ctors]))

-- Equational theory

def attKnowsVk [BytesCtors] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ sk,
      out = vk sk ∧
      p sk
  pred_scott_continuous := by
    sorry

def attKnowsSign [BytesCtors] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ sk nonce msg,
      out = sign sk nonce msg ∧
      p sk ∧
      p nonce ∧
      p msg
  pred_scott_continuous := by
    sorry

def equationalTheory: EquationalTheory where
  ctors := ctors
  attackerKnowledge := [attKnowsVk, attKnowsSign]

instance: EquationalTheory.CtorsEq equationalTheory ctors where pf := rfl

instance: NeZero equationalTheory.ctors.length where
  out := by simp [equationalTheory, ctors]

theorem attacker_knows_vk
  [EquationalTheories]
  [HasEquationalTheory equationalTheory]
  (sk: Bytes) (tr: Trace α)
  :
    sk.AttackerKnows tr →
    (vk sk).AttackerKnows tr
  := by
    intro h_inp
    apply Bytes.AttackerKnows.prove equationalTheory attKnowsVk
    · simp [equationalTheory]
    simp only [attKnowsVk]
    grind

theorem attacker_knows_sign
  [EquationalTheories]
  [HasEquationalTheory equationalTheory]
  (sk nonce msg: Bytes) (tr: Trace α)
  :
    sk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    (sign sk nonce msg).AttackerKnows tr
  := by
    intro h_inp h_nonce h_msg
    apply Bytes.AttackerKnows.prove equationalTheory attKnowsSign
    · simp [equationalTheory]
    simp only [attKnowsSign]
    grind

-- Invariants

def Vk.invariants [BytesCtors]: BytesCtorInvariants.Internal Vk.ctor where
  well_formed := {
    func := fun () V[sk] rec tr =>
      rec sk tr
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk] := dataBytes
      simp_all +arith
  }
  well_formed_later data dataBytes rec_wf := by
    let V[sk] := dataBytes
    simp_all +arith [BytesWellFormedLaterT]
    grind

  usage := {
    func data dataBytes rec tr := Usage.nothing
    func_wf := by grind
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func := fun () V[sk] rec tr =>
      Label.pub
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk] := dataBytes
      simp_all +arith
  }
  label_later data dataBytes rec_wf rec_usg := by
    let V[sk] := dataBytes
    simp_all +arith [GetLabelLaterT]

  invariant := {
    func := fun () V[sk] rec tr =>
      rec sk tr
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk] := dataBytes
      simp_all +arith
  }
  invariant_implies_wellformed data dataBytes rec_inv rec_wf := by
    let V[sk] := dataBytes
    simp_all +arith [BytesInvariantImpliesBytesWellFormedT]
  invariant_later data dataBytes rec := by
    let V[sk] := dataBytes
    simp_all +arith [BytesInvariantLaterT]
    grind

class abbrev Vk.HasInvariants [BytesCtors] [Vk.HasCtor] [BytesCtorsInvariants] := HasBytesInvariants (Vk.id) Vk.invariants

@[simp]
theorem vk.WellFormed
  [BytesCtors] [BytesWellFormed]
  [Bytes.HasCtors ctors] [HasBytesWellFormed Vk.id Vk.invariants.well_formed]
  (inp: Bytes) (tr: ProofTrace)
  :
    (vk inp).WellFormed tr = inp.WellFormed tr
  := by
    simp [vk, Bytes.WellFormed.eq, Vk.invariants]

@[simp]
theorem vk.label
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Vk.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  : (vk inp).label tr = Label.pub
  := by
    simp [vk, Bytes.label.eq, Vk.invariants]

@[simp]
theorem vk.Invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Vk.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  :
    (vk inp).Invariant tr →
    inp.Invariant tr
  := by
    simp [vk, Bytes.Invariant.eq, Vk.invariants]

noncomputable
def extractSignkey [BytesCtors] [Vk.HasCtor] (vk: Bytes): Option Bytes :=
  match vk.view? Vk.id with
  | some { data := (), dataBytes := V[sk] } =>
    some sk
  | none => none

theorem vk_extractSignkey [BytesCtors] [Vk.HasCtor] [Sign.HasCtor] (b: Bytes):
  match extractSignkey b with
  | none => True
  | some sk => b = vk sk
  := by
    simp [extractSignkey, vk]
    grind

theorem extractSignkey.preserves_WellFormed [BytesCtors] [BytesWellFormed] [Bytes.HasCtors ctors] [HasBytesWellFormed Vk.id Vk.invariants.well_formed]: ExtractPreservesWellFormed extractSignkey
  := by
    simp [ExtractPreservesWellFormed]
    grind [vk_extractSignkey, vk.WellFormed]

end Signature

def Bytes.SignkeyHasUsage [BytesCtors] [GetUsage] [GetLabel] [Signature.Vk.HasCtor] (vk: Bytes) (skUsg: Usage) (tr: ProofTrace): Prop :=
  Bytes.XXXHasUsage Signature.extractSignkey vk skUsg tr

theorem Bytes.SignkeyHasUsage_vk
  [BytesCtors] [GetUsage] [GetLabel] [Bytes.HasCtors Signature.ctors]
  (sk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : (Signature.vk sk).SignkeyHasUsage skUsg tr = sk.HasUsage skUsg tr
  := by
    simp [Bytes.SignkeyHasUsage, Bytes.XXXHasUsage, Signature.extractSignkey, Signature.vk]
    grind

grind_pattern Bytes.SignkeyHasUsage_vk => (Signature.vk sk).SignkeyHasUsage skUsg tr

theorem Bytes.SignkeyHasUsage_later
  [BytesCtors] [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  [HasCtors Signature.ctors] [HasBytesWellFormed Signature.Vk.id Signature.Vk.invariants.well_formed]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.SignkeyHasUsage usg tr1 →
    b.SignkeyHasUsage usg tr2
  := by
    simp [Bytes.SignkeyHasUsage]
    apply Bytes.XXXHasUsage_later Signature.extractSignkey Signature.extractSignkey.preserves_WellFormed

grind_pattern Bytes.SignkeyHasUsage_later => tr1 ≤ tr2, b.SignkeyHasUsage usg tr1

noncomputable
def Bytes.signkeyLabel [BytesCtors] [GetLabel] [Signature.Vk.HasCtor] (vk: Bytes) (tr: ProofTrace): Label :=
  Bytes.xxxLabel Signature.extractSignkey vk tr

theorem Bytes.signkeyLabel_vk
  [BytesCtors] [GetLabel] [Bytes.HasCtors Signature.ctors]
  (sk: Bytes) (tr: ProofTrace)
  : (Signature.vk sk).signkeyLabel tr = sk.label tr
  := by
    simp [Bytes.signkeyLabel, Bytes.xxxLabel, Signature.extractSignkey, Signature.vk]
    grind

grind_pattern Bytes.signkeyLabel_vk => (Signature.vk sk).signkeyLabel tr

theorem Bytes.signkeyLabel_later
  [BytesCtors] [BytesWellFormed] [GetUsage] [GetLabel] [GetLabelLater]
  [HasCtors Signature.ctors] [HasBytesWellFormed Signature.Vk.id Signature.Vk.invariants.well_formed]
  (b: Bytes) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.signkeyLabel tr1 = b.signkeyLabel tr2
  := by
    simp [Bytes.signkeyLabel]
    apply Bytes.xxxLabel_later Signature.extractSignkey Signature.extractSignkey.preserves_WellFormed

grind_pattern Bytes.signkeyLabel_later => tr1 ≤ tr2, b.signkeyLabel tr1

namespace Signature

class SignPred [BytesCtors] where
  pred: [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop
  pred_later:
    [BytesWellFormed] → [GetUsage] → [GetLabel] →
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ skUsg vk msg tr1 tr2,
      vk.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      pred skUsg vk msg tr1 →
      pred skUsg vk msg tr2

grind_pattern SignPred.pred_later => tr1 ≤ tr2, SignPred.pred skUsg vk msg tr1

def Sign.invariants [BytesCtors] [SignPred] [Bytes.HasCtors ctors]: BytesCtorInvariants.Internal Sign.ctor where
  well_formed := {
    func := fun () V[sk, nonce, msg] rec tr =>
      rec sk tr ∧
      rec nonce tr ∧
      rec msg tr
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk, nonce, msg] := dataBytes
      simp_all +arith
  }
  well_formed_later data dataBytes rec_wf := by
    let V[sk, nonce, msg] := dataBytes
    simp_all +arith [BytesWellFormedLaterT]
    grind

  usage := {
    func data dataBytes rec tr := Usage.nothing
    func_wf := by grind
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func := fun () V[sk, nonce, msg] rec tr =>
      rec msg tr
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk, nonce, msg] := dataBytes
      simp_all +arith
  }
  label_later data dataBytes rec_wf rec_usg := by
    let V[sk, nonce, msg] := dataBytes
    simp_all +arith [GetLabelLaterT]
    grind

  invariant := {
    func := fun () V[sk, nonce, msg] rec tr =>
      rec sk tr ∧
      rec nonce tr ∧
      rec msg tr ∧
      (vk sk).WellFormed tr ∧
      (
        (
          exists sk_usg,
          -- Honest case:
          -- - the key has the usage of signature key
          -- TODO has usage
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
          (sk.label tr).canFlow (nonce.label tr) tr ∧
          -- - the nonce has the correct usage (for the same reason as above)
          -- nonce `has_usage tr` SigNonce
          True
        ) ∨ (
          -- Attacker case:
          -- the attacker knows the signature key.
          -- The message is not required to be known by the attacker:
          -- the EUF-CMA security assumption on signatures doesn't guarantee
          -- that in case of signature forgeries.
          (sk.label tr).canFlow Label.pub tr
        )
      )

    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk, nonce, msg] := dataBytes
      simp_all +arith
  }
  invariant_implies_wellformed data dataBytes rec_inv rec_wf := by
    let V[sk, nonce, msg] := dataBytes
    simp_all +arith [BytesInvariantImpliesBytesWellFormedT]
  invariant_later data dataBytes rec := by
    let V[sk, nonce, msg] := dataBytes
    simp_all +arith [BytesInvariantLaterT]
    grind [SignPred.pred_later]

class abbrev Sign.HasInvariants [BytesCtors] [Bytes.HasCtors ctors] [BytesCtorsInvariants] [SignPred] := HasBytesInvariants (Sign.id) Sign.invariants

@[simp]
theorem sign.WellFormed
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [SignPred] [Sign.HasInvariants]
  (sk nonce msg: Bytes) (tr: ProofTrace)
  :
    (sign sk nonce msg).WellFormed tr = (
      sk.WellFormed tr ∧
      nonce.WellFormed tr ∧
      msg.WellFormed tr
    )
  := by
    simp [sign, Bytes.WellFormed.eq, Sign.invariants]

@[simp]
theorem sign.label
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [SignPred] [Sign.HasInvariants]
  (sk nonce msg: Bytes) (tr: ProofTrace)
  : (sign sk nonce msg).label tr = msg.label tr
  := by
    simp [sign, Bytes.label.eq, Sign.invariants]

@[simp]
theorem sign.Invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [SignPred] [Vk.HasInvariants] [Sign.HasInvariants]
  (sk nonce msg: Bytes) (sk_usg: Usage) (tr: ProofTrace)
  :
    (
      sk.Invariant tr ∧
      nonce.Invariant tr ∧
      msg.Invariant tr ∧
      sk.HasUsage sk_usg tr ∧
      --nonce `has_usage tr` SigNonce /\
      (sk.label tr).canFlow (nonce.label tr) tr ∧
      (
        (
          sk_usg.type = "SigKey" ∧
          SignPred.pred sk_usg (vk sk) msg tr
        ) ∨ (
          (sk.label tr).canFlow Label.pub tr
        )
      )
    ) →
    (sign sk nonce msg).Invariant tr
  := by
    have := vk.WellFormed sk tr
    simp [sign, Bytes.Invariant.eq, Sign.invariants]
    grind

@[simp]
theorem verify.Invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [SignPred] [Vk.HasInvariants] [Sign.HasInvariants]
  (vk msg sig: Bytes) (skUsg: Usage) (tr: ProofTrace)
  :
    vk.Invariant tr →
    msg.Invariant tr →
    sig.Invariant tr →
    vk.SignkeyHasUsage skUsg tr →
    verify vk msg sig → (
      (
        skUsg.type = "SigKey" →
        SignPred.pred skUsg vk msg tr
      ) ∨ (
        (vk.signkeyLabel tr).canFlow Label.pub tr
      )
    )
  := by
    simp [verify]
    split
    · rename_i sk nonce msg heq
      have := Bytes.pack_view? sig Sign.id
      simp only [heq] at this
      subst this
      have: ({ data := (), dataBytes := V[sk] } : Vk.View).pack = CanSign.vk sk := rfl
      have := Bytes.HasUsage_inj sk skUsg
      simp_all [Bytes.Invariant.eq, Sign.invariants]
      grind
    · simp

def EquationalTheoryInvariant [EquationalTheories] [HasEquationalTheory equationalTheory] [SignPred]: EquationalTheoryInvariants equationalTheory where
  invariant
    | 0 => Vk.invariants
    | 1 => Sign.invariants

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory] [SignPred] [EquationalTheoryInvariant.Has]
  : HasBytesInvariants Vk.id Vk.invariants :=
  EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 0 (by simp [equationalTheory, ctors]))

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory] [SignPred] [EquationalTheoryInvariant.Has]
  : HasBytesInvariants Sign.id Sign.invariants :=
  EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 1 (by simp [equationalTheory, ctors]))

-- Preserve publishability

def Sign.attKnowsVk.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [SignPred] [Vk.HasInvariants]: attKnowsVk.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsVk]
    intro out tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [vk, Bytes.Invariant.eq, Vk.invariants]
    grind

def Sign.attKnowsSign.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [SignPred] [Vk.HasInvariants] [Sign.HasInvariants]: attKnowsSign.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsSign]
    intro out tr ⟨sk, nonce, msg, ⟨ h_out, h_sk, h_nonce, h_msg ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [sign, Bytes.Invariant.eq, Sign.invariants]
    grind

def Sign.PreservesPublishability
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory equationalTheory]
  [SignPred]
  [EquationalTheoryInvariant.Has]
  : EquationalTheory.PreservesPublishability equationalTheory where
  pf := by
    unfold equationalTheory
    simp
    constructor
    · exact Sign.attKnowsVk.preserves_publishability
    · exact attKnowsSign.preserves_publishability

end DY.Signature
