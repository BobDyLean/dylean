import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.EquationalTheoryInvariants
import DY.Bytes.AttackerKnowledge

namespace DY

class CanSign (Bytes: Type u) where
  vk: Bytes → Bytes
  -- sk nonce msg
  sign: Bytes → Bytes → Bytes → Bytes
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

def Sign.ctors := [Vk.ctor, Sign.ctor]

instance [BytesCtors] [tc: Bytes.HasCtors Sign.ctors]: Bytes.HasCtor Vk.ctor := tc.tc (Fin.mk 0 (by simp [Sign.ctors]))
instance [BytesCtors] [tc: Bytes.HasCtors Sign.ctors]: Bytes.HasCtor Sign.ctor := tc.tc (Fin.mk 1 (by simp [Sign.ctors]))

-- Equational theory

def Sign.attKnowsVk [BytesCtors] [Bytes.HasCtors Sign.ctors]: AttackerKnowledge where
  pred p out :=
    ∃ sk,
      out = vk sk ∧
      p sk
  pred_scott_continuous := by
    sorry

def Sign.attKnowsSign [BytesCtors] [Bytes.HasCtors Sign.ctors]: AttackerKnowledge where
  pred p out :=
    ∃ sk nonce msg,
      out = sign sk nonce msg ∧
      p sk ∧
      p nonce ∧
      p msg
  pred_scott_continuous := by
    sorry

def Sign.equationalTheory: EquationalTheory where
  ctors := Sign.ctors
  attackerKnowledge := [Sign.attKnowsVk, Sign.attKnowsSign]

instance: EquationalTheory.CtorsEq Sign.equationalTheory Sign.ctors where pf := rfl

instance: NeZero Sign.equationalTheory.ctors.length where
  out := by simp [Sign.equationalTheory, Sign.ctors]

theorem Sign.attacker_knows_vk
  [EquationalTheories]
  [HasEquationalTheory Sign.equationalTheory]
  (sk: Bytes) (tr: Trace α)
  :
    sk.AttackerKnows tr →
    (vk sk).AttackerKnows tr
  := by
    intro h_inp
    apply Bytes.AttackerKnows.prove Sign.equationalTheory Sign.attKnowsVk
    · simp [Sign.equationalTheory]
    simp only [Sign.attKnowsVk]
    grind

theorem Sign.attacker_knows_sign
  [EquationalTheories]
  [HasEquationalTheory Sign.equationalTheory]
  (sk nonce msg: Bytes) (tr: Trace α)
  :
    sk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    (sign sk nonce msg).AttackerKnows tr
  := by
    intro h_inp h_nonce h_msg
    apply Bytes.AttackerKnows.prove Sign.equationalTheory Sign.attKnowsSign
    · simp [Sign.equationalTheory]
    simp only [Sign.attKnowsSign]
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

class SignPred [BytesCtors] where
  pred: [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop
  pred_later:
    [BytesWellFormed] → [GetUsage] → [GetLabel] →
    ∀ skUsg vk msg tr1 tr2,
      vk.wellFormed tr1 →
      msg.wellFormed tr1 →
      tr1 ≤ tr2 →
      pred skUsg vk msg tr1 →
      pred skUsg vk msg tr2

def Sign.invariants [BytesCtors] [SignPred] [Bytes.HasCtors Sign.ctors]: BytesCtorInvariants.Internal Sign.ctor where
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

  usage := {
    func data dataBytes rec tr := Usage.nothing
    func_wf := by grind
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func := fun () V[sk, nonce, msg] rec tr =>
      Label.pub
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[sk, nonce, msg] := dataBytes
      simp_all +arith
  }
  label_later data dataBytes rec_wf rec_usg := by
    let V[sk, nonce, msg] := dataBytes
    simp_all +arith [GetLabelLaterT]

  invariant := {
    func := fun () V[sk, nonce, msg] rec tr =>
      rec sk tr ∧
      rec nonce tr ∧
      rec msg tr ∧
      (
        (
          exists sk_usg,
          -- Honest case:
          -- - the key has the usage of signature key
          -- TODO has usage
          sk.usage tr = sk_usg ∧
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
        ) \/ (
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
    intro _ _ tr1 tr2
    have := SignPred.pred_later (sk.usage tr1) (vk sk) msg tr1 tr2
    grind

class abbrev Sign.HasInvariants [BytesCtors] [Sign.HasCtor] [BytesCtorsInvariants] := HasBytesInvariants (Sign.id) Sign.invariants

@[simp]
theorem hash.wellFormed
  [BytesCtors] [BytesCtorsInvariants]
  [Sign.HasCtor] [Sign.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).wellFormed tr = inp.wellFormed tr
  := by
    simp [hash, Bytes.wellFormed.eq, Sign.invariants]

@[simp]
theorem hash.label
  [BytesCtors] [BytesCtorsInvariants]
  [Sign.HasCtor] [Sign.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  : (hash inp).label tr = inp.label tr
  := by
    simp [hash, Bytes.label.eq, Sign.invariants]

@[simp]
theorem hash.invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Sign.HasCtor] [Sign.HasInvariants]
  (inp: Bytes) (tr: ProofTrace)
  :
    (hash inp).invariant tr =
    inp.invariant tr
  := by
    simp [hash, Bytes.invariant.eq, Sign.invariants]

def Sign.EquationalTheoryInvariant [EquationalTheories]: EquationalTheoryInvariants Sign.equationalTheory where
  invariant
    | 0 => Sign.invariants

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory Sign.equationalTheory] [Sign.EquationalTheoryInvariant.Has]
  : HasBytesInvariants Sign.id Sign.invariants :=
  Sign.EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 0 (by simp [Sign.equationalTheory, Sign.ctors]))

-- Preserve publishability

def Sign.attKnowsSign.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors Sign.ctors] [Sign.HasInvariants]: Sign.attKnowsSign.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, Sign.attKnowsSign]
    intro out tr ⟨inp, ⟨ h_out, h_inp ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]

def Sign.PreservesPublishability
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory Sign.equationalTheory]
  [Sign.EquationalTheoryInvariant.Has]
  : EquationalTheory.PreservesPublishability Sign.equationalTheory where
  pf := by
    unfold Sign.equationalTheory
    simp
    exact attKnowsSign.preserves_publishability

end DY
