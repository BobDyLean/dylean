module

import DY.Meta
import DY.Meta.Utils
import all Examples.Ratchet.Specification
import Examples.Ratchet.Instance
public meta import Examples.Ratchet.Instance

namespace DY.Example.Ratchet

-- TODO: move, but where?
theorem liftM_parse_preserves_reachability
  {a: Type} [Comparse.ParseableSerializeable a]
  (config: ReachabilityConfig)
  (buf: Bytes)
  : (liftM (Comparse.parse buf): Traceful a).PreservesReachability config (fun _ => True) (fun res _ => Comparse.FormatRel buf res)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
  grind

def honestAttackerLoop (n: Nat) (aliceVkHandle aliceSkHandle bobVkHandle bobSkHandle aliceStHandle bobStHandle: Nat): Traceful Unit := do
  if n = 0 then return () else
  let (bobStHandle, msgHandle) ← sendUpdate "Bob" bobSkHandle bobStHandle
  let aliceStHandle ← processUpdate "Alice" bobVkHandle aliceStHandle msgHandle
  let (aliceStHandle, msgHandle) ← sendUpdate "Alice" aliceSkHandle aliceStHandle
  let bobStHandle ← processUpdate "Bob" aliceVkHandle bobStHandle msgHandle
  honestAttackerLoop (n-1) aliceVkHandle aliceSkHandle bobVkHandle bobSkHandle aliceStHandle bobStHandle

public
def honestAttacker: Traceful Unit := do
  let (_, aliceVkHandle, aliceSkHandle) ← LongTermKeys.generateKeyPair "Ratchet PKI" "Alice" -- 4
  let (_, bobVkHandle, bobSkHandle) ← LongTermKeys.generateKeyPair "Ratchet PKI" "Bob" -- 4

  let (aliceStHandle, msgHandle) ← initiate "Alice" "Bob" aliceSkHandle
  let bobStHandle ← processInitiate "Bob" "Alice" aliceVkHandle msgHandle

  honestAttackerLoop 10 aliceVkHandle aliceSkHandle bobVkHandle bobSkHandle aliceStHandle bobStHandle

#guard (honestAttacker.run Trace.nil).fst = some ()

-- Future work: we could design a step-like tactic to automate this proof
theorem honestAttackerLoop_PreservesReachability
  (n: Nat) (aliceVkHandle aliceSkHandle bobVkHandle bobSkHandle aliceStHandle bobStHandle: Nat)
  : (honestAttackerLoop n aliceVkHandle aliceSkHandle bobVkHandle bobSkHandle aliceStHandle bobStHandle).PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability

  intro tr h_tr h_pre
  unfold honestAttackerLoop
  split
  · apply Traceful.PreservesReachabilityFrom_pure
    · assumption
    grind
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (sendUpdate.reachability) _ ("Bob", bobSkHandle, bobStHandle)
  · assumption
  · simp [sendUpdate.reachability]
  intro ⟨ bobStHandle, msgHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (processUpdate.reachability) _ ("Alice", bobVkHandle, aliceStHandle, msgHandle)
  · assumption
  · simp [processUpdate.reachability]
  intro aliceStHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (sendUpdate.reachability) _ ("Alice", aliceSkHandle, aliceStHandle)
  · assumption
  · simp [sendUpdate.reachability]
  intro ⟨ aliceStHandle, msgHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (processUpdate.reachability) _ ("Bob", aliceVkHandle, bobStHandle, msgHandle)
  · assumption
  · simp [processUpdate.reachability]
  intro aliceStHandle tr h_post h_tr h_le

  apply honestAttackerLoop_PreservesReachability
  · assumption
  grind

-- Future work: we could design a step-like tactic to automate this proof
theorem honestAttacker_PreservesReachability
  : honestAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honestAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "Ratchet PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, aliceVkHandle, aliceSkHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "Ratchet PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, bobVkHandle, bobSkHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (initiate.reachability) _ ("Alice", "Bob", aliceSkHandle)
  · assumption
  · simp [initiate.reachability]
  intro ⟨ aliceStHandle, msgHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (processInitiate.reachability) _ ("Bob", "Alice", aliceVkHandle, msgHandle)
  · assumption
  · simp [processInitiate.reachability]
  intro bobStHandle tr h_post h_tr h_le

  apply honestAttackerLoop_PreservesReachability
  · assumption
  grind

public
theorem honestAttacker_properties:
  let tr := (honestAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 t2 transcript k,
    transcript.length = 21 ∧
    t1 < t2 ∧
    tr.EventLoggedAt (RatchetEvent.SendUpdate "Alice" "Bob" transcript k) t1 ∧
    tr.EventLoggedAt (RatchetEvent.ReceiveUpdate "Bob" "Alice" transcript k) t2
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable honestAttacker_PreservesReachability
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt RatchetEvent 153 tr) with
    | some (RatchetEvent.ReceiveUpdate _ _ transcript k) => (transcript, k)
    | _ => ([], Comparse.BytesLike.empty)
  refine ⟨ 150, 153, witness.fst, witness.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.Ratchet.honestAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 honestAttacker_properties._native.native_decide.ax_1_6]
-/
#guard_msgs in
#print axioms honestAttacker_properties

public
def compromiseStateMyTurnAttacker: Traceful Unit := do
  honestAttacker
  let stHandle := 154

  let compromiseHandle ← StateMyTurn.compromise stHandle
  let globalStBytes ← Network.receiveMessage compromiseHandle
  let globalSt: PersistentLocalState.LocalState StateMyTurn ← Comparse.parse globalStBytes
  let st: StateMyTurn := globalSt.state
  let _ ← Network.sendMessage st.k

#guard (compromiseStateMyTurnAttacker.run Trace.nil).fst = some ()

-- Future work: we could design a step-like tactic to automate this proof
theorem compromiseStateMyTurnAttacker_PreservesReachability
  : compromiseStateMyTurnAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromiseStateMyTurnAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply honestAttacker_PreservesReachability
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (StateMyTurn.compromise.reachability)
  · assumption
  · simp [StateMyTurn.compromise.reachability]
  intro compromiseHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro globalStBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro globalSt tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem compromiseStateMyTurnAttacker_properties:
  let tr := (compromiseStateMyTurnAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t transcript k,
    transcript.length = 21 ∧
    tr.EventLoggedAt (RatchetEvent.ReceiveUpdate "Bob" "Alice" transcript k) t ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromiseStateMyTurnAttacker_PreservesReachability
    grind
  suffices
    ∃ t t2 transcript k,
      transcript.length = 21 ∧
      tr.EventLoggedAt (RatchetEvent.ReceiveUpdate "Bob" "Alice" transcript k) t ∧
      tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt RatchetEvent 153 tr) with
    | some (RatchetEvent.ReceiveUpdate _ _ transcript k) => (transcript, k)
    | _ => ([], Comparse.BytesLike.empty)
  refine ⟨ 153, 157, witness.fst, witness.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.Ratchet.compromiseStateMyTurnAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromiseStateMyTurnAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms compromiseStateMyTurnAttacker_properties

public
def compromiseStateOtherTurnAttacker: Traceful Unit := do
  honestAttacker
  let stHandle := 151

  let compromiseHandle ← StateOtherTurn.compromise stHandle
  let globalStBytes ← Network.receiveMessage compromiseHandle
  let globalSt: PersistentLocalState.LocalState StateOtherTurn ← Comparse.parse globalStBytes
  let st := globalSt.state
  let _ ← Network.sendMessage st.k

#guard (compromiseStateOtherTurnAttacker.run Trace.nil).fst = some ()

-- Future work: we could design a step-like tactic to automate this proof
theorem compromiseStateOtherTurnAttacker_PreservesReachability
  : compromiseStateOtherTurnAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromiseStateOtherTurnAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply honestAttacker_PreservesReachability
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (StateOtherTurn.compromise.reachability)
  · assumption
  · simp [StateOtherTurn.compromise.reachability]
  intro compromiseHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro globalStBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro globalSt tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem compromiseStateOtherTurnAttacker_properties:
  let tr := (compromiseStateOtherTurnAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t transcript k,
    transcript.length = 21 ∧
    tr.EventLoggedAt (RatchetEvent.ReceiveUpdate "Bob" "Alice" transcript k) t ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromiseStateOtherTurnAttacker_PreservesReachability
    grind
  suffices
    ∃ t t2 transcript k,
      transcript.length = 21 ∧
      tr.EventLoggedAt (RatchetEvent.ReceiveUpdate "Bob" "Alice" transcript k) t ∧
      tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt RatchetEvent 153 tr) with
    | some (RatchetEvent.ReceiveUpdate _ _ transcript k) => (transcript, k)
    | _ => ([], Comparse.BytesLike.empty)
  refine ⟨ 153, 157, witness.fst, witness.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.Ratchet.compromiseStateOtherTurnAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromiseStateOtherTurnAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms compromiseStateOtherTurnAttacker_properties

def compromiseSigKeyAttackerLoop (n: Nat) (aliceVkHandle aliceSkHandle bobVkHandle aliceStHandle: Nat) (bobSigKey aliceDhPk transcriptHash k: Bytes): Traceful Unit := do
  if n = 0 then return () else

  let bobDhSk := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let bobDhPk := DiffieHellman.dhPk bobDhSk

  let transcriptElement: TranscriptElement := { recipient := "Alice", dhPk := bobDhPk }
  let transcriptHash := computeTranscriptHash transcriptHash transcriptElement

  let sigNonce := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let sig := Signature.sign bobSigKey sigNonce (Comparse.serialize ({transcriptHash}: SigInput))

  let dhss := DiffieHellman.dh aliceDhPk bobDhSk
  let k := KdfExpand.kdfExpand (KdfExtract.kdfExtract dhss k) transcriptHash 32
  let msgHandle ← Network.sendMessage (Comparse.serialize ({ dhPk := bobDhPk, sig } : Message)) -- 1
  let _ ← Network.sendMessage k

  let aliceStHandle ← processUpdate "Alice" bobVkHandle aliceStHandle msgHandle
  let (aliceStHandle, msgHandle) ← sendUpdate "Alice" aliceSkHandle aliceStHandle

  let msgBytes ← Network.receiveMessage msgHandle
  let msg: Message ← Comparse.parse msgBytes

  let transcriptElement: TranscriptElement := { recipient := "Bob", dhPk := msg.dhPk }
  let transcriptHash := computeTranscriptHash transcriptHash transcriptElement

  let dhss := DiffieHellman.dh msg.dhPk bobDhSk
  let k := KdfExpand.kdfExpand (KdfExtract.kdfExtract dhss k) transcriptHash 32

  let _ ← Network.sendMessage k

  compromiseSigKeyAttackerLoop (n-1) aliceVkHandle aliceSkHandle bobVkHandle aliceStHandle bobSigKey msg.dhPk transcriptHash k

public
def compromiseSigKeyAttacker: Traceful Unit := do
  let (_, aliceVkHandle, aliceSkHandle) ← LongTermKeys.generateKeyPair "Ratchet PKI" "Alice" -- 4
  let (_, bobVkHandle, bobSkHandle) ← LongTermKeys.generateKeyPair "Ratchet PKI" "Bob" -- 4

  let (aliceStHandle, msgHandle) ← initiate "Alice" "Bob" aliceSkHandle
  let _ ← processInitiate "Bob" "Alice" aliceVkHandle msgHandle

  let compromiseHandle ← LongTermKeys.compromisePrivateKey "Ratchet PKI" bobSkHandle -- 2
  let globalStSigkeyBytes ← Network.receiveMessage compromiseHandle
  let globalStSigkey: PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "Ratchet PKI") ← Comparse.parse globalStSigkeyBytes
  let bobSigKey := globalStSigkey.state.sk

  let msgBytes ← Network.receiveMessage msgHandle
  let msg: Message ← Comparse.parse msgBytes

  let transcriptElement: TranscriptElement := { recipient := "Bob", dhPk := msg.dhPk }
  let transcriptHash := computeTranscriptHash initialTranscriptHash transcriptElement

  compromiseSigKeyAttackerLoop 10 aliceVkHandle aliceSkHandle bobVkHandle aliceStHandle bobSigKey msg.dhPk transcriptHash firstKey

#guard (compromiseSigKeyAttacker.run Trace.nil).fst = some ()

-- Future work: we could design a step-like tactic to automate this proof
theorem compromiseSigKeyAttackerLoop_PreservesReachability
  (n: Nat)
  (aliceVkHandle aliceSkHandle bobVkHandle aliceStHandle: Nat)
  (bobSigKey aliceDhPk transcriptHash k: Bytes)
  : (compromiseSigKeyAttackerLoop n aliceVkHandle aliceSkHandle bobVkHandle aliceStHandle bobSigKey aliceDhPk transcriptHash k).PreservesReachability reachability (fun tr => bobSigKey.AttackerKnows tr ∧ aliceDhPk.AttackerKnows tr ∧ transcriptHash.AttackerKnows tr ∧ k.AttackerKnows tr) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  unfold compromiseSigKeyAttackerLoop
  split
  · apply Traceful.PreservesReachabilityFrom_pure
    · assumption
    grind

  lift_lets
  intro bobDhSk
  have: bobDhSk.AttackerKnows tr := by apply Literal.attacker_knows_literalToBytes
  intro bobDhPk
  have: bobDhPk.AttackerKnows tr := by apply DiffieHellman.attacker_knows_dhPk; grind
  intro transcriptElement
  intro transcriptHash
  have: transcriptHash.AttackerKnows tr := by
    subst transcriptHash
    unfold computeTranscriptHash
    apply Hash.attacker_knows_hash
    grind
  intro sig
  have: sig.AttackerKnows tr := by apply Signature.attacker_knows_sign <;> grind
  intro dhss
  have: dhss.AttackerKnows tr := by apply DiffieHellman.attacker_knows_dh <;> grind
  intro k
  have: k.AttackerKnows tr := by
    apply KdfExpand.attacker_knows_kdfExpand
    · apply KdfExtract.attacker_knows_kdfExtract <;> grind
    grind

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · grind
  intro msgHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (processUpdate.reachability) _ ("Alice", bobVkHandle, aliceStHandle, msgHandle)
  · assumption
  · simp [processUpdate.reachability]
  intro aliceStHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (sendUpdate.reachability) _ ("Alice", aliceSkHandle, aliceStHandle)
  · assumption
  · simp [sendUpdate.reachability]
  intro ⟨ aliceStHandle, msgHandle ⟩ tr h_post h_tr h_le
  dsimp (zeta := false) only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro msgBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro msg tr h_post h_tr h_le

  lift_lets
  intro transcriptElement
  intro transcriptHash
  have: transcriptHash.AttackerKnows tr := by
    subst transcriptHash
    unfold computeTranscriptHash
    apply Hash.attacker_knows_hash
    grind (ematch := 10)
  intro dhss
  have: dhss.AttackerKnows tr := by apply DiffieHellman.attacker_knows_dh <;> grind (ematch := 10)
  intro k
  have: k.AttackerKnows tr := by
    apply KdfExpand.attacker_knows_kdfExpand
    · apply KdfExtract.attacker_knows_kdfExtract <;> grind (ematch := 10)
    grind

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply compromiseSigKeyAttackerLoop_PreservesReachability
  · assumption
  grind (ematch := 10)

-- Future work: we could design a step-like tactic to automate this proof
theorem compromiseSigKeyAttacker_PreservesReachability
  : compromiseSigKeyAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromiseSigKeyAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "Ratchet PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, aliceVkHandle, aliceSkHandle ⟩ tr h_post h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "Ratchet PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, bobVkHandle, bobSkHandle ⟩ tr h_post h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (initiate.reachability) _ ("Alice", "Bob", aliceSkHandle)
  · assumption
  · simp [initiate.reachability]
  intro ⟨ aliceStHandle, msgHandle ⟩ tr h_post h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (processInitiate.reachability) _ ("Bob", "Alice", aliceVkHandle, msgHandle)
  · assumption
  · simp [processInitiate.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.compromisePrivateKey.reachability "Ratchet PKI")
  · assumption
  · simp [LongTermKeys.compromisePrivateKey.reachability]
  intro compromiseHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro globalStSigkeyBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro globalStSigkey tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro msgBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro msg tr h_post h_tr h_le

  apply compromiseSigKeyAttackerLoop_PreservesReachability
  · assumption
  repeat' apply And.intro
  · grind (ematch := 10)
  · grind (ematch := 10)
  · unfold computeTranscriptHash
    apply Hash.attacker_knows_hash
    have: initialTranscriptHash.AttackerKnows tr := by
      unfold initialTranscriptHash
      simp only [Comparse.BytesLike.empty]
      apply Literal.attacker_knows_literalToBytes
    grind
  · unfold firstKey
    apply Literal.attacker_knows_literalToBytes

public
theorem compromiseSigKeyAttacker_properties:
  let tr := (compromiseSigKeyAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t transcript k,
    transcript.length = 21 ∧
    tr.EventLoggedAt (RatchetEvent.SendUpdate "Alice" "Bob" transcript k) t ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromiseSigKeyAttacker_PreservesReachability
    grind
  suffices
    ∃ t t2 transcript k,
      transcript.length = 21 ∧
      tr.EventLoggedAt (RatchetEvent.SendUpdate "Alice" "Bob" transcript k) t ∧
      tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt RatchetEvent 113 tr) with
    | some (RatchetEvent.SendUpdate _ _ transcript k) => (transcript, k)
    | _ => ([], Comparse.BytesLike.empty)
  refine ⟨ 113, 116, witness.fst, witness.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.Ratchet.compromiseSigKeyAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromiseSigKeyAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms compromiseSigKeyAttacker_properties

end DY.Example.Ratchet
