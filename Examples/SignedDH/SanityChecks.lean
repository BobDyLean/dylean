module

import DY.Meta
import DY.Meta.Utils
import Examples.SignedDH.Specification
import Examples.SignedDH.Instance
public meta import Examples.SignedDH.Instance

namespace DY.Example.SignedDH

-- TODO: move, but where?
theorem liftM_parse_preserves_reachability
  {a: Type} [Comparse.ParseableSerializeable a]
  (config: ReachabilityConfig)
  (buf: Bytes)
  : (liftM (Comparse.parse buf): Traceful a).PreservesReachability config (fun _ => True) (fun res _ => Comparse.FormatRel buf res)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
  grind

public
def honestAttacker: Traceful Unit := do
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "SignedDH PKI" "Bob" -- 4
  let (stClientHandle, msgClientHandle) ← Client.initiate "Alice" -- 4
  let (_stServerHandle, msgServerHandle) ← Server.receive "Bob" skHandle msgClientHandle -- 5
  let _ ← Client.finish "Alice" "Bob" pkHandle msgServerHandle stClientHandle -- 2

#guard (honestAttacker.run Trace.nil).fst = some ()

theorem honestAttacker_PreservesReachability
  : honestAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honestAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "SignedDH PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, tsPk, tsSk ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.initiate.reachability)
  · assumption
  · simp [Client.initiate.reachability]
  intro ⟨ tsClientSt, tsMsgClient ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Server.receive.reachability) _ ("Bob", tsSk, tsMsgClient)
  · assumption
  · simp [Server.receive.reachability]
  intro ⟨ _, tsMsgServer ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.finish.reachability) _ ("Alice", "Bob", tsPk, tsMsgServer, tsClientSt)
  · assumption
  · simp [Client.finish.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem honestAttacker_properties:
  let tr := (honestAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 t2 xPk yPk k,
    t1 < t2 ∧
    tr.EventLoggedAt (SignedDHEvent.ServerFinishEvent "Bob" xPk yPk k) t1 ∧
    tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent "Alice" "Bob" xPk yPk k) t2
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable honestAttacker_PreservesReachability
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt SignedDHEvent 10 tr) with
    | some (SignedDHEvent.ServerFinishEvent _ xPk yPk k) => (xPk, yPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  refine ⟨ 10, 13, witness.fst, witness.snd.fst, witness.snd.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SignedDH.honestAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 honestAttacker_properties._native.native_decide.ax_1_6]
-/
#guard_msgs in
#print axioms honestAttacker_properties

public
def compromiseClientEphAttacker: Traceful Unit := do
  honestAttacker
  let stClientHandle := 6
  let msgServerHandle := 12

  let compromiseHandle ← ClientInitiateState.compromise stClientHandle
  let globalStClientBytes ← Network.receiveMessage compromiseHandle
  let globalStClient: PersistentLocalState.LocalState ClientInitiateState ← Comparse.parse globalStClientBytes
  let stClient: ClientInitiateState := globalStClient.state

  let msgServerBytes ← Network.receiveMessage msgServerHandle
  let msgServer: ServerMessage ← Comparse.parse msgServerBytes

  let k := Hash.hash (DiffieHellman.dh msgServer.yPk stClient.xSk)
  let _ ← Network.sendMessage k
  return ()

#guard (compromiseClientEphAttacker.run Trace.nil).fst = some ()

theorem compromiseClientEphAttacker_PreservesReachability
  : compromiseClientEphAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromiseClientEphAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply honestAttacker_PreservesReachability
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (ClientInitiateState.compromise.reachability)
  · assumption
  · simp [ClientInitiateState.compromise.reachability]
  intro compromiseHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro globalStClientBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro globalStClient tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro msgServerBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro msgServer tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · dsimp only
    apply Hash.attacker_knows_hash
    apply DiffieHellman.attacker_knows_dh
    · grind
    · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem compromiseClientEphAttacker_properties:
  let tr := (compromiseClientEphAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 xPk yPk k,
    tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent "Alice" "Bob" xPk yPk k) t1 ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromiseClientEphAttacker_PreservesReachability
    grind
  suffices
      ∃ t1 t2 xPk yPk k,
        tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent "Alice" "Bob" xPk yPk k) t1 ∧
        tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt SignedDHEvent 13 tr) with
    | some (SignedDHEvent.ClientFinishEvent _ _ xPk yPk k) => (xPk, yPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  refine ⟨ 13, 17, witness.fst, witness.snd.fst, witness.snd.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SignedDH.compromiseClientEphAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromiseClientEphAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms compromiseClientEphAttacker_properties

public
def compromiseSigKeyAttacker: Traceful Unit := do
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "SignedDH PKI" "Bob" -- 4
  let compromiseHandle ← LongTermKeys.compromisePrivateKey "SignedDH PKI" skHandle -- 2
  let globalStSigkeyBytes ← Network.receiveMessage compromiseHandle
  let globalStSigkey: PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "SignedDH PKI") ← Comparse.parse globalStSigkeyBytes
  let sigKey := globalStSigkey.state.sk

  let (stClientHandle, msgClientHandle) ← Client.initiate "Alice" -- 4

  let msgClientBytes ← Network.receiveMessage msgClientHandle
  let msgClient: ClientMessage ← Comparse.parse msgClientBytes
  let xPk := msgClient.xPk

  let ySk := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let yPk := DiffieHellman.dh_pk ySk
  let k := Hash.hash (DiffieHellman.dh xPk ySk)
  let sigNonce := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let sig := Signature.sign sigKey sigNonce (Comparse.serialize ({xPk, yPk}: SigInput))
  let msgServerHandle ← Network.sendMessage (Comparse.serialize ({ yPk, sig } : ServerMessage)) -- 1
  let _ ← Client.finish "Alice" "Bob" pkHandle msgServerHandle stClientHandle -- 2
  let _ ← Network.sendMessage k -- 1
  return ()

#guard (compromiseSigKeyAttacker.run Trace.nil).fst = some ()

theorem compromiseSigKeyAttacker_PreservesReachability
  : compromiseSigKeyAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromiseSigKeyAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "SignedDH PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.compromisePrivateKey.reachability "SignedDH PKI")
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

  dsimp
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.initiate.reachability)
  · assumption
  · simp [Client.initiate.reachability]
  intro ⟨ stClientHandle, msgClientHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro msgClientBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro msgClient tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp only [Comparse.AttackerKnows_serialize, ServerMessage.IsWellFormed_eq]
    apply And.intro
    · apply DiffieHellman.attacker_knows_dh_pk
      apply Literal.attacker_knows_literalToBytes
    apply Signature.attacker_knows_sign
    · grind (ematch := 10)
    · apply Literal.attacker_knows_literalToBytes
    · simp only [Comparse.AttackerKnows_serialize, SigInput.IsWellFormed_eq]
      apply And.intro
      · grind
      · apply DiffieHellman.attacker_knows_dh_pk
        apply Literal.attacker_knows_literalToBytes
  intro msgServerHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.finish.reachability) _ ("Alice", "Bob", pkHandle, msgServerHandle, stClientHandle)
  · assumption
  · simp [Client.finish.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · dsimp only
    apply Hash.attacker_knows_hash
    apply DiffieHellman.attacker_knows_dh
    · grind
    · apply Literal.attacker_knows_literalToBytes
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem compromiseSigKeyAttacker_properties:
  let tr := (compromiseSigKeyAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 xPk yPk k,
    tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent "Alice" "Bob" xPk yPk k) t1 ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromiseSigKeyAttacker_PreservesReachability
    grind
  suffices
    ∃ t1 t2 xPk yPk k,
      tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent "Alice" "Bob" xPk yPk k) t1 ∧
      tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt SignedDHEvent 11 tr) with
    | some (SignedDHEvent.ClientFinishEvent _ _ xPk yPk k) => (xPk, yPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  refine ⟨ 11, 13, witness.fst, witness.snd.fst, witness.snd.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SignedDH.compromiseSigKeyAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromiseSigKeyAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms compromiseSigKeyAttacker_properties

end DY.Example.SignedDH
