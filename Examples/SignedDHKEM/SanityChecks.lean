module

import DY.Meta
import DY.Meta.Utils
import Examples.SignedDHKEM.Specification
import Examples.SignedDHKEM.Instance
public meta import Examples.SignedDHKEM.Instance

namespace DY.Example.SignedDHKEM

-- TODO: move, but where?
theorem liftM_parse_preserves_reachability
  {a: Type} [Comparse.ParseableSerializeable a]
  (config: ReachabilityConfig)
  (buf: Bytes)
  : (liftM (Comparse.parse buf): Traceful a).PreservesReachability config (fun _ => True) (fun res _ => Comparse.FormatRel buf res)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
  grind

theorem liftM_kemDecap_preserves_reachability
  (config: ReachabilityConfig)
  (sk cipher: Bytes)
  : (liftM (KEM.kemDecap sk cipher): Traceful Bytes).PreservesReachability config (fun tr => sk.AttackerKnows tr ∧ cipher.AttackerKnows tr) (fun res tr => res.AttackerKnows tr)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
  intro tr h_reach h_pre
  apply And.intro
  · grind
  have := KEM.kemDecap.attacker_knows sk cipher tr (by grind) (by grind)
  grind

public
def honestAttacker: Traceful Unit := do
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "SignedDHKEM PKI" "Bob" -- 4
  let (dhStClientHandle, kemStClientHandle, msgClientHandle) ← Client.initiate "Alice" -- 6
  let (_stServerHandle, msgServerHandle) ← Server.receive "Bob" skHandle msgClientHandle -- 6
  let _ ← Client.finish "Alice" "Bob" pkHandle msgServerHandle dhStClientHandle kemStClientHandle -- 2

#guard (honestAttacker.run Trace.nil).fst = some ()

theorem honestAttacker_PreservesReachability
  : honestAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honestAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "SignedDHKEM PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, tsPk, tsSk ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.initiate.reachability)
  · assumption
  · simp [Client.initiate.reachability]
  intro ⟨ dhStClientHandle, kemStClientHandle, msgClientHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Server.receive.reachability) _ ("Bob", tsSk, msgClientHandle)
  · assumption
  · simp [Server.receive.reachability]
  intro ⟨ _, tsMsgServer ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.finish.reachability) _ ("Alice", "Bob", tsPk, tsMsgServer, dhStClientHandle, kemStClientHandle)
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
  ∃ t1 t2 xPk yPk zPk k,
    t1 < t2 ∧
    tr.EventLoggedAt (SignedDHKEMEvent.ServerFinishEvent "Bob" xPk yPk zPk k) t1 ∧
    tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent "Alice" "Bob" xPk yPk zPk k) t2
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable honestAttacker_PreservesReachability
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt SignedDHKEMEvent 13 tr) with
    | some (SignedDHKEMEvent.ServerFinishEvent _ xPk yPk zPk k) => (xPk, yPk, zPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  refine ⟨ 13, 16, witness.fst, witness.snd.fst, witness.snd.snd.fst, witness.snd.snd.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SignedDHKEM.honestAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 honestAttacker_properties._native.native_decide.ax_1_6]
-/
#guard_msgs in
#print axioms honestAttacker_properties

public
def breakDhAndKemAttacker: Traceful Unit := do
  honestAttacker
  let msgClientHandle := 9
  let msgServerHandle := 15

  let msgClientBytes ← Network.receiveMessage msgClientHandle
  let msgClient: ClientMessage ← Comparse.parse msgClientBytes
  let msgServerBytes ← Network.receiveMessage msgServerHandle
  let msgServer: ServerMessage ← Comparse.parse msgServerBytes

  let xPkHandle ← Network.sendMessage msgClient.xPk
  let xSkHandle ← DiffieHellman'.Broken.breakDhPk xPkHandle
  let xSk ← Network.receiveMessage xSkHandle

  let zPkHandle ← Network.sendMessage msgClient.zPk
  let zSkHandle ← KEM.Broken.breakKemPk zPkHandle
  let zSk ← Network.receiveMessage zSkHandle

  let dhss := DiffieHellman'.dh msgServer.yPk xSk
  let kemss ← KEM.kemDecap zSk msgServer.ct
  let k := Hash.hash (Concat.concat dhss kemss)
  let _ ← Network.sendMessage k
  return ()

#guard (breakDhAndKemAttacker.run Trace.nil).fst = some ()

theorem breakDhAndKemAttacker_PreservesReachability
  : breakDhAndKemAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [breakDhAndKemAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply honestAttacker_PreservesReachability
  · assumption
  · grind
  intro _ tr h_post h_tr h_le

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
  · grind
  intro xPkHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (DiffieHellman'.Broken.breakDhPk.reachability)
  · assumption
  · simp [DiffieHellman'.Broken.breakDhPk.reachability]
  intro xSkHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro xSk tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · grind
  intro zPkHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (KEM.Broken.breakKemPk.reachability)
  · assumption
  · simp [KEM.Broken.breakKemPk.reachability]
  intro zSkHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro zSk tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_kemDecap_preserves_reachability
  · assumption
  · apply And.intro
    · grind
    · grind (gen := 50)
  intro kemss tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · dsimp only
    apply Hash.attacker_knows_hash
    apply Concat.attacker_knows_concat
    · apply DiffieHellman'.attacker_knows_dh
      · grind (gen := 50)
      · grind
    · grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem breakDhAndKemAttacker_properties:
  let tr := (breakDhAndKemAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 xPk yPk zPk k,
    tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent "Alice" "Bob" xPk yPk zPk k) t1 ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable breakDhAndKemAttacker_PreservesReachability
    grind
  suffices
      ∃ t1 t2 xPk yPk zPk k,
        tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent "Alice" "Bob" xPk yPk zPk k) t1 ∧
        tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt SignedDHKEMEvent 16 tr) with
    | some (SignedDHKEMEvent.ClientFinishEvent _ _ xPk yPk zPk k) => (xPk, yPk, zPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  refine ⟨ 16, 24, witness.fst, witness.snd.fst, witness.snd.snd.fst, witness.snd.snd.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SignedDHKEM.breakDhAndKemAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 breakDhAndKemAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms breakDhAndKemAttacker_properties


public
def breakSigKeyAttacker: Traceful Unit := do
  let (serverVkHandle, pkHandle, _skHandle) ← LongTermKeys.generateKeyPair "SignedDHKEM PKI" "Bob" -- 4
  let serverSkHandle ← Signature'.Broken.breakVk serverVkHandle -- 2
  let sigKey ← Network.receiveMessage serverSkHandle

  let (dhStClientHandle, kemStClientHandle, msgClientHandle) ← Client.initiate "Alice" -- 6

  let msgClientBytes ← Network.receiveMessage msgClientHandle
  let msgClient: ClientMessage ← Comparse.parse msgClientBytes
  let xPk := msgClient.xPk
  let zPk := msgClient.zPk

  let ySk := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let yPk := DiffieHellman'.dh_pk ySk
  let dhss := DiffieHellman'.dh xPk ySk
  let entropy := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let (ct, kemss) := KEM.kemEncap zPk entropy
  let k := Hash.hash (Concat.concat dhss kemss)

  let sigNonce := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let sig := Signature'.sign sigKey sigNonce (Comparse.serialize ({xPk, yPk, zPk, ct}: SigInput))
  let msgServerHandle ← Network.sendMessage (Comparse.serialize ({ yPk, ct, sig } : ServerMessage)) -- 1
  let _ ← Client.finish "Alice" "Bob" pkHandle msgServerHandle dhStClientHandle kemStClientHandle -- 2
  let _ ← Network.sendMessage k -- 1
  return ()

#guard (breakSigKeyAttacker.run Trace.nil).fst = some ()

theorem breakSigKeyAttacker_PreservesReachability
  : breakSigKeyAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [breakSigKeyAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "SignedDHKEM PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Signature'.Broken.breakVk.reachability)
  · assumption
  · simp [Signature'.Broken.breakVk.reachability]
  intro serverSkHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro sigKey tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.initiate.reachability)
  · assumption
  · simp [Client.initiate.reachability]
  intro ⟨ dhStClientHandle, kemStClientHandle, msgClientHandle ⟩ tr h_post h_tr h_le

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
    · apply DiffieHellman'.attacker_knows_dh_pk
      apply Literal.attacker_knows_literalToBytes
    apply And.intro
    · have := KEM.kemEncap.attacker_knows
      have := Literal.attacker_knows_literalToBytes
      grind
    apply Signature'.attacker_knows_sign
    · grind
    · apply Literal.attacker_knows_literalToBytes
    · simp only [Comparse.AttackerKnows_serialize, SigInput.IsWellFormed_eq]
      apply And.intro
      · grind
      apply And.intro
      · apply DiffieHellman'.attacker_knows_dh_pk
        apply Literal.attacker_knows_literalToBytes
      apply And.intro
      · grind
      have := KEM.kemEncap.attacker_knows
      have := Literal.attacker_knows_literalToBytes
      grind
  intro msgServerHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.finish.reachability) _ ("Alice", "Bob", pkHandle, msgServerHandle, dhStClientHandle, kemStClientHandle)
  · assumption
  · simp [Client.finish.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · dsimp only
    apply Hash.attacker_knows_hash
    apply Concat.attacker_knows_concat
    · apply DiffieHellman'.attacker_knows_dh
      · grind
      · apply Literal.attacker_knows_literalToBytes
    · have: msgClient.zPk.AttackerKnows tr := by grind
      have := KEM.kemEncap.attacker_knows
      have := Literal.attacker_knows_literalToBytes
      grind
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem breakSigKeyAttacker_properties:
  let tr := (breakSigKeyAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 xPk yPk zPk k,
    tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent "Alice" "Bob" xPk yPk zPk k) t1 ∧
    k.AttackerKnows tr
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable breakSigKeyAttacker_PreservesReachability
    grind
  suffices
    ∃ t1 t2 xPk yPk zPk k,
      tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent "Alice" "Bob" xPk yPk zPk k) t1 ∧
      tr.MessageSentAt k t2
  by
    have := Trace.MessageSentAt_implies_AttackerKnows
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  simp only [DY.Trace.MessageSentAt_eq_getMessageSentAt]
  let witness :=
    match (Trace.getEventAt SignedDHKEMEvent 13 tr) with
    | some (SignedDHKEMEvent.ClientFinishEvent _ _ xPk yPk zPk k) => (xPk, yPk, zPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  refine ⟨ 13, 15, witness.fst, witness.snd.fst, witness.snd.snd.fst, witness.snd.snd.snd, ?_ ⟩
  native_decide

/--
info: 'DY.Example.SignedDHKEM.breakSigKeyAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 breakSigKeyAttacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms breakSigKeyAttacker_properties

end DY.Example.SignedDHKEM
