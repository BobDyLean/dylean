module

import DY.Meta
import DY.Meta.Utils
public import Examples.MerkleTree.Specification
public import Examples.MerkleTree.Proof
import all Examples.MerkleTree.Proof
public import Examples.MerkleTree.Instance
public meta import Examples.MerkleTree.Instance

namespace DY.Example.MerkleTree

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
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "MerkleTree PKI" "Bob" -- 4
  let msgHandle0 ← Network.sendMessage (Literal.literalToBytes "foo 0".toByteArray) -- 1
  let msgHandle1 ← Network.sendMessage (Literal.literalToBytes "bar 1".toByteArray) -- 1
  let msgHandle2 ← Network.sendMessage (Literal.literalToBytes "baz 2".toByteArray) -- 1
  let msgHandle3 ← Network.sendMessage (Literal.literalToBytes "qux 3".toByteArray) -- 1
  let msgHandle4 ← Network.sendMessage (Literal.literalToBytes "quux 4".toByteArray) -- 1
  let (msgSigHandle, stHandle) ← Server.authenticate "Bob" [msgHandle0, msgHandle1, msgHandle2, msgHandle3, msgHandle4] skHandle -- 8
  let msgInclHandle ← Server.proveInclusion "Bob" 3 stHandle -- 1
  Client.checkInclusion "Bob" msgSigHandle msgInclHandle pkHandle -- 1
  return ()

theorem honestAttacker_PreservesReachability
  : honestAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honestAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "MerkleTree PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_post h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle1 tr h_post h_tr tr_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle2 tr h_post h_tr tr_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle3 tr h_post h_tr tr_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle4 tr h_post h_tr tr_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle5 tr h_post h_tr tr_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Server.authenticate.reachability) _ ("Bob", [msgHandle1, msgHandle2, msgHandle3, msgHandle4, msgHandle5], skHandle)
  · assumption
  · simp [Server.authenticate.reachability]
  intro ⟨ msgSigHandle, stHandle ⟩ tr h_post h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Server.proveInclusion.reachability) _ ("Bob", 3, stHandle)
  · assumption
  · simp [Server.proveInclusion.reachability]
  intro msgInclHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.checkInclusion.reachability) _ ("Bob", msgSigHandle, msgInclHandle, pkHandle)
  · assumption
  · simp [Client.checkInclusion.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem honestAttacker_properties:
  let tr := (honestAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ (t1 t2: Nat) (msg: Bytes),
    t1 < t2 ∧
    tr.EventLoggedAt (TheEvent.ServerAuthenticated "Bob" msg) t1 ∧
    tr.EventLoggedAt (TheEvent.ClientAccept "Bob" msg) t2
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable honestAttacker_PreservesReachability
    grind
  refine ⟨ 12, 18, (Literal.literalToBytes "qux 3".toByteArray), ?_ ⟩
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  native_decide

/--
info: 'DY.Example.MerkleTree.honestAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 honestAttacker_properties._native.native_decide.ax_1_2]
-/
#guard_msgs in
#print axioms honestAttacker_properties

public
def compromiseSigKeyAttacker: Traceful Unit := do
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "MerkleTree PKI" "Bob" -- 4

  let compromiseHandle ← LongTermKeys.compromisePrivateKey "MerkleTree PKI" skHandle -- 2
  let globalStSigkeyBytes ← Network.receiveMessage compromiseHandle
  let globalStSigkey: PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "SignedDH PKI") ← Comparse.parse globalStSigkeyBytes
  let sigKey := globalStSigkey.state.sk


  let msg0 := (Literal.literalToBytes "foo 0".toByteArray)
  let msg1 := (Literal.literalToBytes "bar 1".toByteArray)
  let msg2 := (Literal.literalToBytes "baz 2".toByteArray)
  let msg3 := (Literal.literalToBytes "qux 3".toByteArray)
  let msg4 := (Literal.literalToBytes "quux 4".toByteArray)
  let elements := [msg0, msg1, msg2, msg3, msg4, msg4]

  let rootHash := merkleTreeHash (.bytes) elements
  let tbs: SignedRootHashTBS := { rootHash, length := elements.length }
  let tbsBytes: Bytes := Comparse.serialize tbs
  let sigNonce := Literal.literalToBytes "00000000000000000000000000000000".toByteArray
  let sig := Signature.sign sigKey sigNonce tbsBytes

  let msgSig: SignedRootHash := { tbs, sig }
  let msgSigHandle ← Network.sendMessage (Comparse.serialize msgSig)

  let msgIncl: ElementAndInclusionProof := {
    element := elements[4]
    i := 4
    inclusionProof := mkInclusionProof (.bytes) elements 4 (by grind)
  }
  let msgInclHandle ← Network.sendMessage (Comparse.serialize msgIncl)

  Client.checkInclusion "Bob" msgSigHandle msgInclHandle pkHandle -- 1
  return ()

#guard (compromiseSigKeyAttacker.run Trace.nil).fst = some ()

theorem compromiseSigKeyAttacker_PreservesReachability
  : compromiseSigKeyAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [compromiseSigKeyAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "MerkleTree PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.compromisePrivateKey.reachability "MerkleTree PKI")
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
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp only [Comparse.AttackerKnows_serialize, SignedRootHash.IsWellFormed_eq]
    apply And.intro
    · simp only [SignedRootHashTBS.IsWellFormed_eq]
      apply pred_merkleTreeHash _ _ (Bytes.AttackerKnows · tr)
      · intro b h_b
        apply Hash.attacker_knows_hash
        grind
      simp [Literal.attacker_knows_literalToBytes]
    apply Signature.attacker_knows_sign
    · grind
    · apply Literal.attacker_knows_literalToBytes
    · simp only [Comparse.AttackerKnows_serialize, SignedRootHashTBS.IsWellFormed_eq]
      apply pred_merkleTreeHash _ _ (Bytes.AttackerKnows · tr)
      · intro b h_b
        apply Hash.attacker_knows_hash
        grind
      simp [Literal.attacker_knows_literalToBytes]
  intro msgSigHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp only [Comparse.AttackerKnows_serialize, ElementAndInclusionProof.IsWellFormed_eq]
    apply And.intro
    · simp [Literal.attacker_knows_literalToBytes]
    apply pred_mkInclusionProof _ _ _ _ (Bytes.AttackerKnows · tr)
    · intro b h_b
      apply Hash.attacker_knows_hash
      grind
    simp [Literal.attacker_knows_literalToBytes]
  intro msgInclHandle tr h_post h_tr h_le

  dsimp
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Client.checkInclusion.reachability) _ ("Bob", msgSigHandle, msgInclHandle, pkHandle)
  · assumption
  · simp [Client.checkInclusion.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

theorem rewrite_forall_nat_into_forall_fin {P: Nat → Prop} (n: Nat) (h: ∀ i, n ≤ i → P i): (∀ i: Nat, P i) = (∀ i: Fin n, P i.val) := by
  simp only [eq_iff_iff]
  constructor
  · grind
  · intro h i
    by_cases n ≤ i
    · grind
    · exact h ⟨ i, by grind ⟩

public
theorem compromiseSigKeyAttacker_properties:
  let tr := (compromiseSigKeyAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 element,
    tr.EventLoggedAt (TheEvent.ClientAccept "Bob" element) t1 ∧
    (∀ t2, ¬ (tr.EventLoggedAt (TheEvent.ServerAuthenticated "Bob" element) t2))
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable compromiseSigKeyAttacker_PreservesReachability
    grind
  conv in (∀ t': Nat, _) =>
    rewrite [rewrite_forall_nat_into_forall_fin tr.length (by grind)]
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  refine ⟨ 8, (Literal.literalToBytes "quux 4".toByteArray), ?_ ⟩
  native_decide

/--
info: 'DY.Example.MerkleTree.compromiseSigKeyAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compromiseSigKeyAttacker_properties._native.native_decide.ax_1_3]
-/
#guard_msgs in
#print axioms compromiseSigKeyAttacker_properties

end DY.Example.MerkleTree
