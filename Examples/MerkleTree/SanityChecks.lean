module

import DY.Meta
import DY.Meta.Utils
public import Examples.MerkleTree.Specification
public import Examples.MerkleTree.Proof
public import Examples.MerkleTree.Instance
public meta import Examples.MerkleTree.Instance

namespace DY.Example.MerkleTree

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
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle2 tr h_post h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle3 tr h_post h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle4 tr h_post h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.reachability)
  · assumption
  · simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle5 tr h_post h_tr tr_le
  dsimp only

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
  dsimp only

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

end DY.Example.MerkleTree
