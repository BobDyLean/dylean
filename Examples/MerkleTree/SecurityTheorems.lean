-- module -- no module to use `#print axioms`

import DY.Meta
import DY.Meta.Utils
import Examples.MerkleTree.Specification
import Examples.MerkleTree.Proof
import Examples.MerkleTree.Instance

namespace DY.Example.MerkleTree

section SecurityTheorems

theorem client_authentication
  (server: Participant)
  (element: Bytes)
  (time: Nat)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (TheEvent.ClientAccept server element) time →
    (
      let tr_before := tr.prefix time
      tr_before.EventLogged (TheEvent.ServerAuthenticated server element) ∨
      (∃ spk, LongTermKeys.LongTermKeyCompromised "MerkleTree PKI" server spk tr_before)
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant, LongTermKeys.label] at this
  grind

/--
info: 'DY.Example.MerkleTree.client_authentication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms client_authentication

end SecurityTheorems

section SanityChecks

def honest: Traceful Unit := do
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

theorem honest_PreservesReachability
  : honest.PreservesReachability reachability
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr
  unfold honest
  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (LongTermKeys.generateKeyPair.reachability "MerkleTree PKI")
    simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Network.reachability)
    simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle1 tr h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Network.reachability)
    simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle2 tr h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Network.reachability)
    simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle3 tr h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Network.reachability)
    simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle4 tr h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Network.reachability)
    simp [Literal.attacker_knows_literalToBytes]
  intro msgHandle5 tr h_tr tr_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Server.authenticate.reachability) _ ("Bob", [msgHandle1, msgHandle2, msgHandle3, msgHandle4, msgHandle5], skHandle)
    simp [Server.authenticate.reachability]
  intro ⟨ msgSigHandle, stHandle ⟩ tr h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Server.proveInclusion.reachability) _ ("Bob", 3, stHandle)
    simp [Server.proveInclusion.reachability]
  intro msgInclHandle tr h_tr h_le
  dsimp only

  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (Client.checkInclusion.reachability) _ ("Bob", msgSigHandle, msgInclHandle, pkHandle)
    simp [Client.checkInclusion.reachability]
  intro _ tr h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure

theorem sanity_check:
  ∃ tr: ExecTrace,
    tr.Reachable reachability ∧
    ∃ (t1 t2: Nat) (msg: Bytes),
      t1 < t2 ∧
      tr.EventLoggedAt (TheEvent.ServerAuthenticated "Bob" msg) t1 ∧
      tr.EventLoggedAt (TheEvent.ClientAccept "Bob" msg) t2
:= by
  refine ⟨ (honest.run (Trace.nil)).snd, ?_ ⟩
  apply And.intro
  · exact honest_PreservesReachability Trace.nil (Trace.ReachableFrom.Base)
  refine ⟨ 12, 18, (Literal.literalToBytes "qux 3".toByteArray), ?_ ⟩
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  native_decide

/--
info: 'DY.Example.MerkleTree.sanity_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sanity_check._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms sanity_check

end SanityChecks

end DY.Example.MerkleTree
