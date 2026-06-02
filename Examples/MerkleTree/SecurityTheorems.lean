module

import DY.Meta
import DY.Meta.Utils
public import Examples.MerkleTree.Specification
public import Examples.MerkleTree.Proof
public import Examples.MerkleTree.Instance

namespace DY.Example.MerkleTree

public
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

end DY.Example.MerkleTree
