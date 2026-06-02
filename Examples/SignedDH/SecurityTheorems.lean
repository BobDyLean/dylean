module

import DY.Meta
import DY.Meta.Utils
public import Examples.SignedDH.Specification
public import Examples.SignedDH.Proof
import all Examples.SignedDH.Proof
public import Examples.SignedDH.Instance

namespace DY.Example.SignedDH

public
theorem client_auth
  (client server: Participant)
  (xPk yPk k: Bytes)
  (time: Nat)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
    (
      let tr_before := tr.prefix time
      tr_before.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk k) ∨
      (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH PKI" server spk tr_before)
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant, LongTermKeys.label] at this
  grind

/--
info: 'DY.Example.SignedDH.client_auth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms client_auth

public
theorem client_secrecy
  (client server: Participant)
  (xPk yPk k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
    (
      let tr_before := tr.prefix time
      (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH PKI" server spk tr_before) ∨
      ClientEphemeralStateCompromised client xPk tr ∨
      ServerEphemeralStateCompromised server yPk tr
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant] at this
  simp_all [client_label, server_label, LongTermKeys.label]
  grind

/--
info: 'DY.Example.SignedDH.client_secrecy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms client_secrecy

end DY.Example.SignedDH
