module

import DY.Meta
import DY.Meta.Utils
public import Examples.SignedDHKEM.Specification
public import Examples.SignedDHKEM.Proof
import all Examples.SignedDHKEM.Proof
public import Examples.SignedDHKEM.Instance

namespace DY.Example.SignedDHKEM

public
theorem client_auth
  (client server: Participant)
  (xPk yPk zPk k: Bytes)
  (time: Nat)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent client server xPk yPk zPk k) time →
    (
      let tr_before := tr.prefix time
      tr_before.EventLogged (SignedDHKEMEvent.ServerFinishEvent server xPk yPk zPk k) ∨
      (∃ spk,
        LongTermKeys.LongTermKeyCompromised "SignedDHKEM PKI" server spk tr_before ∨
        Signature'.Broken.ThisVkHasBeenBroken spk tr_before
      )
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant, LongTermKeys.label, mkLongTermLabel, Signature'.Broken.label] at this
  grind

/--
info: 'DY.Example.SignedDHKEM.client_auth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms client_auth

public
theorem client_secrecy
  (client server: Participant)
  (xPk yPk zPk k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLoggedAt (SignedDHKEMEvent.ClientFinishEvent client server xPk yPk zPk k) time →
    (
      let tr_before := tr.prefix time
      (
        (∃ spk,
          LongTermKeys.LongTermKeyCompromised "SignedDHKEM PKI" server spk tr_before ∨
          Signature'.Broken.ThisVkHasBeenBroken spk tr_before
        )
      ) ∨
      (
        (
          ClientEphemeralDHStateCompromised client xPk tr ∨
          DiffieHellman'.Broken.ThisDhPkHasBeenBroken xPk tr ∨
          DiffieHellman'.Broken.ThisDhPkHasBeenBroken yPk tr
        ) ∧ (
          ClientEphemeralKEMStateCompromised client zPk tr ∨
          KEM.Broken.ThisKemPkHasBeenBroken zPk tr
        )
      ) ∨
      ServerEphemeralStateCompromised server xPk yPk zPk tr
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant] at this
  simp_all [clientDhLabel, clientKemLabel, serverLabel, mkLongTermLabel, LongTermKeys.label, KEM.Broken.label, DiffieHellman'.Broken.label, Signature'.Broken.label]
  grind

/--
info: 'DY.Example.SignedDHKEM.client_secrecy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms client_secrecy

end DY.Example.SignedDHKEM
