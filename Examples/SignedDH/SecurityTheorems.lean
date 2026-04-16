module

public import DY.Step
import DY.Step.Utils
public import Examples.SignedDH.Specification
public import Examples.SignedDH.Proof
import all Examples.SignedDH.Proof

namespace DY.Example.SignedDH

theorem client_auth
  (client server: Participant)
  (xPk yPk k: Bytes)
  (time: Nat)
  (tr: ProofTrace):
  tr.Invariant → -- reachable
  tr.erase.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
  (
    let tr_before := tr.prefix time
    tr_before.erase.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk k) ∨
    (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH" server spk tr_before.erase)
  )
:= by
  intro h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant, LongTermKeys.label] at this
  grind

theorem client_secrecy
  (client server: Participant)
  (xPk yPk k: Bytes)
  (tr: ProofTrace):
  tr.Invariant → -- reachable
  k.AttackerKnows tr.erase →
  tr.erase.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
  (
    let tr_before := tr.prefix time
    (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH" server spk tr_before.erase) ∨
    ClientEphemeralStateCompromised client xPk tr.erase ∨
    ServerEphemeralStateCompromised server yPk tr.erase
  )
  := by
    intro h_trinv h_pub h_ev
    have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
    simp [ProtocolEvent.EventInv.invariant] at this
    simp_all [client_label, server_label, LongTermKeys.label]
    grind

end DY.Example.SignedDH
