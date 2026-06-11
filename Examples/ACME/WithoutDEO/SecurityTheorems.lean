module

import DY.Meta
import DY.Meta.Utils
public import Examples.ACME.Specification
public import Examples.ACME.WithoutDEO.Proof
import all Examples.ACME.WithoutDEO.Proof
import all Examples.SignedDH.Proof
public import Examples.ACME.WithoutDEO.Instance

namespace DY.Example.ACME.WithoutDEO

public
theorem owner_authentication
  (address: String) (oPk: Bytes)
  (time: Nat)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (ACMEEvent.LetsEncryptAcceptAddress address oPk) time →
    (
      let tr_before := tr.prefix time
      tr_before.EventLogged (ACMEEvent.OwnerRegisterAddress address oPk)
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant] at this
  grind

/--
info: 'DY.Example.ACME.WithoutDEO.owner_authentication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms owner_authentication

end DY.Example.ACME.WithoutDEO
