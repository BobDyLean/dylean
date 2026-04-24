-- module -- no module to use `#print axioms`

import DY.Step
import DY.Step.Utils
import Examples.SignedDH.Specification
import Examples.SignedDH.Proof
import Examples.SignedDH.Instance

namespace DY.Example.SignedDH

def honest: Traceful Unit := do
  let (_, tsPk, tsSk) ← LongTermKeys.generateKeyPair "SignedDH" "Bob" -- 4
  let (tsClientSt, tsMsgClient) ← client_initiate "Alice" -- 4
  let (_tsServerSt, tsMsgServer) ← server_receive "Bob" tsSk tsMsgClient -- 5
  let _ ← client_finish "Alice" "Bob" tsPk tsMsgServer tsClientSt -- 2

theorem honest_PreservesReachability
  : honest.PreservesReachability reachability
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr
  unfold honest
  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (LongTermKeys.reachability "SignedDH")
    simp
  intro ⟨ _, tsPk, tsSk ⟩ tr h_tr h_le
  dsimp only
  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (.make (fun me => client_initiate me))
    simp
  intro ⟨ tsClientSt, tsMsgClient ⟩ tr h_tr h_le
  dsimp only
  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (.make (fun (me, sk_ts, msg_ts) => server_receive me sk_ts msg_ts)) _ ("Bob", tsSk, tsMsgClient)
    simp
  intro ⟨ _, tsMsgServer ⟩ tr h_tr h_le
  dsimp only
  apply Traceful.PreservesReachabilityFrom_bind
  · assumption
  · apply Traceful.PreservesReachabilityFrom_base (.make (fun (me, server, pk_ts, msg_ts, sid) => client_finish me server pk_ts msg_ts sid)) _ ("Alice", "Bob", tsPk, tsMsgServer, tsClientSt)
    simp
  intro _ tr h_tr h_le
  apply Traceful.PreservesReachabilityFrom_pure

theorem sanity_check:
  ∃ tr: ExecTrace,
    tr.Reachable reachability ∧
    ∃ t1 t2 xPk yPk k,
      t1 < t2 ∧
      tr.EventLoggedAt (SignedDHEvent.ServerFinishEvent "Bob" xPk yPk k) t1 ∧
      tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent "Alice" "Bob" xPk yPk k) t2
:= by
  exists (honest.run (Trace.nil)).snd
  apply And.intro
  · exact honest_PreservesReachability Trace.nil (Trace.ReachableFrom.Base)
  exists 10
  exists 13
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt SignedDHEvent 10 (honest.run Trace.nil).snd.val) with
    | some (SignedDHEvent.ServerFinishEvent _ xPk yPk k) => (xPk, yPk, k)
    | _ => (Comparse.BytesLike.empty, Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  exists witness.fst
  exists witness.snd.fst
  exists witness.snd.snd
  native_decide

/--
info: 'DY.Example.SignedDH.sanity_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sanity_check._native.native_decide.ax_1_5]
-/
#guard_msgs in
#print axioms sanity_check

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
      (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH" server spk tr_before)
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

theorem client_secrecy
  (client server: Participant)
  (xPk yPk k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
    (
      let tr_before := tr.prefix time
      (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH" server spk tr_before) ∨
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
