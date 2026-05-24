-- module -- no module to use `#print axioms`

import DY.Meta
import DY.Meta.Utils
import Examples.SignedDH.Specification
import Examples.SignedDH.Proof
import Examples.SignedDH.Instance

namespace DY.Example.SignedDH

def honest: Traceful Unit := do
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "SignedDH PKI" "Bob" -- 4
  let (stClientHandle, msgClientHandle) ← client_initiate "Alice" -- 4
  let (_stServerHandle, msgServerHandle) ← server_receive "Bob" skHandle msgClientHandle -- 5
  let _ ← client_finish "Alice" "Bob" pkHandle msgServerHandle stClientHandle -- 2

theorem honest_PreservesReachability
  : honest.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honest]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "SignedDH PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, tsPk, tsSk ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (client_initiate.reachability)
  · assumption
  · simp [client_initiate.reachability]
  intro ⟨ tsClientSt, tsMsgClient ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (server_receive.reachability) _ ("Bob", tsSk, tsMsgClient)
  · assumption
  · simp [server_receive.reachability]
  intro ⟨ _, tsMsgServer ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (client_finish.reachability) _ ("Alice", "Bob", tsPk, tsMsgServer, tsClientSt)
  · assumption
  · simp [client_finish.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

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
  · apply Traceful.PreservesReachability_to_Reachable honest_PreservesReachability
    grind
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
 sanity_check._native.native_decide.ax_1_6]
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
