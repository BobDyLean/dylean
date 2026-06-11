module

import DY.Meta
import DY.Meta.Utils
import Examples.ACME.Specification
import Examples.ACME.WithoutDEO.Instance
public meta import Examples.ACME.WithoutDEO.Instance

namespace DY.Example.ACME.WithoutDEO

public
def honestAttacker: Traceful Unit := do
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "ACME PKI" "LetsEncrypt" -- 4
  let (_, oSkHandle) ← Owner.generateKeyPair "Owner" -- 3
  let stHandle ← Owner.claimAddress "Owner" "example.com" oSkHandle -- 2
  let (msgHandle, pendingStHandle) ← LetsEncrypt.initiate "LetsEncrypt" "example.com" skHandle -- 4
  let (dnsEntryHandle, msgHandle') ← Owner.respond "Owner" "LetsEncrypt" msgHandle pkHandle stHandle -- 3
  LetsEncrypt.finish "LetsEncrypt" msgHandle' pendingStHandle dnsEntryHandle -- 1
  return ()

#guard (honestAttacker.run Trace.nil).fst = some ()

theorem honestAttacker_PreservesReachability
  : honestAttacker.PreservesReachability reachability (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  dsimp only [honestAttacker]

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.reachability "ACME PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.reachability]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Owner.generateKeyPair.reachability)
  · assumption
  · simp [Owner.generateKeyPair.reachability]
  intro ⟨ _, oSkHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Owner.claimAddress.reachability) _ ("Owner", "example.com", oSkHandle)
  · assumption
  · simp [Owner.claimAddress.reachability]
  intro stHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LetsEncrypt.initiate.reachability) _ ("LetsEncrypt", "example.com", skHandle)
  · assumption
  · simp [LetsEncrypt.initiate.reachability]
  intro ⟨ msgHandle, pendingStHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Owner.respond.reachability) _ ("Owner", "LetsEncrypt", msgHandle, pkHandle, stHandle)
  · assumption
  · simp [Owner.respond.reachability]
  intro ⟨ dnsEntryHandle, msgHandle' ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LetsEncrypt.finish.reachability) _ ("LetsEncrypt", msgHandle', pendingStHandle, dnsEntryHandle)
  · assumption
  · simp [LetsEncrypt.finish.reachability]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

public
theorem honestAttacker_properties:
  let tr := (honestAttacker.run (Trace.nil)).snd.val
  tr.Reachable reachability ∧
  ∃ t1 t2 oPk,
    t1 < t2 ∧
    tr.EventLoggedAt (ACMEEvent.OwnerRegisterAddress "example.com" oPk) t1 ∧
    tr.EventLoggedAt (ACMEEvent.LetsEncryptAcceptAddress "example.com" oPk) t2
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable honestAttacker_PreservesReachability
    grind
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt ACMEEvent 7 tr) with
    | some (ACMEEvent.OwnerRegisterAddress addr oPk) => oPk
    | _ => Comparse.BytesLike.empty
  refine ⟨ 7, 16, witness, ?_ ⟩
  native_decide

/--
info: 'DY.Example.ACME.WithoutDEO.honestAttacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 honestAttacker_properties._native.native_decide.ax_1_6]
-/
#guard_msgs in
#print axioms honestAttacker_properties

end DY.Example.ACME.WithoutDEO
