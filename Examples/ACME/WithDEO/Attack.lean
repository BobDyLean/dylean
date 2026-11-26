module

import DY.Meta
import DY.Meta.Utils
import Examples.ACME.Specification
import Examples.ACME.WithDEO.Instance
public meta import Examples.ACME.WithDEO.Instance
public import Examples.ACME.WithDEO.SignDEO

namespace DY.Example.ACME.WithDEO

public
def attacker: Traceful Unit := do
  -- First, a honest run of the protocol happens
  let (_, pkHandle, skHandle) ← LongTermKeys.generateKeyPair "ACME PKI" "LetsEncrypt" -- 4
  let (_, oSkHandle) ← Owner.generateKeyPair "Owner" -- 3
  let stHandle ← Owner.claimAddress "Owner" "example.com" oSkHandle -- 2
  let (msgHandle, pendingStHandle) ← LetsEncrypt.initiate "LetsEncrypt" "example.com" skHandle -- 4
  let (dnsEntryHandle, msgHandle') ← Owner.respond "Owner" "LetsEncrypt" msgHandle pkHandle stHandle -- 3
  LetsEncrypt.finish "LetsEncrypt" msgHandle' pendingStHandle dnsEntryHandle -- 1

  -- start another run of the protocol
  let (msgHandle', pendingStHandle') ← LetsEncrypt.initiate "LetsEncrypt" "example.com" skHandle -- 4

  -- retrieve the signature in the DNS entry through "compromise" (it is public data)
  let dnsEntryMsgHandle ← DNSEntry.compromise dnsEntryHandle -- 2
  let dnsEntryBytes ← Network.receiveMessage dnsEntryMsgHandle
  let dnsEntry: DNSEntry ← Comparse.parse dnsEntryBytes
  let sig := dnsEntry.sig

  -- receive the token
  let msgBytes ← Network.receiveMessage msgHandle'
  let msg: LetsEncryptMessage ← Comparse.parse msgBytes
  let token := msg.token
  -- compute the DEO
  let oSk' := SignDEO.deogen token sig
  let oPk' := Signature.vk oSk'

  let msgHandle ← Network.sendMessage (Comparse.serialize ({address := "example.com", oPk := oPk'}: OwnerMessage)) -- 1
  LetsEncrypt.finish "LetsEncrypt" msgHandle pendingStHandle' dnsEntryHandle -- 1
  return ()

#guard (attacker.run Trace.empty).fst = some ()

-- TODO: move, but where?
theorem liftM_parse_preserves_reachability
  {a: Type} [Comparse.ParseableSerializeable a]
  (config: TransitionSystem)
  (buf: Bytes)
  : (liftM (Comparse.parse buf): Traceful a).PreservesReachability config (fun _ => True) (fun res _ => Comparse.FormatRel buf res)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
  grind

-- Future work: we could design a step-like tactic to automate this proof
theorem attacker_PreservesReachability
  : attacker.PreservesReachability transition (fun _ => True) (fun _ _ => True)
:= by
  unfold Traceful.PreservesReachability
  intro tr h_tr h_pre
  unfold attacker

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LongTermKeys.generateKeyPair.transition "ACME PKI")
  · assumption
  · simp [LongTermKeys.generateKeyPair.transition]
  intro ⟨ _, pkHandle, skHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Owner.generateKeyPair.transition)
  · assumption
  · simp [Owner.generateKeyPair.transition]
  intro ⟨ _, oSkHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Owner.claimAddress.transition) _ ("Owner", "example.com", oSkHandle)
  · assumption
  · simp [Owner.claimAddress.transition]
  intro stHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LetsEncrypt.initiate.transition) _ ("LetsEncrypt", "example.com", skHandle)
  · assumption
  · simp [LetsEncrypt.initiate.transition]
  intro ⟨ msgHandle, pendingStHandle ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Owner.respond.transition) _ ("Owner", "LetsEncrypt", msgHandle, pkHandle, stHandle)
  · assumption
  · simp [Owner.respond.transition]
  intro ⟨ dnsEntryHandle, msgHandle' ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LetsEncrypt.finish.transition) _ ("LetsEncrypt", msgHandle', pendingStHandle, dnsEntryHandle)
  · assumption
  · simp [LetsEncrypt.finish.transition]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LetsEncrypt.initiate.transition) _ ("LetsEncrypt", "example.com", skHandle)
  · assumption
  · simp [LetsEncrypt.initiate.transition]
  intro ⟨ msgHandle', pendingStHandle' ⟩ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (DNSEntry.compromise.transition) _ (dnsEntryHandle)
  · assumption
  · simp [DNSEntry.compromise.transition]
  intro dnsEntryMsgHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro dnsEntryBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro dnsEntry tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Network.receiveMessage.preservesReachability
  · assumption
  · grind
  intro msgBytes tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply liftM_parse_preserves_reachability
  · assumption
  · grind
  intro msg tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (Network.transition)
  · assumption
  · simp only [Comparse.AttackerKnows_serialize, OwnerMessage.IsWellFormed_eq]
    apply SignDEO.attacker_knows_vk
    apply SignDEO.attacker_knows_deogen
    · grind
    · grind
  intro msgHandle tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (LetsEncrypt.finish.transition) _ ("LetsEncrypt", msgHandle, pendingStHandle', dnsEntryHandle)
  · assumption
  · simp [LetsEncrypt.finish.transition]
  intro _ tr h_post h_tr h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · assumption
  grind

theorem rewrite_forall_nat_into_forall_fin {P: Nat → Prop} (n: Nat) (h: ∀ i, n ≤ i → P i): (∀ i: Nat, P i) = (∀ i: Fin n, P i.val) := by
  simp only [eq_iff_iff]
  constructor
  · grind
  · intro h i
    by_cases n ≤ i
    · grind
    · exact h ⟨ i, by grind ⟩

public
theorem attacker_properties:
  let tr := (attacker.run (Trace.empty)).snd.val
  tr.Reachable transition ∧
  ∃ t oPk,
    tr.EventLoggedAt (ACMEEvent.LetsEncryptAcceptAddress "example.com" oPk) t ∧
    (∀ t', ¬ tr.EventLoggedAt (ACMEEvent.OwnerRegisterAddress "example.com" oPk) t')
:= by
  intro tr
  refine ⟨ ?_, ?_ ⟩
  · apply Traceful.PreservesReachability_to_Reachable attacker_PreservesReachability
    grind
  conv in (∀ t': Nat, _) =>
    rewrite [rewrite_forall_nat_into_forall_fin tr.length (by grind)]
  simp only [DY.Trace.EventLoggedAt_eq_getEventAt]
  let witness :=
    match (Trace.getEventAt ACMEEvent 24 tr) with
    | some (ACMEEvent.LetsEncryptAcceptAddress addr oPk) => oPk
    | _ => Comparse.BytesLike.empty
  refine ⟨ 24, witness, ?_ ⟩
  native_decide

/--
info: 'DY.Example.ACME.WithDEO.attacker_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 attacker_properties._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms attacker_properties

end DY.Example.ACME.WithDEO
