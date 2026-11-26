module

import DY.Meta
public import Examples.ACME.Specification
import all Examples.ACME.Specification

namespace DY.Example.ACME.WithoutDEO

open DY.Comparse

-- Future work: the following section is boilerplate that could be meta-programmed
public section ExecBytesConfig

class HasExecBytesWithoutDEO where
  [bytesFunc: Bytes.Def]
  [bytesFunc0: Bytes.Has Random.BytesPart.Functor]
  [bytesFunc1: Bytes.Has Literal.BytesPart.Functor]
  [bytesFunc2: Bytes.Has Concat.BytesPart.Functor]
  [bytesFunc3: Bytes.Has Signature.BytesPart.Functor]
  [bytesLen: Bytes.length.Def]
  [bytesLen0: Bytes.length.Has Random.BytesPart.length]
  [bytesLen1: Bytes.length.Has Literal.BytesPart.length]
  [bytesLen2: Bytes.length.Has Concat.BytesPart.length]
  [bytesLen3: Bytes.length.Has Signature.BytesPart.length]
  [att: Bytes.AttackerKnows.Def]
  [att0: Bytes.AttackerKnows.Has Random.attackerKnows]
  [att1: Bytes.AttackerKnows.Has Literal.attackerKnows]
  [att2: Bytes.AttackerKnows.Has Concat.attackerKnows]
  [att3: Bytes.AttackerKnows.Has Signature.attackerKnows]

attribute [reducible, scoped instance] HasExecBytesWithoutDEO.bytesFunc
attribute [reducible, scoped instance] HasExecBytesWithoutDEO.bytesFunc0
attribute [reducible, scoped instance] HasExecBytesWithoutDEO.bytesFunc1
attribute [reducible, scoped instance] HasExecBytesWithoutDEO.bytesFunc2
attribute [reducible, scoped instance] HasExecBytesWithoutDEO.bytesFunc3
attribute [reducible, scoped instance] HasExecBytesWithoutDEO.bytesLen
attribute [           scoped instance] HasExecBytesWithoutDEO.bytesLen0
attribute [           scoped instance] HasExecBytesWithoutDEO.bytesLen1
attribute [           scoped instance] HasExecBytesWithoutDEO.bytesLen2
attribute [           scoped instance] HasExecBytesWithoutDEO.bytesLen3
attribute [reducible, scoped instance] HasExecBytesWithoutDEO.att
attribute [           scoped instance] HasExecBytesWithoutDEO.att0
attribute [           scoped instance] HasExecBytesWithoutDEO.att1
attribute [           scoped instance] HasExecBytesWithoutDEO.att2
attribute [           scoped instance] HasExecBytesWithoutDEO.att3

instance [HasExecBytesWithoutDEO]: HasExecBytes where

end ExecBytesConfig

-- Future work: the following section is boilerplate that could be meta-programmed
public section ExecTraceConfig

-- same as HasExecTrace, but instead extends HasExecBytesWithoutDEO
class HasExecTraceWithoutDEO extends HasExecBytesWithoutDEO where
  [traceExec: ExecTrace.Def]
  [traceExec0: ExecTrace.Has Network.TracePart.Exec]
  [traceExec1: ExecTrace.Has Random.TracePart.Exec]
  [traceExec2: ExecTrace.Has (ProtocolEvent.TracePart.Exec ACMEEvent)]
  [traceExec3: ExecTrace.Has (PersistentLocalState.CompromisableState.TracePart.Exec OwnerKeyState)]
  [traceExec4: ExecTrace.Has (PersistentLocalState.CompromisableState.TracePart.Exec OwnerAddressState)]
  [traceExec5: ExecTrace.Has (PersistentLocalState.CompromisableState.TracePart.Exec LetsEncryptPendingChallengeState)]
  [traceExec6: ExecTrace.Has (PersistentGlobalState.CompromisableState.TracePart.Exec DNSEntry)]
  [traceExec7: ExecTrace.Has (LongTermKeys.TracePart.Exec "ACME PKI")]
  [attBase: Trace.BaseAttackerKnows.Def]

attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec0
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec1
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec2
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec3
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec4
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec5
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec6
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.traceExec7
attribute [reducible, scoped instance] HasExecTraceWithoutDEO.attBase

instance [HasExecTraceWithoutDEO]: HasExecTrace where

end ExecTraceConfig

-- Future work: the following section is boilerplate that could be meta-programmed
public section ProofTraceConfig

class HasProofTrace extends HasExecTraceWithoutDEO where
  [traceProof: ProofTrace.Def]
  [traceProof0: ProofTrace.Has Network.TracePart.Proof]
  [traceProof1: ProofTrace.Has Random.TracePart.Proof]
  [traceProof2: ProofTrace.Has (ProtocolEvent.TracePart.Proof ACMEEvent)]
  [traceProof3: ProofTrace.Has (PersistentLocalState.CompromisableState.TracePart.Proof OwnerKeyState)]
  [traceProof4: ProofTrace.Has (PersistentLocalState.CompromisableState.TracePart.Proof OwnerAddressState)]
  [traceProof5: ProofTrace.Has (PersistentLocalState.CompromisableState.TracePart.Proof LetsEncryptPendingChallengeState)]
  [traceProof6: ProofTrace.Has (PersistentGlobalState.CompromisableState.TracePart.Proof DNSEntry)]
  [traceProof7: ProofTrace.Has (LongTermKeys.TracePart.Proof "ACME PKI")]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4
attribute [reducible, scoped instance] HasProofTrace.traceProof5
attribute [reducible, scoped instance] HasProofTrace.traceProof6
attribute [reducible, scoped instance] HasProofTrace.traceProof7

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

instance instSignPred
  : Signature.SignPred
where
  pred _skUsg _vk _msg _tr := True

instance
  [Bytes.Invariants.Def]
  : Signature.SignPredProof
where
  pred_later := by simp [Signature.SignPred.pred]

end BytesInvariants

-- Future work: the following section is boilerplate that could be meta-programmed
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: Bytes.Invariants.Def]
  [bytesInvProof: Bytes.Invariants.Lawful]
  [bytesInv0: Bytes.Invariants.Has Random.BytesPart.invariants]
  [bytesInv1: Bytes.Invariants.Has Literal.BytesPart.invariants]
  [bytesInv2: Bytes.Invariants.Has Concat.BytesPart.invariants]
  [bytesInv3: Bytes.Invariants.Has Signature.BytesPart.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

@[grind]
def sigAcmeUsage: Usage := {
  type := "SigKey",
  tag := "ACME PKI",
  data := none,
}

instance OwnerKeyStateInv : PersistentLocalState.CompromisableLocalStateInv OwnerKeyState
where
  invariant me st tr :=
    let oSk := st.oSk
    oSk.Publishable tr ∧
    oSk.HasUsage sigAcmeUsage tr
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    grind [canFlowTrans]

theorem OwnerKeyStateInv_imp_Invariant
  (participant: Participant) (st: OwnerKeyState) (tr: ProofTrace)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.oSk.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

instance OwnerAddressStateInv : PersistentLocalState.CompromisableLocalStateInv OwnerAddressState
where
  invariant me st tr :=
    let { address, oSk } := st
    oSk.Publishable tr ∧
    oSk.HasUsage sigAcmeUsage tr ∧
    tr.erase.EventLogged (ACMEEvent.OwnerRegisterAddress address (Signature.vk oSk))
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by grind [canFlowTrans]

instance LetsEncryptPendingChallengeStateInv : PersistentLocalState.CompromisableLocalStateInv LetsEncryptPendingChallengeState
where
  invariant me st tr :=
    let { address, token } := st
    token.Publishable tr
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by grind [canFlowTrans]

theorem LetsEncryptPendingChallengeStateInv_imp_Invariant
  (participant: Participant) (st: LetsEncryptPendingChallengeState) (tr: ProofTrace)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.token.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

instance DNSEntryInv : PersistentGlobalState.CompromisableGlobalStateInv DNSEntry
where
  invariant st tr :=
    st.sig.Publishable tr ∧
    ∃ oSk nonce token,
      st.sig = Signature.sign oSk nonce token ∧
      tr.erase.EventLogged (ACMEEvent.OwnerRegisterAddress st.address (Signature.vk oSk))
  invariant_later := by grind
  invariant_implies_KnowableBy state tr := by grind [canFlowTrans]

@[grind]
instance : LongTermKeys.ProofConfig "ACME PKI" (fun _ => sigAcmeUsage) (LongTermKeys.label "ACME PKI")
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "ACME PKI" who vk ∧
    vk.SignkeyHasUsage sigAcmeUsage tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

instance SignedDHEventInv : ProtocolEvent.EventInv ACMEEvent
where
  invariant tr ev :=
    match ev with
    | .OwnerRegisterAddress .. =>
      True
    | .LetsEncryptAcceptAddress address oPk =>
      tr.erase.EventLogged (ACMEEvent.OwnerRegisterAddress address oPk)

end TraceInvariant

-- Future work: the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: Trace.Invariant.Def]
  [traceInv0: Trace.Invariant.Has Network.TracePart.Proof]
  [traceInv1: Trace.Invariant.Has Random.TracePart.Proof]
  [traceInv2: Trace.Invariant.Has (ProtocolEvent.TracePart.Proof ACMEEvent)]
  [traceInv3: Trace.Invariant.Has (PersistentLocalState.CompromisableState.TracePart.Proof OwnerKeyState)]
  [traceInv4: Trace.Invariant.Has (PersistentLocalState.CompromisableState.TracePart.Proof OwnerAddressState)]
  [traceInv5: Trace.Invariant.Has (PersistentLocalState.CompromisableState.TracePart.Proof LetsEncryptPendingChallengeState)]
  [traceInv6: Trace.Invariant.Has (PersistentGlobalState.CompromisableState.TracePart.Proof DNSEntry)]
  [traceInv7: Trace.Invariant.Has (LongTermKeys.TracePart.Proof "ACME PKI")]
  [attBaseThm: Trace.BaseAttackerKnows_implies_Publishable.Proof]
  [attThm: Bytes.AttackerKnows_implies_Publishable.Proof]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.traceInv5
attribute [           scoped instance] HasTraceInvariant.traceInv6
attribute [           scoped instance] HasTraceInvariant.traceInv7
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

@[instance]
theorem Owner.generateKeyPair.proof (owner: Participant):
  HoareTriple
    (Owner.generateKeyPair owner)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Owner.generateKeyPair
  step with ⟨ (fun _ => Label.pub), sigAcmeUsage ⟩
  step
  step
  step by simp only [PersistentLocalState.LocalStateInv.invariant]; grind
  step
  grind

@[instance]
theorem Owner.claimAddress.proof (owner: Participant) (address: String) (oSkHandle: Nat):
  HoareTriple
    (Owner.claimAddress owner address oSkHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Owner.claimAddress
  step
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
  step by simp only [ProtocolEvent.EventInv.invariant]
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
  grind

@[instance]
theorem LetsEncrypt.initiate.proof (server: Participant) (address: String) (skHandle: Nat):
  HoareTriple
    (LetsEncrypt.initiate server address skHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold LetsEncrypt.initiate
  step with ⟨ (fun _ => Label.pub), Usage.nothing ⟩
  step
  step with ⟨ (fun _ => Label.secret), Usage.nothing ⟩
  step with ⟨ sigAcmeUsage ⟩ by simp_all [Signature.SignPred.pred, LongTermKeys.IsLongTermSecretKey, sigAcmeUsage]; grind
  step
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
  step
  grind

@[instance]
theorem Owner.respond.proof (owner server: Participant) (msgHandle lePkHandle stHandle: Nat):
  HoareTriple
    (Owner.respond owner server msgHandle lePkHandle stHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Owner.respond
  step
  step
  step
  step with ⟨ sigAcmeUsage ⟩ by simp_all [LongTermKeys.IsLongTermPublicKey]; grind
  step
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
  step with ⟨ (fun _ => Label.secret), Usage.nothing ⟩
  step with ⟨ sigAcmeUsage ⟩ by simp_all [PersistentLocalState.LocalStateInv.invariant, Signature.SignPred.pred]; grind
  step by simp_all [PersistentLocalState.LocalStateInv.invariant, PersistentGlobalState.GlobalStateInv.invariant, Signature.SignPred.pred]; grind
  step
  step
  grind

local
instance (priority := high)
  [ExecTrace.Def] [ProofTrace.Def]
  [Bytes.Invariants.Def]
  (vkey msg sig: Bytes)
  : HoareTriplePureGhost
    (Signature.verify vkey msg sig)
    (skUsg: Usage)
    (fun _tr => True)
    (fun res _tr => res = Signature.verify vkey msg sig)
where
  pf := by grind

theorem verify_implies_signature
  (vkey msg sig: Bytes)
  : Signature.verify vkey msg sig = true →
    ∃ sk nonce,
      vkey = Signature.vk sk ∧
      sig = Signature.sign sk nonce msg
:= by
  simp only [Signature.sign, Signature.verify, Signature.vk]
  grind

theorem sign_injective
  (sk1 sk2 nonce1 nonce2 msg1 msg2: Bytes)
  : Signature.sign sk1 nonce1 msg1 = Signature.sign sk2 nonce2 msg2  →
    sk1 = sk2
:= by
  simp only [Signature.sign]
  grind

@[instance]
theorem LetsEncrypt.finish.proof (server: Participant) (msgHandle pendingStHandle dnsEntryHandle: Nat):
  HoareTriple
    (LetsEncrypt.finish server msgHandle pendingStHandle dnsEntryHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold LetsEncrypt.finish
  step
  step
  step
  step
  step
  step with ⟨ sigAcmeUsage ⟩
  step by
    simp_all [PersistentGlobalState.GlobalStateInv.invariant, ProtocolEvent.EventInv.invariant]
    grind [verify_implies_signature, sign_injective]
  step
  grind

@[instance]
theorem OwnerKeyState.compromise.proof (stHandle: Nat): HoareTriple (OwnerKeyState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold OwnerKeyState.compromise; step; grind

@[instance]
theorem OwnerAddressState.compromise.proof (stHandle: Nat): HoareTriple (OwnerAddressState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold OwnerAddressState.compromise; step; grind

@[instance]
theorem LetsEncryptPendingChallengeState.compromise.proof (stHandle: Nat): HoareTriple (LetsEncryptPendingChallengeState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold LetsEncryptPendingChallengeState.compromise; step; grind

@[instance]
theorem DNSEntry.compromise.proof (stHandle: Nat): HoareTriple (DNSEntry.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold DNSEntry.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

-- Future work: the following section is boilerplate that could be meta-programmed
section
public instance: Trace.Reachable_implies_Invariant.Part Owner.generateKeyPair.transition := .mk (fun owner => Owner.generateKeyPair.proof owner)
public instance: Trace.Reachable_implies_Invariant.Part Owner.claimAddress.transition := .mk (fun (owner, address, oSkHandle) => Owner.claimAddress.proof owner address oSkHandle)
public instance: Trace.Reachable_implies_Invariant.Part LetsEncrypt.initiate.transition := .mk (fun (server, address, skHandle) => LetsEncrypt.initiate.proof server address skHandle)
public instance: Trace.Reachable_implies_Invariant.Part Owner.respond.transition := .mk (fun (owner, server, msgHandle, lePkHandle, stHandle) => Owner.respond.proof owner server msgHandle lePkHandle stHandle)
public instance: Trace.Reachable_implies_Invariant.Part LetsEncrypt.finish.transition := .mk (fun (server, msgHandle, pendingStHandle, dnsEntryHandle) => LetsEncrypt.finish.proof server msgHandle pendingStHandle dnsEntryHandle)
public instance: Trace.Reachable_implies_Invariant.Part OwnerKeyState.compromise.transition := .mk (fun stHandle => OwnerKeyState.compromise.proof stHandle)
public instance: Trace.Reachable_implies_Invariant.Part OwnerAddressState.compromise.transition := .mk (fun stHandle => OwnerAddressState.compromise.proof stHandle)
public instance: Trace.Reachable_implies_Invariant.Part LetsEncryptPendingChallengeState.compromise.transition := .mk (fun stHandle => LetsEncryptPendingChallengeState.compromise.proof stHandle)
public instance: Trace.Reachable_implies_Invariant.Part DNSEntry.compromise.transition := .mk (fun stHandle => DNSEntry.compromise.proof stHandle)
end

#combine into Trace.Reachable_implies_Invariant from
  Network,
  Random,
  LongTermKeys "ACME PKI",
  Owner.generateKeyPair,
  Owner.claimAddress,
  LetsEncrypt.initiate,
  Owner.respond,
  LetsEncrypt.finish,
  OwnerKeyState.compromise,
  OwnerAddressState.compromise,
  LetsEncryptPendingChallengeState.compromise,
  DNSEntry.compromise,

end ReachabilityImpliesInvariant

end DY.Example.ACME.WithoutDEO
