module

import DY.Meta
public import Examples.ACME.Specification
import all Examples.ACME.Specification

namespace DY.Example.ACME.WithoutDEO

open DY.Comparse

public section ExecBytesConfig

class HasExecBytesWithoutDEO where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has Signature.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has Signature.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has Signature.attackerKnowledge]

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

public section ExecTraceConfig

-- same as HasExecTrace, but instead extends HasExecBytesWithoutDEO
class HasExecTraceWithoutDEO extends HasExecBytesWithoutDEO where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT ACMEEvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OwnerKeyState)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OwnerAddressState)]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT LetsEncryptPendingChallengeState)]
  [traceExec6: ExecTraceTypes.Has (PersistentGlobalState.CompromisableState.ExecEntryT DNSEntry)]
  [traceExec7: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "ACME PKI")]
  [attBase: BaseAttackerKnowledge]

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

-- TODO: this whole section should be meta-programmable
public section ProofTraceConfig

class HasProofTrace extends HasExecTraceWithoutDEO where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT ACMEEvent)]
  [traceProof3: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT OwnerKeyState)]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT OwnerAddressState)]
  [traceProof5: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT LetsEncryptPendingChallengeState)]
  [traceProof6: ProofTraceTypes.Has (PersistentGlobalState.CompromisableState.ProofEntryT DNSEntry)]
  [traceProof7: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "ACME PKI")]

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
  [BytesInvariants]
  : Signature.SignPredProof
where
  pred_later := by simp [Signature.SignPred.pred]

end BytesInvariants

public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInvProof: BytesInvariantsProofs]
  [bytesInv0: BytesInvariants.Has Random.invariants]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has Signature.invariants]

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

-- TODO: this whole section should be meta-programmable
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT ACMEEvent)]
  [traceInv3: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT OwnerKeyState)]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT OwnerAddressState)]
  [traceInv5: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT LetsEncryptPendingChallengeState)]
  [traceInv6: TraceInvariant.Has (PersistentGlobalState.CompromisableState.ProofEntryT DNSEntry)]
  [traceInv7: TraceInvariant.Has (LongTermKeys.ProofEntryT "ACME PKI")]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

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
theorem Owner.generateKeyPair.spec (owner: Participant):
  HoareTriple
    (Owner.generateKeyPair owner)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold Owner.generateKeyPair
  step with ⟨ (fun _ => Label.pub), sigAcmeUsage ⟩
  step
  step
  step by simp only [PersistentLocalState.LocalStateInv.invariant]; grind
  step
  grind

@[instance]
theorem Owner.claimAddress.spec (owner: Participant) (address: String) (oSkHandle: Nat):
  HoareTriple
    (Owner.claimAddress owner address oSkHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold Owner.claimAddress
  step
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
  step by simp only [ProtocolEvent.EventInv.invariant]
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
  step
  grind

@[instance]
theorem LetsEncrypt.initiate.spec (server: Participant) (address: String) (skHandle: Nat):
  HoareTriple
    (LetsEncrypt.initiate server address skHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
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
theorem Owner.respond.spec (owner server: Participant) (msgHandle lePkHandle stHandle: Nat):
  HoareTriple
    (Owner.respond owner server msgHandle lePkHandle stHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
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
  [ExecTraceTypes] [ProofTraceTypes]
  [BytesInvariants]
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
theorem LetsEncrypt.finish.spec (server: Participant) (msgHandle pendingStHandle dnsEntryHandle: Nat):
  HoareTriple
    (LetsEncrypt.finish server msgHandle pendingStHandle dnsEntryHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
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
theorem OwnerKeyState.compromise.spec (stHandle: Nat): HoareTriple (OwnerKeyState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold OwnerKeyState.compromise; step; grind

@[instance]
theorem OwnerAddressState.compromise.spec (stHandle: Nat): HoareTriple (OwnerAddressState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold OwnerAddressState.compromise; step; grind

@[instance]
theorem LetsEncryptPendingChallengeState.compromise.spec (stHandle: Nat): HoareTriple (LetsEncryptPendingChallengeState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold LetsEncryptPendingChallengeState.compromise; step; grind

@[instance]
theorem DNSEntry.compromise.spec (stHandle: Nat): HoareTriple (DNSEntry.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold DNSEntry.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

public instance: ReachableImpliesInvariant Owner.generateKeyPair.reachability := .mk (fun owner => Owner.generateKeyPair.spec owner)
public instance: ReachableImpliesInvariant Owner.claimAddress.reachability := .mk (fun (owner, address, oSkHandle) => Owner.claimAddress.spec owner address oSkHandle)
public instance: ReachableImpliesInvariant LetsEncrypt.initiate.reachability := .mk (fun (server, address, skHandle) => LetsEncrypt.initiate.spec server address skHandle)
public instance: ReachableImpliesInvariant Owner.respond.reachability := .mk (fun (owner, server, msgHandle, lePkHandle, stHandle) => Owner.respond.spec owner server msgHandle lePkHandle stHandle)
public instance: ReachableImpliesInvariant LetsEncrypt.finish.reachability := .mk (fun (server, msgHandle, pendingStHandle, dnsEntryHandle) => LetsEncrypt.finish.spec server msgHandle pendingStHandle dnsEntryHandle)
public instance: ReachableImpliesInvariant OwnerKeyState.compromise.reachability := .mk (fun stHandle => OwnerKeyState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant OwnerAddressState.compromise.reachability := .mk (fun stHandle => OwnerAddressState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant LetsEncryptPendingChallengeState.compromise.reachability := .mk (fun stHandle => LetsEncryptPendingChallengeState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant DNSEntry.compromise.reachability := .mk (fun stHandle => DNSEntry.compromise.spec stHandle)

#combine into ReachabilityTheorem from
  Network,
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
