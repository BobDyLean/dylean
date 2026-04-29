module

import DY.Meta.Step
import DY.Meta.Utils
public import Examples.SignedDH.Specification
import all Examples.SignedDH.Specification

namespace DY.Example.SignedDH

open DY.Comparse

-- TODO: this whole section should be meta-programmable
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent)]
  [traceProof3: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState)]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState)]
  [traceProof5: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState)]
  [traceProof6: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "SignedDH")]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4
attribute [reducible, scoped instance] HasProofTrace.traceProof5
attribute [reducible, scoped instance] HasProofTrace.traceProof6

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

def client_label
  (me: Participant) (xPk: Bytes)
  : Label
where
  isCorrupt tr := ClientEphemeralStateCompromised me xPk tr

def server_label
  (me: Participant) (yPk: Bytes)
  : Label
where
  isCorrupt tr := ServerEphemeralStateCompromised me yPk tr

structure LongTermKeyUsage where
  principal: Participant

instance : ParseableSerializeable LongTermKeyUsage := .make <|
  .triviallyIsomorphic
    (.string)
    (fun principal => { principal })
    (fun { principal := principal } => principal)


@[grind]
def mk_long_term_usage (me: Participant): Usage := {
  type := "SigKey",
  tag := "SignedDH",
  data := serialize ({ principal := me }: LongTermKeyUsage)
}

@[grind inj]
theorem mk_long_term_usage_inj:
  Function.Injective mk_long_term_usage
  := by
    simp [Function.Injective, mk_long_term_usage]
    grind

instance SignedDHSignPred
  : Signature.SignPred
where
  pred skUsg vk msg tr :=
    ∃ server, skUsg = mk_long_term_usage server ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) => (
        ∃ ySk,
          msg.yPk = DiffieHellman.dh_pk ySk ∧
          ySk.label tr = server_label server msg.yPk ∧
          tr.erase.EventLogged (SignedDHEvent.ServerFinishEvent server msg.xPk msg.yPk (Hash.hash (DiffieHellman.dh msg.xPk ySk)))
      )
    )

instance
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman.DhPk.invariants]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  : Signature.SignPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman.dh_pk.WellFormed]

end BytesInvariants

-- TODO: this whole section should be meta-programmable
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInv0: BytesInvariantsProofs]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has Hash.invariants]
  [bytesInv4: BytesInvariants.Has Signature.invariants]
  [bytesInv5: BytesInvariants.Has DiffieHellman.invariants]
  [bytesInv6: BytesInvariants.Has Random.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3
attribute [           scoped instance] HasBytesInvariants.bytesInv4
attribute [           scoped instance] HasBytesInvariants.bytesInv5
attribute [           scoped instance] HasBytesInvariants.bytesInv6

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

instance ClientInitiateStateInv : PersistentLocalState.CompromisableLocalStateInv ClientInitiateState
where
  invariant me st tr :=
    let { xPk, xSk } := st
    xPk = DiffieHellman.dh_pk xSk ∧
    xPk.Publishable tr ∧
    xSk.Invariant tr ∧
    xSk.label tr = client_label me xPk
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (client_label participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, client_label, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

-- for monotonicity
theorem ClientInitiateStateInv_imp_Invariant
  (participant: Participant) (st: ClientInitiateState)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.xSk.Invariant tr ∧
      st.xPk.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] ClientInitiateStateInv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr

instance ClientFinishStateInv : PersistentLocalState.CompromisableLocalStateInv ClientFinishState
where
  invariant me st tr :=
    let { xPk, kC } := st
    xPk.Publishable tr ∧
    kC.Invariant tr ∧
    (kC.label tr).canFlow (client_label me xPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (client_label participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, client_label, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

instance ServerFinishStateInv : PersistentLocalState.CompromisableLocalStateInv ServerFinishState
where
  invariant me st tr :=
    let { yPk, kS } := st
    yPk.Publishable tr ∧
    kS.Invariant tr ∧
    (kS.label tr).canFlow (server_label me yPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (server_label participant state.yPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, server_label, ServerEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

@[grind]
instance : LongTermKeys.ProofConfig "SignedDH" mk_long_term_usage
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "SignedDH" who vk ∧
    vk.SignkeyHasUsage (mk_long_term_usage who) tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

instance SignedDHEventInv : ProtocolEvent.EventInv (SignedDHEvent)
where
  invariant tr ev :=
    match ev with
    | SignedDHEvent.ClientInitiateEvent client xPk => (
      xPk.Invariant tr ∧
      xPk.dhSkLabel tr = client_label client xPk
    )
    | SignedDHEvent.ServerFinishEvent server xPk yPk kS => (
      kS.Invariant tr ∧
      xPk.Invariant tr ∧
      kS.label tr = (server_label server yPk).join (xPk.dhSkLabel tr)
    )
    | SignedDHEvent.ClientFinishEvent client server xPk yPk kC => (
      (
        tr.erase.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk kC) ∧
        kC.Invariant tr ∧
        kC.label tr = (client_label client xPk).join (server_label server yPk)
      ) ∨ (∃ spk, (LongTermKeys.label "SignedDH" server spk).isCorrupt tr.erase)
    )

end TraceInvariant

-- TODO: this whole section should be meta-programmable
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent)]
  [traceInv3: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState)]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState)]
  [traceInv5: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState)]
  [traceInv6: TraceInvariant.Has (LongTermKeys.ProofEntryT "SignedDH")]
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
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

attribute [local grind] ProtocolEvent.EventInv.invariant
attribute [local grind] SignedDHEventInv
attribute [local grind] ClientInitiateStateInv
attribute [local grind] ClientFinishStateInv
attribute [local grind] ServerFinishStateInv
attribute [local grind] Signature.SignPred.pred
attribute [local grind] SignedDHSignPred
attribute [local grind] PersistentLocalState.LocalStateInv.invariant
attribute [local grind] PersistentLocalState.CompromisableLocalStateInv.toLocalStateInv
attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

@[instance]
theorem client_initiate.spec (me: Participant):
  HoareTriple
    (client_initiate me)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold client_initiate
  step with ⟨ fun xSk => client_label me (DiffieHellman.dh_pk xSk), Usage.nothing ⟩
  step
  step
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  step
  grind

@[instance]
theorem server_receive.spec (me: Participant) (sk_ts: Nat) (msg_ts: Nat):
  HoareTriple
    (server_receive me sk_ts msg_ts)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold server_receive
  step
  step
  step_intro
  step
  step with ⟨ fun ySk => server_label me (DiffieHellman.dh_pk ySk), Usage.nothing ⟩
  step
  hoist
  step
  step
  step with ⟨ fun _ => Label.secret, Usage.nothing ⟩
  hoist
  step_intro
  step_intro -- interesting stuff: we will prove things on `sig` later on, because we need to log the event before
  step
  step_let sig with ⟨ mk_long_term_usage me ⟩
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    have: sig_msg.Publishable tr := by grind -- TODO how to infer this automatically?
    grind
  step
  grind

@[instance]
theorem client_finish.spec (me: Participant) (server: Participant) (pk_ts: Nat) (msg_ts: Nat) (sid: Nat):
  HoareTriple
    (client_finish me server pk_ts msg_ts sid)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold client_finish
  step
  step
  step
  split
  step
  step with ⟨ mk_long_term_usage server ⟩ by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  hoist
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step_intro
  step
  grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

instance: ∀ id, ReachableImpliesInvariant (reachability.internal id)
  | 0 => inferInstanceAs <| ReachableImpliesInvariant Network.reachability
  | 1 => inferInstanceAs <| ReachableImpliesInvariant (LongTermKeys.reachability "SignedDH")
  | 2 => .mk (fun me => client_initiate.spec me)
  | 3 => .mk (fun (me, sk_ts, msg_ts) => server_receive.spec me sk_ts msg_ts)
  | 4 => .mk (fun (me, server, pk_ts, msg_ts, sid) => client_finish.spec me server pk_ts msg_ts sid)

instance: ReachableImpliesInvariant reachability := inferInstanceAs (ReachableImpliesInvariant (.combine reachability.internal))

end ReachabilityImpliesInvariant

end DY.Example.SignedDH
