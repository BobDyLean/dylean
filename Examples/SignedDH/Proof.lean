module

import DY.Meta.Step
import DY.Meta.Utils
public import Examples.SignedDH.Specification
import all Examples.SignedDH.Specification

namespace DY.Example.SignedDH

open DY.Comparse

-- Future work: the following section is boilerplate that could be meta-programmed
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTrace.Def]
  [traceProof0: ProofTrace.Has Network.TracePart.Proof]
  [traceProof1: ProofTrace.Has Random.TracePart.Proof]
  [traceProof2: ProofTrace.Has (ProtocolEvent.TracePart.Proof SignedDH.SignedDHEvent)]
  [traceProof3: ProofTrace.Has (PersistentLocalState.CompromisableState.TracePart.Proof SignedDH.ClientInitiateState)]
  [traceProof4: ProofTrace.Has (PersistentLocalState.CompromisableState.TracePart.Proof SignedDH.ClientFinishState)]
  [traceProof5: ProofTrace.Has (PersistentLocalState.CompromisableState.TracePart.Proof SignedDH.ServerFinishState)]
  [traceProof6: ProofTrace.Has (LongTermKeys.TracePart.Proof "SignedDH PKI")]

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

def clientLabel
  (me: Participant) (xPk: Bytes)
  : Label
where
  isCorrupt tr := ClientEphemeralStateCompromised me xPk tr

def serverLabel
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
def mkLongTermUsage (me: Participant): Usage := {
  type := "SigKey",
  tag := "SignedDH PKI",
  data := serialize ({ principal := me }: LongTermKeyUsage)
}

@[grind inj]
theorem mkLongTermUsage_inj:
  Function.Injective mkLongTermUsage
  := by
    simp [Function.Injective, mkLongTermUsage]
    grind

instance SignedDHSignPred
  : Signature.SignPred
where
  pred skUsg _vk msg tr :=
    ∃ server, skUsg = mkLongTermUsage server ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) => (
        ∃ ySk,
          msg.yPk = DiffieHellman.dhPk ySk ∧
          ySk.label tr = serverLabel server msg.yPk ∧
          tr.erase.EventLogged (SignedDHEvent.ServerFinishEvent server msg.xPk msg.yPk (Hash.hash (DiffieHellman.dh msg.xPk ySk)))
      )
    )

instance
  [Bytes.Invariants.Def]
  [Bytes.Invariants.Has DiffieHellman.DhPk.BytesPart.invariants]
  [Bytes.Invariants.Has Literal.BytesPart.invariants]
  [Bytes.Invariants.Has Concat.BytesPart.invariants]
  : Signature.SignPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman.dhPk.WellFormed]

end BytesInvariants

-- Future work: the following section is boilerplate that could be meta-programmed
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: Bytes.Invariants.Def]
  [bytesInvProof: Bytes.Invariants.Lawful]
  [bytesInv0: Bytes.Invariants.Has Random.BytesPart.invariants]
  [bytesInv1: Bytes.Invariants.Has Literal.BytesPart.invariants]
  [bytesInv2: Bytes.Invariants.Has Concat.BytesPart.invariants]
  [bytesInv3: Bytes.Invariants.Has Hash.BytesPart.invariants]
  [bytesInv4: Bytes.Invariants.Has Signature.BytesPart.invariants]
  [bytesInv5: Bytes.Invariants.Has DiffieHellman.BytesPart.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3
attribute [           scoped instance] HasBytesInvariants.bytesInv4
attribute [           scoped instance] HasBytesInvariants.bytesInv5

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

instance ClientInitiateStateInv : PersistentLocalState.CompromisableLocalStateInv ClientInitiateState
where
  invariant me st tr :=
    let { xPk, xSk } := st
    xPk = DiffieHellman.dhPk xSk ∧
    xPk.Publishable tr ∧
    xSk.Invariant tr ∧
    xSk.label tr = clientLabel me xPk
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (clientLabel participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, clientLabel, ClientEphemeralStateCompromised]
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
    (kC.label tr).canFlow (clientLabel me xPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (clientLabel participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, clientLabel, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

instance ServerFinishStateInv : PersistentLocalState.CompromisableLocalStateInv ServerFinishState
where
  invariant me st tr :=
    let { yPk, kS } := st
    yPk.Publishable tr ∧
    kS.Invariant tr ∧
    (kS.label tr).canFlow (serverLabel me yPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (serverLabel participant state.yPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, serverLabel, ServerEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

@[grind]
instance : LongTermKeys.ProofConfig "SignedDH PKI" mkLongTermUsage (LongTermKeys.label "SignedDH PKI")
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "SignedDH PKI" who vk ∧
    vk.SignkeyHasUsage (mkLongTermUsage who) tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

instance SignedDHEventInv : ProtocolEvent.EventInv (SignedDHEvent)
where
  invariant tr ev :=
    match ev with
    | SignedDHEvent.ClientInitiateEvent client xPk => (
      xPk.Invariant tr ∧
      xPk.dhSkLabel tr = clientLabel client xPk
    )
    | SignedDHEvent.ServerFinishEvent server xPk yPk kS => (
      kS.Invariant tr ∧
      xPk.Invariant tr ∧
      kS.label tr = (serverLabel server yPk).join (xPk.dhSkLabel tr)
    )
    | SignedDHEvent.ClientFinishEvent client server xPk yPk kC => (
      (
        tr.erase.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk kC) ∧
        kC.Invariant tr ∧
        kC.label tr = (clientLabel client xPk).join (serverLabel server yPk)
      ) ∨ (∃ spk, (LongTermKeys.label "SignedDH PKI" server spk).isCorrupt tr.erase)
    )

end TraceInvariant

-- Future work: the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: Trace.Invariant.Def]
  [traceInv0: Trace.Invariant.Has Network.TracePart.Proof]
  [traceInv1: Trace.Invariant.Has Random.TracePart.Proof]
  [traceInv2: Trace.Invariant.Has (ProtocolEvent.TracePart.Proof SignedDH.SignedDHEvent)]
  [traceInv3: Trace.Invariant.Has (PersistentLocalState.CompromisableState.TracePart.Proof SignedDH.ClientInitiateState)]
  [traceInv4: Trace.Invariant.Has (PersistentLocalState.CompromisableState.TracePart.Proof SignedDH.ClientFinishState)]
  [traceInv5: Trace.Invariant.Has (PersistentLocalState.CompromisableState.TracePart.Proof SignedDH.ServerFinishState)]
  [traceInv6: Trace.Invariant.Has (LongTermKeys.TracePart.Proof "SignedDH PKI")]
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
theorem Client.initiate.proof (me: Participant):
  HoareTriple
    (Client.initiate me)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Client.initiate
  step with ⟨ fun xSk => clientLabel me (DiffieHellman.dhPk xSk), Usage.nothing ⟩
  step
  step
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  step
  grind

@[instance]
theorem Server.receive.proof (me: Participant) (skHandle: Nat) (msgHandle: Nat):
  HoareTriple
    (Server.receive me skHandle msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Server.receive
  step
  step
  step_intro
  step
  step with ⟨ fun ySk => serverLabel me (DiffieHellman.dhPk ySk), Usage.nothing ⟩
  step
  hoist
  step
  step
  step with ⟨ fun _ => Label.secret, Usage.nothing ⟩
  hoist
  step_intro
  step_intro -- interesting stuff: we will prove things on `sig` later on, because we need to log the event before
  step
  step_let sig with ⟨ mkLongTermUsage me ⟩
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    have: sig_msg.Publishable tr := by grind -- TODO how to infer this automatically?
    grind
  step
  grind

@[instance]
theorem Client.finish.proof (me: Participant) (server: Participant) (pkHandle: Nat) (msgHandle: Nat) (stHandle: Nat):
  HoareTriple
    (Client.finish me server pkHandle msgHandle stHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Client.finish
  step
  step
  step
  split
  step
  step with ⟨ mkLongTermUsage server ⟩ by
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
  grind

@[instance]
theorem ClientInitiateState.compromise.proof (stHandle: Nat): HoareTriple (ClientInitiateState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ClientInitiateState.compromise; step; grind

@[instance]
theorem ClientFinishState.compromise.proof (stHandle: Nat): HoareTriple (ClientFinishState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ClientFinishState.compromise; step; grind

@[instance]
theorem ServerFinishState.compromise.proof (stHandle: Nat): HoareTriple (ServerFinishState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ServerFinishState.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

public instance: Trace.Reachable_implies_Invariant.Part Client.initiate.transition := .mk (fun me => Client.initiate.proof me)
public instance: Trace.Reachable_implies_Invariant.Part Server.receive.transition := .mk (fun (me, skHandle, msgHandle) => Server.receive.proof me skHandle msgHandle)
public instance: Trace.Reachable_implies_Invariant.Part Client.finish.transition := .mk (fun (me, server, pkHandle, msgHandle, stHandle) => Client.finish.proof me server pkHandle msgHandle stHandle)
public instance: Trace.Reachable_implies_Invariant.Part ClientInitiateState.compromise.transition := .mk (fun (stHandle) => ClientInitiateState.compromise.proof stHandle)
public instance: Trace.Reachable_implies_Invariant.Part ClientFinishState.compromise.transition := .mk (fun (stHandle) => ClientFinishState.compromise.proof stHandle)
public instance: Trace.Reachable_implies_Invariant.Part ServerFinishState.compromise.transition := .mk (fun (stHandle) => ServerFinishState.compromise.proof stHandle)

#combine into Trace.Reachable_implies_Invariant from
  Network,
  Random,
  LongTermKeys "SignedDH PKI",
  Client.initiate,
  Server.receive,
  Client.finish,
  ClientInitiateState.compromise,
  ClientFinishState.compromise,
  ServerFinishState.compromise,

end ReachabilityImpliesInvariant

end DY.Example.SignedDH
