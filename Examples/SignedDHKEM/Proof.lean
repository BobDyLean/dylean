module

import DY.Meta
public import Examples.SignedDHKEM.Specification
import all Examples.SignedDHKEM.Specification

namespace DY.Example.SignedDHKEM

open DY.Comparse

-- TODO: this whole section should be meta-programmable
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SignedDHKEMEvent)]
  [traceProof3: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateDHState)]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateKEMState)]
  [traceProof5: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientFinishState)]
  [traceProof6: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerFinishState)]
  [traceProof7: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "SignedDHKEM PKI")]
  [traceProof8: ProofTraceTypes.Has (KEM.Broken.ProofEntryT)]
  [traceProof9: ProofTraceTypes.Has (DiffieHellman'.Broken.ProofEntryT)]
  [traceProof10: ProofTraceTypes.Has (Signature'.Broken.ProofEntryT)]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4
attribute [reducible, scoped instance] HasProofTrace.traceProof5
attribute [reducible, scoped instance] HasProofTrace.traceProof6
attribute [reducible, scoped instance] HasProofTrace.traceProof7
attribute [reducible, scoped instance] HasProofTrace.traceProof8
attribute [reducible, scoped instance] HasProofTrace.traceProof9
attribute [reducible, scoped instance] HasProofTrace.traceProof10

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

def clientDhLabel
  (me: Participant) (xPk: Bytes)
  : Label
where
  isCorrupt tr := ClientEphemeralDHStateCompromised me xPk tr


def clientKemLabel
  (me: Participant) (zPk: Bytes)
  : Label
where
  isCorrupt tr := ClientEphemeralKEMStateCompromised me zPk tr

def serverLabel
  (me: Participant) (xPk yPk zPk: Bytes)
  : Label
where
  isCorrupt tr := ServerEphemeralStateCompromised me xPk yPk zPk tr

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
  tag := "SignedDHKEM PKI",
  data := serialize ({ principal := me }: LongTermKeyUsage)
}

@[grind inj]
theorem mkLongTermUsage_inj:
  Function.Injective mkLongTermUsage
  := by
    simp [Function.Injective, mkLongTermUsage]
    grind

instance SignedDHKEMSignPred
  : Signature'.SignPred
where
  pred skUsg vk msg tr :=
    ∃ server, skUsg = mkLongTermUsage server ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) => (
        ∃ ySk entropy,
          let dhss := DiffieHellman'.dh msg.xPk ySk
          let encapResult := KEM.kemEncap msg.zPk entropy
          msg.yPk = DiffieHellman'.dh_pk ySk ∧
          ySk.label tr = (serverLabel server msg.xPk msg.yPk msg.zPk).join (DiffieHellman'.Broken.label msg.yPk) ∧
          msg.ct = encapResult.fst ∧
          entropy.WellFormed tr ∧
          entropy.label tr = (serverLabel server msg.xPk msg.yPk msg.zPk).join (msg.zPk.kemSkLabel tr) ∧
          tr.erase.EventLogged (SignedDHKEMEvent.ServerFinishEvent server msg.xPk msg.yPk msg.zPk (Hash.hash (Concat.concat dhss encapResult.snd)))
      )
    )

instance
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman'.DhPk.invariants]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  [BytesInvariants.Has KEM.invariants]
  : Signature'.SignPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman'.dh_pk.WellFormed]

end BytesInvariants

-- TODO: this whole section should be meta-programmable
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInvProof: BytesInvariantsProofs]
  [bytesInv0: BytesInvariants.Has Random.invariants]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has Hash.invariants]
  [bytesInv4: BytesInvariants.Has Signature'.invariants]
  [bytesInv5: BytesInvariants.Has DiffieHellman'.invariants]
  [bytesInv6: BytesInvariants.Has KEM.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
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

instance ClientInitiateDHStateInv : PersistentLocalState.CompromisableLocalStateInv ClientInitiateDHState
where
  invariant me st tr :=
    let { xPk, xSk } := st
    xPk = DiffieHellman'.dh_pk xSk ∧
    xPk.Publishable tr ∧
    xSk.Invariant tr ∧
    xSk.label tr = (clientDhLabel me xPk).join (DiffieHellman'.Broken.label xPk)
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: ((clientDhLabel participant state.xPk).join (DiffieHellman'.Broken.label state.xPk)).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, clientDhLabel, ClientEphemeralDHStateCompromised]
      grind
    grind [canFlowTrans]

-- for monotonicity
theorem ClientInitiateDHStateInv_imp_Invariant
  (participant: Participant) (st: ClientInitiateDHState)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.xSk.Invariant tr ∧
      st.xPk.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] ClientInitiateDHStateInv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr

instance ClientInitiateKEMStateInv : PersistentLocalState.CompromisableLocalStateInv ClientInitiateKEMState
where
  invariant me st tr :=
    let { zPk, zSk } := st
    zPk = KEM.kemPk zSk ∧
    zPk.Publishable tr ∧
    zSk.Invariant tr ∧
    zSk.label tr = (clientKemLabel me zPk).join (KEM.Broken.label zPk)
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: ((clientKemLabel participant state.zPk).join (KEM.Broken.label state.zPk)).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, clientKemLabel, ClientEphemeralKEMStateCompromised]
      grind
    grind [canFlowTrans]

-- for monotonicity
theorem ClientInitiateKEMStateInv_imp_Invariant
  (participant: Participant) (st: ClientInitiateKEMState)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.zSk.Invariant tr ∧
      st.zPk.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] ClientInitiateKEMStateInv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr


instance ClientFinishStateInv : PersistentLocalState.CompromisableLocalStateInv ClientFinishState
where
  invariant me st tr :=
    let { xPk, zPk, kC } := st
    xPk.Publishable tr ∧
    zPk.Publishable tr ∧
    kC.Invariant tr ∧
    (kC.label tr).canFlow ((clientDhLabel me xPk).meet (clientKemLabel me zPk)) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: ((clientDhLabel participant state.xPk).meet (clientKemLabel participant state.zPk)).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, clientDhLabel, clientKemLabel, ClientEphemeralDHStateCompromised, ClientEphemeralKEMStateCompromised, PersistentLocalState.label_isCorrupt]
      grind
    grind [canFlowTrans]

instance ServerFinishStateInv : PersistentLocalState.CompromisableLocalStateInv ServerFinishState
where
  invariant me st tr :=
    let { xPk, yPk, zPk, kS } := st
    xPk.Publishable tr ∧
    yPk.Publishable tr ∧
    zPk.Publishable tr ∧
    kS.Invariant tr ∧
    (kS.label tr).canFlow (serverLabel me xPk yPk zPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (serverLabel participant state.xPk state.yPk state.zPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, serverLabel, ServerEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

def mkLongTermLabel (p: Participant) (vk: Bytes): Label :=
  (LongTermKeys.label "SignedDHKEM PKI" p vk).join (Signature'.Broken.label vk)

@[grind]
instance : LongTermKeys.ProofConfig "SignedDHKEM PKI" mkLongTermUsage mkLongTermLabel
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel' tr = mkLongTermLabel who vk ∧
    vk.SignkeyHasUsage' (mkLongTermUsage who) tr

  label_canFlow := by simp [mkLongTermLabel]; grind

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind [Signature'.vk.Invariant, mkLongTermLabel]

instance SignedDHKEMEventInv : ProtocolEvent.EventInv (SignedDHKEMEvent)
where
  invariant tr ev :=
    match ev with
    | .ClientInitiateEvent client xPk zPk => (
      xPk.Invariant tr ∧
      xPk.dhSkLabel' tr = (clientDhLabel client xPk).join (DiffieHellman'.Broken.label xPk)
    )
    | .ServerFinishEvent server xPk yPk zPk kS => (
      kS.Invariant tr ∧
      xPk.Invariant tr ∧
      kS.label tr = (((serverLabel server xPk yPk zPk).join (DiffieHellman'.Broken.label yPk)).join (xPk.dhSkLabel' tr)).meet ((serverLabel server xPk yPk zPk).join (zPk.kemSkLabel tr))
    )
    | .ClientFinishEvent client server xPk yPk zPk kC => (
      (
        tr.erase.EventLogged (SignedDHKEMEvent.ServerFinishEvent server xPk yPk zPk kC) ∧
        kC.Invariant tr ∧
        kC.label tr = (((clientDhLabel client xPk).join (DiffieHellman'.Broken.label xPk)).join ((serverLabel server xPk yPk zPk).join (DiffieHellman'.Broken.label yPk))).meet (((clientKemLabel client zPk).join (KEM.Broken.label zPk)).join (serverLabel server xPk yPk zPk))
      ) ∨ (∃ spk, (mkLongTermLabel server spk).isCorrupt tr.erase)
    )

end TraceInvariant

-- TODO: this whole section should be meta-programmable
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT SignedDHKEMEvent)]
  [traceInv3: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateDHState)]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateKEMState)]
  [traceInv5: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientFinishState)]
  [traceInv6: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerFinishState)]
  [traceInv7: TraceInvariant.Has (LongTermKeys.ProofEntryT "SignedDHKEM PKI")]
  [traceInv8: TraceInvariant.Has KEM.Broken.ProofEntryT]
  [traceInv9: TraceInvariant.Has DiffieHellman'.Broken.ProofEntryT]
  [traceInv10: TraceInvariant.Has Signature'.Broken.ProofEntryT]
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
attribute [           scoped instance] HasTraceInvariant.traceInv8
attribute [           scoped instance] HasTraceInvariant.traceInv9
attribute [           scoped instance] HasTraceInvariant.traceInv10
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

attribute [local grind] ProtocolEvent.EventInv.invariant
attribute [local grind] SignedDHKEMEventInv
attribute [local grind] ClientInitiateDHStateInv
attribute [local grind] ClientInitiateKEMStateInv
attribute [local grind] ClientFinishStateInv
attribute [local grind] ServerFinishStateInv
attribute [local grind] Signature'.SignPred.pred
attribute [local grind] SignedDHKEMSignPred
attribute [local grind] PersistentLocalState.LocalStateInv.invariant
attribute [local grind] PersistentLocalState.CompromisableLocalStateInv.toLocalStateInv
attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

@[instance]
theorem Client.initiate.spec (me: Participant):
  HoareTriple
    (Client.initiate me)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Client.initiate
  step with ⟨ fun xSk => (clientDhLabel me (DiffieHellman'.dh_pk xSk)).join (DiffieHellman'.Broken.label (DiffieHellman'.dh_pk xSk)), Usage.nothing ⟩
  step
  step with ⟨ fun zSk => (clientKemLabel me (KEM.kemPk zSk)).join (KEM.Broken.label (KEM.kemPk zSk)), Usage.nothing ⟩
  step
  step
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  step
  grind

instance (lhs rhs: Bytes):
  HoareTriplePure
    (Concat.concat lhs rhs)
    (fun tr =>
      lhs.Invariant tr ∧
      rhs.Invariant tr
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = (lhs.label tr).meet (rhs.label tr)
    )
where
  pf tr pre := by simp_all

@[instance]
theorem Server.receive.spec (me: Participant) (skHandle: Nat) (msgHandle: Nat):
  HoareTriple
    (Server.receive me skHandle msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Server.receive
  step
  step
  step_intro
  step_intro
  step
  step with ⟨ fun ySk => (serverLabel me xPk (DiffieHellman'.dh_pk ySk) zPk).join (DiffieHellman'.Broken.label (DiffieHellman'.dh_pk ySk)), Usage.nothing ⟩
  step
  step
  step with ⟨ fun entropy => (serverLabel me xPk (DiffieHellman'.dh_pk ySk) zPk).join (zPk.kemSkLabel tr), Usage.nothing ⟩
  step
  dsimp -zeta at *
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
    have: (dhss.label tr).canFlow (ySk.label tr) tr.erase := by grind
    grind
  step by
    have: sig_msg.Publishable tr := by grind -- TODO how to infer this automatically?
    grind
  step
  grind

@[instance]
theorem Client.finish.spec (me: Participant) (server: Participant) (pkHandle: Nat) (msgHandle: Nat) (dhStHandle: Nat) (kemStHandle: Nat):
  HoareTriple
    (Client.finish me server pkHandle msgHandle dhStHandle kemStHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold Client.finish
  step
  step
  step
  split
  step
  split
  rename_i zPk zSk _
  step
  step with ⟨ mkLongTermUsage server ⟩ by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  hoist
  step
  step
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    simp only [ProtocolEvent.EventInv.invariant]
    have:
      ∀ entropy,
        let (ct, ss) := KEM.kemEncap (KEM.kemPk zSk) entropy
        ss.label tr = entropy.label tr ∧
        KEM.kemDecap zSk ct = some ss
    := by
      intro entropy
      -- should these be grind patterns?
      have := KEM.kemEncap.ss_label (KEM.kemPk zSk) entropy
      have := KEM.kemDecap_kemEncap zSk entropy
      grind
    grind
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant, Label.canFlow]
    grind
  step
  grind

@[instance]
theorem ClientInitiateDHState.compromise.spec (stHandle: Nat): HoareTriple (ClientInitiateDHState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ClientInitiateDHState.compromise; step; grind

@[instance]
theorem ClientInitiateKEMState.compromise.spec (stHandle: Nat): HoareTriple (ClientInitiateKEMState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ClientInitiateKEMState.compromise; step; grind

@[instance]
theorem ClientFinishState.compromise.spec (stHandle: Nat): HoareTriple (ClientFinishState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ClientFinishState.compromise; step; grind

@[instance]
theorem ServerFinishState.compromise.spec (stHandle: Nat): HoareTriple (ServerFinishState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ServerFinishState.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

public instance: ReachableImpliesInvariant Client.initiate.reachability := .mk (fun me => Client.initiate.spec me)
public instance: ReachableImpliesInvariant Server.receive.reachability := .mk (fun (me, skHandle, msgHandle) => Server.receive.spec me skHandle msgHandle)
public instance: ReachableImpliesInvariant Client.finish.reachability := .mk (fun (me, server, pkHandle, msgHandle, dhStHandle, kemStHandle) => Client.finish.spec me server pkHandle msgHandle dhStHandle kemStHandle)
public instance: ReachableImpliesInvariant ClientInitiateDHState.compromise.reachability := .mk (fun (stHandle) => ClientInitiateDHState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant ClientInitiateKEMState.compromise.reachability := .mk (fun (stHandle) => ClientInitiateKEMState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant ClientFinishState.compromise.reachability := .mk (fun (stHandle) => ClientFinishState.compromise.spec stHandle)
public instance: ReachableImpliesInvariant ServerFinishState.compromise.reachability := .mk (fun (stHandle) => ServerFinishState.compromise.spec stHandle)

#combine into ReachabilityTheorem from
  Network,
  LongTermKeys "SignedDHKEM PKI",
  Client.initiate,
  Server.receive,
  Client.finish,
  ClientInitiateDHState.compromise,
  ClientInitiateKEMState.compromise,
  ClientFinishState.compromise,
  ServerFinishState.compromise,
  KEM.Broken.breakKemPk,
  DiffieHellman'.Broken.breakDhPk,
  Signature'.Broken.breakVk,

end ReachabilityImpliesInvariant

end DY.Example.SignedDHKEM
