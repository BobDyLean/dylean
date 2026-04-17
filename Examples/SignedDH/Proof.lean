module

public import DY.Step
import DY.Step.Utils
public import Examples.SignedDH.Specification
import all Examples.SignedDH.Specification

namespace DY.Example.SignedDH

open DY.Comparse

-- TODO: this whole section should be meta-programmable
public section ProofTraceConfig

@[expose]
public
def ProofEntryT.internal: Fin 7 → Type
  | 0 => Network.ProofEntryT
  | 1 => Random.ProofEntryT
  | 2 => ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState
  | 6 => LongTermKeys.ProofEntryT "SignedDH"

public
abbrev ProofEntryT: Type :=
  ProofTraceTypes.combine ProofEntryT.internal

public
instance: ∀ id, ErasableProofEntry (ExecEntryT.internal id) (ProofEntryT.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => by dsimp only [ExecEntryT.internal, ProofEntryT.internal]; infer_instance

public
instance: ErasableProofEntry ExecEntryT ProofEntryT :=
  (inferInstance: ErasableProofEntry (ExecTraceTypes.combine ExecEntryT.internal) (ProofTraceTypes.combine ProofEntryT.internal))

instance: ProofTraceTypes.HasStep Network.ProofEntryT ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 0) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep Random.ProofEntryT ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 1) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 2) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 3) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 4) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 5) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (LongTermKeys.ProofEntryT "SignedDH") ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 6) (ProofTraceTypes.combine ProofEntryT.internal))

instance: ProofTraceTypes where
  ProofT := ProofEntryT
  tc := inferInstance

instance: ProofTraceTypes.Has ProofEntryT := inferInstanceAs (ProofTraceTypes.Has ProofTrace.Entry)

example: ProofTraceTypes.Has Network.ProofEntryT := inferInstance
example: ProofTraceTypes.Has Random.ProofEntryT := inferInstance
example: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) := inferInstance
example: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) := inferInstance
example: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) := inferInstance
example: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) := inferInstance
example: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "SignedDH") := inferInstance

end ProofTraceConfig

public section BytesInvariants

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

def invariants.internal: (id: Fin 6) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => Literal.invariants
  | 1 => Concat.invariants
  | 2 => Hash.invariants
  | 3 => Signature.invariants
  | 4 => DiffieHellman.invariants
  | 5 => Random.invariants

abbrev invariants: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

instance [BytesInvariants]: BytesInvariants.HasStep Literal.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Concat.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Hash.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 2) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Signature.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 3) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep DiffieHellman.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 4) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Random.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 5) invariants)

instance: BytesInvariants where
  invs := invariants

instance: BytesInvariants.Has invariants := inferInstance

example: BytesInvariants.Has Hash.invariants := inferInstance
example: BytesInvariants.Has Signature.invariants := inferInstance
example: BytesInvariants.Has DiffieHellman.invariants := inferInstance
example: BytesInvariants.Has Random.invariants := inferInstance

def invariantsProofs.internal: (id: Fin 6) → Bytes.PartialInvariantsProofs (invariants.internal id)
  | 0 => Literal.invariantsProofs
  | 1 => Concat.invariantsProofs
  | 2 => Hash.invariantsProofs
  | 3 => Signature.invariantsProofs
  | 4 => DiffieHellman.invariantsProofs
  | 5 => Random.invariantsProofs

abbrev invariantsProofs: Bytes.PartialInvariantsProofs invariants :=
  Bytes.PartialInvariantsProofs.combine invariantsProofs.internal

instance: BytesInvariantsProofs where
  pfs := invariantsProofs

end BytesInvariantsConfig

public section TraceInvariant

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

public
instance: ∀ id, SubTraceInvariant (ProofEntryT.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance: SubTraceInvariant ProofEntryT :=
  (inferInstance: SubTraceInvariant (ProofTraceTypes.combine ProofEntryT.internal))

instance : TraceInvariant where
  tc_inv := by dsimp only [ProofTrace.Entry, ProofTraceTypes.ProofT]; infer_instance

instance: TraceInvariant.Has ProofEntryT := inferInstanceAs (TraceInvariant.Has ProofTrace.Entry)

instance: TraceInvariant.HasStep Network.ProofEntryT ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 0) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep Random.ProofEntryT ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 1) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 2) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 3) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 4) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 5) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (LongTermKeys.ProofEntryT "SignedDH") ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 6) (ProofTraceTypes.combine ProofEntryT.internal))

example: TraceInvariant.Has Network.ProofEntryT := inferInstance
example: TraceInvariant.Has Random.ProofEntryT := inferInstance
example: TraceInvariant.Has (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) := inferInstance
example: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) := inferInstance
example: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) := inferInstance
example: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) := inferInstance
example: TraceInvariant.Has (LongTermKeys.ProofEntryT "SignedDH") := inferInstance

instance : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal id) (baseAttackerKnowledge.internal id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Network.baseAttackerKnowledgeTheorem
  | 1 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Random.baseAttackerKnowledgeTheorem
  | 2 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply ProtocolEvent.baseAttackerKnowledgeTheorem
  | 3 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 4 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 5 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 6 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply LongTermKeys.baseAttackerKnowledgeTheorem "SignedDH"

instance: SubBaseAttackerKnowledgeTheorem (ProofEntryT) (baseAttackerKnowledge) := by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  infer_instance

instance: BaseAttackerKnowledgeTheorem where
  pf := by
    dsimp only [ProofTrace.Entry, ProofTraceTypes.ProofT, BaseAttackerKnowledge.attackerKnows]
    -- TODO infer_instance
    exact instSubBaseAttackerKnowledgeTheoremExecEntryTProofEntryTBaseAttackerKnowledge

instance: (id: Fin 6) → SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem Literal.attackerKnowledge)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem Concat.attackerKnowledge)
  | 2 => inferInstanceAs (SubAttackerKnowledgeTheorem Hash.attackerKnowledge)
  | 3 => inferInstanceAs (SubAttackerKnowledgeTheorem Signature.attackerKnowledge)
  | 4 => inferInstanceAs (SubAttackerKnowledgeTheorem DiffieHellman.attackerKnowledge)
  | 5 => inferInstanceAs (SubAttackerKnowledgeTheorem Random.attackerKnowledge)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledgeTheorem where
  inst := inferInstanceAs (SubAttackerKnowledgeTheorem attackerKnowledge)

end TraceInvariantConfig

public section Proofs

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

instance: ∀ id, ReachableImpliesInvariant (reachability.internal id)
  | 0 => inferInstanceAs <| ReachableImpliesInvariant Network.reachability
  | 1 => inferInstanceAs <| ReachableImpliesInvariant (LongTermKeys.reachability "SignedDH")
  | 2 => .mk (fun me => client_initiate.spec me)
  | 3 => .mk (fun (me, sk_ts, msg_ts) => server_receive.spec me sk_ts msg_ts)
  | 4 => .mk (fun (me, server, pk_ts, msg_ts, sid) => client_finish.spec me server pk_ts msg_ts sid)

instance: ReachableImpliesInvariant reachability := inferInstanceAs (ReachableImpliesInvariant (.combine reachability.internal))

end ReachabilityImpliesInvariant

end DY.Example.SignedDH
