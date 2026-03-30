module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentGlobalState
public import DY.Actions.ProtocolEvent
public import DY.Actions.Network
public import DY.Comparse
import DY.Step

namespace DY.Compromise

section Execution

public
structure CompromiseEvent (StateT: Type) where
  state: StateT

@[expose]
public
def ExecEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => ProtocolEvent.ExecEntryT (CompromiseEvent StateT)

public
abbrev ExecEntryT (StateT: Type): Type :=
  ExecTraceTypes.combine (ExecEntryT.internal StateT)

public
instance (StateT: Type): ExecTraceTypes.HasStep (ProtocolEvent.ExecEntryT (CompromiseEvent StateT)) (ExecEntryT StateT) :=
  inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal StateT 0) (ExecTraceTypes.combine (ExecEntryT.internal StateT)))

public
def baseAttackerKnowledge.internal [BytesFunctor] [ExecTraceTypes] (StateT: Type): (id: Fin 1) → SubBaseAttackerKnowledge (ExecEntryT.internal StateT id)
  | 0 => ProtocolEvent.baseAttackerKnowledge (CompromiseEvent StateT)

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type): SubBaseAttackerKnowledge (ExecEntryT StateT) :=
  SubBaseAttackerKnowledge.combine (baseAttackerKnowledge.internal StateT)

public
def compromise
  (StateT: Type)
  [BytesFunctor]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has (PersistentGlobalState.ExecEntryT StateT)]
  [ExecTraceTypes.Has (ExecEntryT StateT)]
  (i: Nat)
  : Traceful Nat
:= do
  let state: StateT ← PersistentGlobalState.getGlobalState i
  ProtocolEvent.logEvent ({ state }: CompromiseEvent StateT)
  Network.sendMessage (Comparse.ParseableSerializeable.serialize state)

public
def GlobalStateCompromised
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  tr.EventLogged ({ state }: CompromiseEvent StateT)

public
theorem GlobalStateCompromised_le
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (state: StateT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    GlobalStateCompromised state tr1 →
    GlobalStateCompromised state tr2
:= by
  simp [GlobalStateCompromised]
  grind

grind_pattern GlobalStateCompromised_le => tr1 ≤ tr2, GlobalStateCompromised state tr1

end Execution

section Proof

@[expose]
public
def ProofEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => ProtocolEvent.ProofEntryT (CompromiseEvent StateT)

public
abbrev ProofEntryT (StateT: Type): Type :=
  TraceTypes.combine (ProofEntryT.internal StateT)

public
instance (StateT: Type): ∀ id, ErasableProofEntry (ExecEntryT.internal StateT id) (ProofEntryT.internal StateT id)
  | 0 => by dsimp only [ExecEntryT.internal, ProofEntryT.internal]; infer_instance

public
instance (StateT: Type): ErasableProofEntry (ExecEntryT StateT) (ProofEntryT StateT) :=
  (inferInstance: ErasableProofEntry (ExecTraceTypes.combine (ExecEntryT.internal StateT)) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance (StateT: Type): TraceTypes.HasStep (ProtocolEvent.ProofEntryT (CompromiseEvent StateT)) (ProofEntryT StateT) :=
  inferInstanceAs (TraceTypes.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  {StateT: Type}
  [TraceTypes]
  : ProtocolEvent.EventInv (CompromiseEvent StateT)
where
  invariant _ _ := True

public
instance [TraceTypes] (StateT: Type): ∀ id, ProofEntryInvariant (ProofEntryT.internal StateT id)
  | 0 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance [TraceTypes] (StateT: Type): ProofEntryInvariant (ProofEntryT StateT) :=
  (inferInstance: ProofEntryInvariant (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance [TraceTypes] (StateT: Type): TraceInvariant.HasStep (ProtocolEvent.ProofEntryT (CompromiseEvent StateT)) (ProofEntryT StateT) :=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [TraceTypes.Has (ProofEntryT StateT)]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal StateT id) (baseAttackerKnowledge.internal StateT id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply ProtocolEvent.baseAttackerKnowledgeTheorem

public
instance baseAttackerKnowledgeTheorem
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [TraceTypes.Has (ProofEntryT StateT)]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : SubBaseAttackerKnowledgeTheorem (ProofEntryT StateT) (baseAttackerKnowledge StateT)
:= by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  infer_instance

public
def label
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (state: StateT)
:=
  ProtocolEvent.label ({ state }: CompromiseEvent StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (state: StateT)
  (tr: ExecTrace)
  : (label state).isCorrupt tr = GlobalStateCompromised state tr
:= by
  grind [label, GlobalStateCompromised]

grind_pattern label_isCorrupt => (label state).isCorrupt tr

public
class CompromisableStateInv
  (StateT: Type)
  [TraceTypes]
  [BytesFunctor] [BytesInvariants]
  [Comparse.ParseableSerializeable StateT]
  [PersistentGlobalState.GlobalStateInv StateT]
  [ExecTraceTypes.Has (ExecEntryT StateT)]
where
  invariant_implies_KnowableBy:
    ∀ (state: StateT) tr,
      PersistentGlobalState.GlobalStateInv.invariant state tr →
      Comparse.isWellFormed (Bytes.KnowableBy (label state)) state tr

@[instance]
public
theorem compromise.spec
  {StateT: Type}
  [TraceInvariant]
  [BytesFunctor] [BytesInvariants] [BytesInvariantsProofs]
  [PersistentGlobalState.GlobalStateInv StateT]
  [Comparse.ParseableSerializeable StateT]
  [TraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
  [TraceTypes.Has (PersistentGlobalState.ProofEntryT StateT)] [TraceInvariant.Has (PersistentGlobalState.ProofEntryT StateT)]
  [TraceTypes.Has (ProofEntryT StateT)] [TraceInvariant.Has (ProofEntryT StateT)]
  [CompromisableStateInv StateT]
  (i: Nat)
  : HoareTriple
    (compromise StateT i)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold compromise
  step
  step by simp [ProtocolEvent.EventInv.invariant]
  step by
    have := CompromisableStateInv.invariant_implies_KnowableBy state tr
    have : (label state).isCorrupt tr.erase := by simp_all [label, ProtocolEvent.label_isCorrupt]
    grind [Comparse.isWellFormed, canFlowTrans]
  trivial

end Proof

end DY.Compromise
