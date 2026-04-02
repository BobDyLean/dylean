module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.Network -- for compromise
public import DY.Actions.ProtocolEvent -- for compromise
public import DY.Comparse -- for compromise
import DY.Step.Init

namespace DY.PersistentGlobalState

section State

section Execution

namespace State

public
structure ExecEntryT (StateT: Type) where
  st: StateT

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type): SubBaseAttackerKnowledge (ExecEntryT StateT) where
  attackerKnows _ _ _ := False

end State

public
def storeGlobalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (st: StateT)
  : Traceful Nat
:= do
  let entry: State.ExecEntryT StateT := { st }
  appendEntry entry

public
def getGlobalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (i: Nat)
  : Traceful StateT
:= do
  let e: State.ExecEntryT StateT ← getEntry i
  return e.st

end Execution

section Proof

public
class GlobalStateInv [TraceTypes] (StateT: Type) where
  invariant: StateT → ProofTrace → Prop
  invariant_later: ∀ st tr1 tr2,
    tr1 ≤ tr2 →
    invariant st tr1 →
    invariant st tr2

grind_pattern GlobalStateInv.invariant_later => tr1 ≤ tr2, GlobalStateInv.invariant st tr1
grind_pattern [grind_later] GlobalStateInv.invariant_later => tr1 ≤ tr2, GlobalStateInv.invariant st tr1

namespace State

public
abbrev ProofEntryT (StateT: Type) := ExecEntryT StateT

public
instance (StateT: Type): ErasableProofEntry (ExecEntryT StateT) (ProofEntryT StateT) := ErasableProofEntry.default (ExecEntryT StateT)

public
instance
  [TraceTypes]
  (StateT: Type)
  [GlobalStateInv StateT]
  : ProofEntryInvariant (ProofEntryT StateT)
where
  invariant tr entry :=
    GlobalStateInv.invariant entry.st tr

public
instance baseAttackerKnowledgeTheorem
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [TraceTypes.Has (ProofEntryT StateT)]
  [GlobalStateInv StateT]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : SubBaseAttackerKnowledgeTheorem (ProofEntryT StateT) (baseAttackerKnowledge StateT)
where
  pf trBefore entry b := by
    simp [baseAttackerKnowledge]

end State

@[instance]
public
theorem storeGlobalState.spec
  {StateT: Type}
  [TraceInvariant]
  [GlobalStateInv StateT]
  [TraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (st: StateT)
  : HoareTriple
    (storeGlobalState st)
    (fun tr => GlobalStateInv.invariant st tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold storeGlobalState
  dsimp only
  step with ⟨ fun _ => State.ExecEntryT.mk st ⟩ by simp_all [ErasableProofEntry.erase, ProofEntryInvariant.invariant]
  trivial

@[instance]
public
theorem getGlobalState.spec
  {StateT: Type}
  [TraceInvariant]
  [GlobalStateInv StateT]
  [TraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (i: Nat)
  : HoareTriple
    (getGlobalState i: Traceful StateT)
    (fun _ => True)
    (fun st tr => GlobalStateInv.invariant st tr)
:= by
  apply HoareTriple.mk
  unfold getGlobalState
  step
  have: GlobalStateInv.invariant e.st tr := by simp_all [ErasableProofEntry.erase, ProofEntryInvariant.invariant]; grind
  rename_i h; clear h
  step
  grind

end Proof

end State

section Compromise

section Execution

namespace Compromise

public
structure CompromiseEvent (StateT: Type) where
  state: StateT

@[expose]
public
def ExecEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => ProtocolEvent.ExecEntryT (CompromiseEvent StateT)

@[expose, implicit_reducible]
public
def ExecEntryT (StateT: Type): Type :=
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

end Compromise

public
def compromise
  (StateT: Type)
  [BytesFunctor]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (i: Nat)
  : Traceful Nat
:= do
  let state: StateT ← getGlobalState i
  ProtocolEvent.logEvent ({ state }: Compromise.CompromiseEvent StateT)
  Network.sendMessage (Comparse.ParseableSerializeable.serialize state)

public
def GlobalStateCompromised
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  tr.EventLogged ({ state }: Compromise.CompromiseEvent StateT)

public
theorem GlobalStateCompromised_le
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (state: StateT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    GlobalStateCompromised state tr1 →
    GlobalStateCompromised state tr2
:= by
  simp [GlobalStateCompromised]
  grind

grind_pattern GlobalStateCompromised_le => tr1 ≤ tr2, GlobalStateCompromised state tr1
grind_pattern [grind_later] GlobalStateCompromised_le => tr1 ≤ tr2, GlobalStateCompromised state tr1

end Execution

section Proof

namespace Compromise

@[expose]
public
def ProofEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => ProtocolEvent.ProofEntryT (Compromise.CompromiseEvent StateT)

@[expose, implicit_reducible]
public
def ProofEntryT (StateT: Type): Type :=
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
  apply instSubBaseAttackerKnowledgeTheoremCombine

end Compromise

public
def label
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (state: StateT)
:=
  ProtocolEvent.label ({ state }: Compromise.CompromiseEvent StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (state: StateT)
  (tr: ExecTrace)
  : (label state).isCorrupt tr = GlobalStateCompromised state tr
:= by
  grind [label, GlobalStateCompromised]

grind_pattern label_isCorrupt => (label state).isCorrupt tr

public
class CompromisableGlobalStateInv
  (StateT: Type)
  [TraceTypes]
  [BytesFunctor] [BytesInvariants]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
extends
  GlobalStateInv StateT
where
  invariant_implies_KnowableBy:
    ∀ (state: StateT) tr,
      GlobalStateInv.invariant state tr →
      Comparse.isWellFormed (Bytes.KnowableBy (label state)) state tr

@[instance]
public
theorem compromise.spec
  {StateT: Type}
  [BytesFunctor]
  [Comparse.ParseableSerializeable StateT]
  [TraceInvariant]
  [TraceTypes.Has Network.ProofEntryT]
  [TraceTypes.Has (State.ProofEntryT StateT)]
  [TraceTypes.Has (Compromise.ProofEntryT StateT)]
  [BytesInvariants] [BytesInvariantsProofs]
  [Comparse.ParseableSerializeable StateT]
  [CompromisableGlobalStateInv StateT]
  [TraceInvariant.Has Network.ProofEntryT]
  [TraceInvariant.Has (State.ProofEntryT StateT)]
  [TraceInvariant.Has (Compromise.ProofEntryT StateT)]
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
    have := CompromisableGlobalStateInv.invariant_implies_KnowableBy state tr
    have : (label state).isCorrupt tr.erase := by simp_all [label, ProtocolEvent.label_isCorrupt]
    grind [Comparse.isWellFormed, canFlowTrans]
  trivial

end Proof

end Compromise

section CompromisableState

namespace CompromisableState

@[expose]
public
def ExecEntryT.internal (StateT: Type): Fin 2 → Type
  | 0 => State.ExecEntryT StateT
  | 1 => Compromise.ExecEntryT StateT

@[expose, implicit_reducible]
public
def ExecEntryT (StateT: Type): Type :=
  ExecTraceTypes.combine (ExecEntryT.internal StateT)

public
instance (StateT: Type): ExecTraceTypes.HasStep (State.ExecEntryT StateT) (ExecEntryT StateT) :=
  inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal StateT 0) (ExecTraceTypes.combine (ExecEntryT.internal StateT)))

public
instance (StateT: Type): ExecTraceTypes.HasStep (Compromise.ExecEntryT StateT) (ExecEntryT StateT) :=
  inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal StateT 1) (ExecTraceTypes.combine (ExecEntryT.internal StateT)))

public
def baseAttackerKnowledge.internal [BytesFunctor] [ExecTraceTypes] (StateT: Type): (id: Fin 2) → SubBaseAttackerKnowledge (ExecEntryT.internal StateT id)
  | 0 => State.baseAttackerKnowledge StateT
  | 1 => Compromise.baseAttackerKnowledge StateT

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type): SubBaseAttackerKnowledge (ExecEntryT StateT) :=
  SubBaseAttackerKnowledge.combine (baseAttackerKnowledge.internal StateT)

@[expose]
public
def ProofEntryT.internal (StateT: Type): Fin 2 → Type
  | 0 => State.ProofEntryT StateT
  | 1 => Compromise.ProofEntryT StateT

@[expose, implicit_reducible]
public
def ProofEntryT (StateT: Type): Type :=
  TraceTypes.combine (ProofEntryT.internal StateT)

public
instance (StateT: Type): ∀ id, ErasableProofEntry (ExecEntryT.internal StateT id) (ProofEntryT.internal StateT id)
  | 0 | 1 => by dsimp only [ExecEntryT.internal, ProofEntryT.internal]; infer_instance

public
instance (StateT: Type): ErasableProofEntry (ExecEntryT StateT) (ProofEntryT StateT) :=
  (inferInstance: ErasableProofEntry (ExecTraceTypes.combine (ExecEntryT.internal StateT)) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance (StateT: Type): TraceTypes.HasStep (State.ProofEntryT StateT) (ProofEntryT StateT) :=
  inferInstanceAs (TraceTypes.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance (StateT: Type): TraceTypes.HasStep (Compromise.ProofEntryT StateT) (ProofEntryT StateT) :=
  inferInstanceAs (TraceTypes.HasStep (ProofEntryT.internal StateT 1) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
  : ∀ id, ProofEntryInvariant (ProofEntryT.internal StateT id)
  | 0 | 1 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
  : ProofEntryInvariant (ProofEntryT StateT)
:=
  (inferInstance: ProofEntryInvariant (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
  : TraceInvariant.HasStep (State.ProofEntryT StateT) (ProofEntryT StateT)
:=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
  : TraceInvariant.HasStep (Compromise.ProofEntryT StateT) (ProofEntryT StateT)
:=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 1) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT]
  [TraceTypes.Has (ProofEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal StateT id) (baseAttackerKnowledge.internal StateT id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply State.baseAttackerKnowledgeTheorem
  | 1 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Compromise.baseAttackerKnowledgeTheorem

public
instance baseAttackerKnowledgeTheorem
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT]
  [TraceTypes.Has (ProofEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : SubBaseAttackerKnowledgeTheorem (ProofEntryT StateT) (baseAttackerKnowledge StateT)
:= by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  apply instSubBaseAttackerKnowledgeTheoremCombine -- infer_instance?


end CompromisableState

end CompromisableState

end DY.PersistentGlobalState
