module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentGlobalState
import DY.Step.Init

namespace DY

public
abbrev Participant := String

namespace PersistentLocalState

section State

section Execution

public
structure LocalState (StateT: Type) where
  participant: Participant
  state: StateT

noncomputable
instance
  [BytesFunctor]
  (StateT: Type)
  [Comparse.ParseableSerializeable StateT]: Comparse.ParseableSerializeable (LocalState StateT) := Comparse.comparseMetaProgramExists

namespace State

@[expose]
public
def ExecEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => PersistentGlobalState.State.ExecEntryT (LocalState StateT)

@[expose, implicit_reducible]
public
def ExecEntryT (StateT: Type): Type :=
  ExecTraceTypes.combine (ExecEntryT.internal StateT)

public
instance (StateT: Type): ExecTraceTypes.HasStep (PersistentGlobalState.State.ExecEntryT (LocalState StateT)) (ExecEntryT StateT) :=
  inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal StateT 0) (ExecTraceTypes.combine (ExecEntryT.internal StateT)))

public
def baseAttackerKnowledge.internal [BytesFunctor] [ExecTraceTypes] (StateT: Type): (id: Fin 1) → SubBaseAttackerKnowledge (ExecEntryT.internal StateT id)
  | 0 => PersistentGlobalState.State.baseAttackerKnowledge (LocalState StateT)

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type): SubBaseAttackerKnowledge (ExecEntryT StateT) :=
  SubBaseAttackerKnowledge.combine (baseAttackerKnowledge.internal StateT)

end State

public
def storeLocalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (participant: Participant) (state: StateT)
  : Traceful Nat
:= do
  PersistentGlobalState.storeGlobalState ({ participant, state }: LocalState StateT)

public
def getLocalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (participant: Participant) (i: Nat)
  : Traceful StateT
:= do
  let st: LocalState StateT ← PersistentGlobalState.getGlobalState i
  guard (st.participant = participant)
  return st.state

end Execution

section Proof

public
class LocalStateInv [TraceTypes] (StateT: Type) where
  invariant: Participant → StateT → ProofTrace → Prop
  invariant_later: ∀ p st tr1 tr2,
    tr1 ≤ tr2 →
    invariant p st tr1 →
    invariant p st tr2

grind_pattern LocalStateInv.invariant_later => tr1 ≤ tr2, LocalStateInv.invariant p st tr1
grind_pattern [grind_later] LocalStateInv.invariant_later => tr1 ≤ tr2, LocalStateInv.invariant p st tr1

namespace State

@[expose]
public
def ProofEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => PersistentGlobalState.State.ProofEntryT (LocalState StateT)

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
instance (StateT: Type): TraceTypes.HasStep (PersistentGlobalState.State.ProofEntryT (LocalState StateT)) (ProofEntryT StateT) :=
  inferInstanceAs (TraceTypes.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceTypes]
  (StateT: Type) [LocalStateInv StateT]
  : PersistentGlobalState.GlobalStateInv (LocalState StateT)
where
  invariant st tr := LocalStateInv.invariant st.participant st.state tr
  invariant_later st tr1 tr2 := LocalStateInv.invariant_later st.participant st.state tr1 tr2

public
instance [TraceTypes] (StateT: Type) [LocalStateInv StateT]: ∀ id, SubTraceInvariant (ProofEntryT.internal StateT id)
  | 0 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance [TraceTypes] (StateT: Type) [LocalStateInv StateT]: SubTraceInvariant (ProofEntryT StateT) :=
  (inferInstance: SubTraceInvariant (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance [TraceTypes] (StateT: Type) [LocalStateInv StateT]: TraceInvariant.HasStep (PersistentGlobalState.State.ProofEntryT (LocalState StateT)) (ProofEntryT StateT) :=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [LocalStateInv StateT]
  [TraceTypes.Has (ProofEntryT StateT)]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal StateT id) (baseAttackerKnowledge.internal StateT id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentGlobalState.State.baseAttackerKnowledgeTheorem

public
instance baseAttackerKnowledgeTheorem
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [LocalStateInv StateT]
  [TraceTypes.Has (ProofEntryT StateT)]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : SubBaseAttackerKnowledgeTheorem (ProofEntryT StateT) (baseAttackerKnowledge StateT)
:= by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  apply instSubBaseAttackerKnowledgeTheoremCombine

end State

@[instance]
public
theorem storeLocalState.spec
  {StateT: Type}
  [TraceInvariant]
  [LocalStateInv StateT]
  [TraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (participant: Participant) (state: StateT)
  : HoareTriple
    (storeLocalState participant state)
    (fun tr => LocalStateInv.invariant participant state tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold storeLocalState
  step by simp_all [PersistentGlobalState.GlobalStateInv.invariant]
  trivial

@[instance]
public
theorem getLocalState.spec
  {StateT: Type}
  [TraceInvariant]
  [LocalStateInv StateT]
  [TraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (participant: Participant) (i: Nat)
  : HoareTriple
    (getLocalState participant i: Traceful StateT)
    (fun _ => True)
    (fun st tr => LocalStateInv.invariant participant st tr)
:= by
  apply HoareTriple.mk
  unfold getLocalState
  step
  step
  step
  simp_all [PersistentGlobalState.GlobalStateInv.invariant]

end Proof

end State

section Compromise

section Execution

namespace Compromise

@[expose]
public
def ExecEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => PersistentGlobalState.Compromise.ExecEntryT (LocalState StateT)

@[expose, implicit_reducible]
public
def ExecEntryT (StateT: Type): Type :=
  ExecTraceTypes.combine (ExecEntryT.internal StateT)

public
instance (StateT: Type): ExecTraceTypes.HasStep (PersistentGlobalState.Compromise.ExecEntryT (LocalState StateT)) (ExecEntryT StateT) :=
  inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal StateT 0) (ExecTraceTypes.combine (ExecEntryT.internal StateT)))

public
def baseAttackerKnowledge.internal [BytesFunctor] [ExecTraceTypes] (StateT: Type): (id: Fin 1) → SubBaseAttackerKnowledge (ExecEntryT.internal StateT id)
  | 0 => PersistentGlobalState.Compromise.baseAttackerKnowledge (LocalState StateT)

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type): SubBaseAttackerKnowledge (ExecEntryT StateT) :=
  SubBaseAttackerKnowledge.combine (baseAttackerKnowledge.internal StateT)

end Compromise

public
noncomputable
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
  PersistentGlobalState.compromise (LocalState StateT) i

public
def LocalStateCompromised
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant: Participant) (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  PersistentGlobalState.GlobalStateCompromised ({ participant, state }: LocalState StateT) tr

public
theorem LocalStateCompromised_le
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant: Participant) (state: StateT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    LocalStateCompromised participant state tr1 →
    LocalStateCompromised participant state tr2
:= by
  simp [LocalStateCompromised]
  grind

grind_pattern LocalStateCompromised_le => tr1 ≤ tr2, LocalStateCompromised participant state tr1
grind_pattern [grind_later] LocalStateCompromised_le => tr1 ≤ tr2, LocalStateCompromised participant state tr1

end Execution

section Proof

namespace Compromise

@[expose]
public
def ProofEntryT.internal (StateT: Type): Fin 1 → Type
  | 0 => PersistentGlobalState.Compromise.ProofEntryT (LocalState StateT)

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
instance (StateT: Type): TraceTypes.HasStep (PersistentGlobalState.Compromise.ProofEntryT (LocalState StateT)) (ProofEntryT StateT) :=
  inferInstanceAs (TraceTypes.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance [TraceTypes] (StateT: Type): ∀ id, SubTraceInvariant (ProofEntryT.internal StateT id)
  | 0 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance [TraceTypes] (StateT: Type): SubTraceInvariant (ProofEntryT StateT) :=
  (inferInstance: SubTraceInvariant (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance [TraceTypes] (StateT: Type): TraceInvariant.HasStep (PersistentGlobalState.Compromise.ProofEntryT (LocalState StateT)) (ProofEntryT StateT) :=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [TraceTypes.Has (ProofEntryT StateT)]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal StateT id) (baseAttackerKnowledge.internal StateT id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentGlobalState.Compromise.baseAttackerKnowledgeTheorem

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
  (participant: Participant) (state: StateT)
:=
  PersistentGlobalState.label ({ participant, state }: LocalState StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant: Participant) (state: StateT)
  (tr: ExecTrace)
  : (label participant state).isCorrupt tr = LocalStateCompromised participant state tr
:= by
  grind [label, LocalStateCompromised]

grind_pattern label_isCorrupt => (label participant state).isCorrupt tr

public
class CompromisableLocalStateInv
  (StateT: Type)
  [TraceTypes]
  [BytesFunctor] [BytesInvariants]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
extends
  LocalStateInv StateT
where
  invariant_implies_KnowableBy:
    ∀ (participant: Participant) (state: StateT) tr,
      LocalStateInv.invariant participant state tr →
      Comparse.isWellFormed (Bytes.KnowableBy (label participant state)) state tr

axiom LocalState.isWellFormedLemma
  [BytesFunctor]
  {StateT: Type} [Comparse.ParseableSerializeable StateT]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatible pre]
  (x: LocalState StateT) (tr: τ):
  Comparse.isWellFormed pre x tr = Comparse.isWellFormed pre x.state tr

grind_pattern LocalState.isWellFormedLemma => Comparse.isWellFormed pre x tr

instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  [CompromisableLocalStateInv StateT]
  : PersistentGlobalState.CompromisableGlobalStateInv (LocalState StateT)
where
  invariant_implies_KnowableBy := by
    intro { participant, state } tr
    have := CompromisableLocalStateInv.invariant_implies_KnowableBy participant state tr
    simp [label] at this
    simp [PersistentGlobalState.GlobalStateInv.invariant]
    grind

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
  [CompromisableLocalStateInv StateT]
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
  [CompromisableLocalStateInv StateT]
  : ∀ id, SubTraceInvariant (ProofEntryT.internal StateT id)
  | 0 | 1 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableLocalStateInv StateT]
  : SubTraceInvariant (ProofEntryT StateT)
:=
  (inferInstance: SubTraceInvariant (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableLocalStateInv StateT]
  : TraceInvariant.HasStep (State.ProofEntryT StateT) (ProofEntryT StateT)
:=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 0) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceTypes] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableLocalStateInv StateT]
  : TraceInvariant.HasStep (Compromise.ProofEntryT StateT) (ProofEntryT StateT)
:=
  inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal StateT 1) (TraceTypes.combine (ProofEntryT.internal StateT)))

public
instance
  [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type) [Comparse.ParseableSerializeable StateT]
  [TraceTypes.Has (ProofEntryT StateT)]
  [CompromisableLocalStateInv StateT]
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
  [CompromisableLocalStateInv StateT]
  [TraceInvariant.Has (ProofEntryT StateT)]
  : SubBaseAttackerKnowledgeTheorem (ProofEntryT StateT) (baseAttackerKnowledge StateT)
:= by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  apply instSubBaseAttackerKnowledgeTheoremCombine -- infer_instance?

end CompromisableState

end CompromisableState

end DY.PersistentLocalState
