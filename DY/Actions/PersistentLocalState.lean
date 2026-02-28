module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentGlobalState
public import DY.Actions.Compromise
import DY.Step.Init

namespace DY.PersistentLocalState

public
abbrev Participant := String

public
structure LocalState (StateT: Type) where
  participant: Participant
  state: StateT

public
abbrev ExecEntryT (StateT: Type) := PersistentGlobalState.ExecEntryT (LocalState StateT)

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type) := PersistentGlobalState.baseAttackerKnowledge (LocalState StateT)

public
def ProofEntryT (StateT: Type) := PersistentGlobalState.ProofEntryT (LocalState StateT)

public
abbrev ProofEntryFunc (StateT: Type) := PersistentGlobalState.ProofEntryFunc (LocalState StateT)

public
class LocalStateInv [TraceTypes] (StateT: Type) where
  invariant: Participant → StateT → ProofTrace → Prop
  invariant_later: ∀ p st tr1 tr2,
    tr1 ≤ tr2 →
    invariant p st tr1 →
    invariant p st tr2

grind_pattern LocalStateInv.invariant_later => tr1 ≤ tr2, LocalStateInv.invariant p st tr1

public
instance
  [TraceTypes]
  (StateT: Type) [LocalStateInv StateT]
  : PersistentGlobalState.GlobalStateInv (LocalState StateT)
where
  invariant st tr := LocalStateInv.invariant st.participant st.state tr
  invariant_later st tr1 tr2 := LocalStateInv.invariant_later st.participant st.state tr1 tr2

public
abbrev Invariant [TraceTypes] (StateT: Type) [LocalStateInv StateT] := PersistentGlobalState.Invariant (LocalState StateT)

public
def baseAttackerKnowledgeTheorem [TraceInvariant] [BytesFunctor] [BytesInvariants] (StateT: Type) [TraceTypes.Has (ProofEntryFunc StateT)] [LocalStateInv StateT] [TraceInvariant.Has (Invariant StateT)] := PersistentGlobalState.baseAttackerKnowledgeTheorem (LocalState StateT)

public
def storeLocalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (participant: Participant) (state: StateT)
  : Traceful Nat
:= do
  PersistentGlobalState.storeGlobalState ({ participant, state }: LocalState StateT)

@[instance]
public
theorem storeLocalState.spec
  {StateT: Type}
  [TraceInvariant]
  [LocalStateInv StateT]
  [TraceTypes.Has (ProofEntryFunc StateT)] [TraceInvariant.Has (Invariant StateT)]
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

public
def getLocalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (participant: Participant) (i: Nat)
  : Traceful StateT
:= do
  let st: LocalState StateT ← PersistentGlobalState.getGlobalState i
  guard (st.participant = participant)
  return st.state

@[instance]
public
theorem getLocalState.spec
  {StateT: Type}
  [TraceInvariant]
  [LocalStateInv StateT]
  [TraceTypes.Has (ProofEntryFunc StateT)] [TraceInvariant.Has (Invariant StateT)]
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

public
def LocalStateCompromised
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (LocalState StateT)))] -- ugh
  (participant: Participant) (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  Compromise.GlobalStateCompromised ({ participant, state }: LocalState StateT) tr

public
theorem LocalStateCompromised_le
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (LocalState StateT)))] -- ugh
  (participant: Participant) (state: StateT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    LocalStateCompromised participant state tr1 →
    LocalStateCompromised participant state tr2
:= by
  simp [LocalStateCompromised]
  grind

grind_pattern LocalStateCompromised_le => tr1 ≤ tr2, LocalStateCompromised participant state tr1

public
def label
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (LocalState StateT)))] -- ugh
  (participant: Participant) (state: StateT)
:=
  Compromise.label ({ participant, state }: LocalState StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (LocalState StateT)))] -- ugh
  (participant: Participant) (state: StateT)
  (tr: ExecTrace)
  : (label participant state).isCorrupt tr = LocalStateCompromised participant state tr
:= by
  grind [label, LocalStateCompromised]

grind_pattern label_isCorrupt => (label participant state).isCorrupt tr

public
class CompromisableStateInv
  (StateT: Type)
  [TraceTypes]
  [BytesFunctor] [BytesInvariants]
  [Comparse.ParseableSerializeable StateT]
  [LocalStateInv StateT]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (LocalState StateT)))] -- ugh
where
  invariant_implies_KnowableBy:
    ∀ (participant: Participant) (state: StateT) tr,
      LocalStateInv.invariant participant state tr →
      Comparse.isWellFormed (Bytes.KnowableBy (label participant state)) state tr

noncomputable
instance
  [BytesFunctor]
  (StateT: Type)
  [Comparse.ParseableSerializeable StateT]: Comparse.ParseableSerializeable (LocalState StateT) := Comparse.comparseMetaProgramExists

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
  [LocalStateInv StateT]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (LocalState StateT)))] -- ugh
  [CompromisableStateInv StateT]
  : Compromise.CompromisableStateInv (LocalState StateT)
where
  invariant_implies_KnowableBy := by
    intro { participant, state } tr
    have := CompromisableStateInv.invariant_implies_KnowableBy participant state tr
    simp [PersistentGlobalState.GlobalStateInv.invariant]
    grind

end DY.PersistentLocalState
