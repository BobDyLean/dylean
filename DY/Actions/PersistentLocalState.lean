module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentGlobalState
import DY.Meta.Step

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

public -- it is useful to implement attacker programs
instance
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (StateT: Type)
  [Comparse.ParseableSerializeable StateT]
  : Comparse.ParseableSerializeable (LocalState StateT)
:= .make <|
  .triviallyIsomorphic
    (.prod .slowString Comparse.ParseableSerializeable.mf)
    (fun ⟨ participant, state ⟩ => { participant, state })
    (fun { participant, state } => ⟨ participant, state ⟩)

public -- it is useful to implement attacker programs
theorem LocalState.IsWellFormed_eq
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  {StateT: Type} [Comparse.ParseableSerializeable StateT]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: LocalState StateT) (tr: τ):
  Comparse.IsWellFormed pre x tr = Comparse.IsWellFormed pre x.state tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern LocalState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

namespace State

#combine (StateT: Type) into ExecEntryT, baseAttackerKnowledge from
  PersistentGlobalState.State (LocalState StateT)

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
  (participant: Participant) (handle: Nat)
  : Traceful StateT
:= do
  let st: LocalState StateT ← PersistentGlobalState.getGlobalState handle
  guard (st.participant = participant)
  return st.state

end Execution

section Proof

public
class LocalStateInv [ExecTraceTypes] [ProofTraceTypes] (StateT: Type) where
  invariant: Participant → StateT → ProofTrace → Prop
  invariant_later: ∀ p st tr1 tr2,
    tr1 ≤ tr2 →
    invariant p st tr1 →
    invariant p st tr2

grind_pattern LocalStateInv.invariant_later => tr1 ≤ tr2, LocalStateInv.invariant p st tr1
grind_pattern [grind_later] LocalStateInv.invariant_later => tr1 ≤ tr2, LocalStateInv.invariant p st tr1

namespace State

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  (StateT: Type) [LocalStateInv StateT]
  : PersistentGlobalState.GlobalStateInv (LocalState StateT)
where
  invariant st tr := LocalStateInv.invariant st.participant st.state tr
  invariant_later st tr1 tr2 := LocalStateInv.invariant_later st.participant st.state tr1 tr2

#combine (StateT: Type) into
  ProofEntryT,
  SubTraceInvariant [LocalStateInv StateT],
  SubBaseAttackerKnowledgeTheorem [LocalStateInv StateT],
from
  PersistentGlobalState.State (LocalState StateT)

end State

@[instance]
public
theorem storeLocalState.spec
  {StateT: Type}
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [LocalStateInv StateT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
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
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [LocalStateInv StateT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (participant: Participant) (handle: Nat)
  : HoareTriple
    (getLocalState participant handle: Traceful StateT)
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

#combine (StateT: Type) into ExecEntryT, baseAttackerKnowledge from
  PersistentGlobalState.Compromise (LocalState StateT),

end Compromise

public
def compromise
  (StateT: Type)
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (handle: Nat)
  : Traceful Nat
:= do
  PersistentGlobalState.compromise (LocalState StateT) handle

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

#combine (StateT: Type) into
  ProofEntryT,
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  PersistentGlobalState.Compromise (LocalState StateT)

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
  [ExecTraceTypes] [ProofTraceTypes]
  [BytesFunctor] [BytesInvariants]
  [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
extends
  LocalStateInv StateT
where
  invariant_implies_KnowableBy:
    ∀ (participant: Participant) (state: StateT) tr,
      LocalStateInv.invariant participant state tr →
      Comparse.IsWellFormed (Bytes.KnowableBy (label participant state)) state tr

instance
  [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor] [BytesInvariants]
  [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesInvariants.Has Literal.invariants]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Concat.invariants]
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
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ProofTraceTypes.Has Network.ProofEntryT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  [ProofTraceTypes.Has (Compromise.ProofEntryT StateT)]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  [Comparse.ParseableSerializeable StateT]
  [CompromisableLocalStateInv StateT]
  [TraceInvariant.Has Network.ProofEntryT]
  [TraceInvariant.Has (State.ProofEntryT StateT)]
  [TraceInvariant.Has (Compromise.ProofEntryT StateT)]
  (handle: Nat)
  : HoareTriple
    (compromise StateT handle)
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

#combine (StateT: Type) into ExecEntryT, baseAttackerKnowledge from
  State StateT,
  Compromise StateT,

#combine (StateT: Type) into ProofEntryT
from
  State StateT,
  Compromise StateT,

#combine
  (StateT: Type)
  [BytesFunctor] [BytesInvariants]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT] [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableLocalStateInv StateT]
into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem__noExecHas,
from
  State StateT,
  Compromise StateT,

end CompromisableState

end CompromisableState

end DY.PersistentLocalState
