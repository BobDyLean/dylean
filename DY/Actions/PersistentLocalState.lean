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
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  (StateT: Type)
  [Comparse.ParseableSerializeable StateT]
  : Comparse.ParseableSerializeable (LocalState StateT)
:= .make <|
  .triviallyIsomorphic
    (.prod .unboundedString Comparse.ParseableSerializeable.mf)
    (fun ⟨ participant, state ⟩ => { participant, state })
    (fun { participant, state } => ⟨ participant, state ⟩)

public -- it is useful to implement attacker programs
theorem LocalState.IsWellFormed_eq
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  {StateT: Type} [Comparse.ParseableSerializeable StateT]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: LocalState StateT) (tr: τ):
  Comparse.IsWellFormed pre x tr = Comparse.IsWellFormed pre x.state tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern LocalState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

namespace State

#combine (StateT: Type) into ExecTrace, Trace.BaseAttackerKnows from
  PersistentGlobalState.State (LocalState StateT)

end State

public
def storeLocalState
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace.Has (State.TracePart.Exec StateT)]
  (participant: Participant) (state: StateT)
  : Traceful Nat
:= do
  PersistentGlobalState.storeGlobalState ({ participant, state }: LocalState StateT)

public
def getLocalState
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace.Has (State.TracePart.Exec StateT)]
  (participant: Participant) (handle: Nat)
  : Traceful StateT
:= do
  let st: LocalState StateT ← PersistentGlobalState.getGlobalState handle
  guard (st.participant = participant)
  return st.state

end Execution

section Proof

public
class LocalStateInv [ExecTrace.Def] [ProofTrace.Def] (StateT: Type) where
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
  [ExecTrace.Def] [ProofTrace.Def]
  (StateT: Type) [LocalStateInv StateT]
  : PersistentGlobalState.GlobalStateInv (LocalState StateT)
where
  invariant st tr := LocalStateInv.invariant st.participant st.state tr
  invariant_later st tr1 tr2 := LocalStateInv.invariant_later st.participant st.state tr1 tr2

#combine (StateT: Type) into
  ProofTrace,
  Trace.Invariant [LocalStateInv StateT],
  Trace.BaseAttackerKnows_implies_Publishable [LocalStateInv StateT],
from
  PersistentGlobalState.State (LocalState StateT)

end State

@[instance]
public
theorem storeLocalState.proof
  {StateT: Type}
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [LocalStateInv StateT]
  [ExecTrace.Has (State.TracePart.Exec StateT)] [ProofTrace.Has (State.TracePart.Proof StateT)] [Trace.Invariant.Has (State.TracePart.Proof StateT)]
  (participant: Participant) (state: StateT)
  : HoareTriple
    (storeLocalState participant state)
    (fun tr => LocalStateInv.invariant participant state tr)
    (fun _ _ => True)
:= by
  unfold storeLocalState
  step by simp_all [PersistentGlobalState.GlobalStateInv.invariant]
  grind

@[instance]
public
theorem getLocalState.proof
  {StateT: Type}
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [LocalStateInv StateT]
  [ExecTrace.Has (State.TracePart.Exec StateT)] [ProofTrace.Has (State.TracePart.Proof StateT)] [Trace.Invariant.Has (State.TracePart.Proof StateT)]
  (participant: Participant) (handle: Nat)
  : HoareTriple
    (getLocalState participant handle: Traceful StateT)
    (fun _ => True)
    (fun st tr => LocalStateInv.invariant participant st tr)
:= by
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

#combine (StateT: Type) into ExecTrace, Trace.BaseAttackerKnows from
  PersistentGlobalState.Compromise (LocalState StateT),

end Compromise

public
def compromise
  (StateT: Type)
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace.Def]
  [ExecTrace.Has Network.TracePart.Exec]
  [ExecTrace.Has (State.TracePart.Exec StateT)]
  [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
  (handle: Nat)
  : Traceful Nat
:= do
  PersistentGlobalState.compromise (LocalState StateT) handle

public
def LocalStateCompromised
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
  (participant: Participant) (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  PersistentGlobalState.GlobalStateCompromised ({ participant, state }: LocalState StateT) tr

public
theorem LocalStateCompromised_le
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
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
  ProofTrace,
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from
  PersistentGlobalState.Compromise (LocalState StateT)

end Compromise

public
def label
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
  (participant: Participant) (state: StateT)
:=
  PersistentGlobalState.label ({ participant, state }: LocalState StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
  (participant: Participant) (state: StateT)
  (tr: ExecTrace)
  : (label participant state).isCorrupt tr = LocalStateCompromised participant state tr
:= by
  grind [label, LocalStateCompromised]

grind_pattern label_isCorrupt => (label participant state).isCorrupt tr

public
class CompromisableLocalStateInv
  (StateT: Type)
  [ExecTrace.Def] [ProofTrace.Def]
  [Bytes.Def] [Bytes.Invariants.Def]
  [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
extends
  LocalStateInv StateT
where
  invariant_implies_KnowableBy:
    ∀ (participant: Participant) (state: StateT) tr,
      LocalStateInv.invariant participant state tr →
      Comparse.IsWellFormed (Bytes.KnowableBy (label participant state)) state tr

instance
  [ExecTrace.Def] [ProofTrace.Def] [Bytes.Def] [Bytes.Invariants.Def]
  [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Invariants.Has Literal.BytesPart.invariants]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length] [Bytes.Invariants.Has Concat.BytesPart.invariants]
  (StateT: Type)
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
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
theorem compromise.proof
  {StateT: Type}
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [ExecTrace.Has Network.TracePart.Exec]
  [ProofTrace.Has Network.TracePart.Proof]
  [ExecTrace.Has (State.TracePart.Exec StateT)]
  [ProofTrace.Has (State.TracePart.Proof StateT)]
  [ExecTrace.Has (Compromise.TracePart.Exec StateT)]
  [ProofTrace.Has (Compromise.TracePart.Proof StateT)]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.Invariants.Has Literal.BytesPart.invariants]
  [Bytes.Invariants.Has Concat.BytesPart.invariants]
  [Comparse.ParseableSerializeable StateT]
  [CompromisableLocalStateInv StateT]
  [Trace.Invariant.Has Network.TracePart.Proof]
  [Trace.Invariant.Has (State.TracePart.Proof StateT)]
  [Trace.Invariant.Has (Compromise.TracePart.Proof StateT)]
  (handle: Nat)
  : HoareTriple
    (compromise StateT handle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold compromise
  step
  grind

end Proof

end Compromise

section CompromisableState

namespace CompromisableState

#combine (StateT: Type) into ExecTrace, Trace.BaseAttackerKnows from
  State StateT,
  Compromise StateT,

#combine (StateT: Type) into ProofTrace
from
  State StateT,
  Compromise StateT,

#combine
  (StateT: Type)
  [Bytes.Def] [Bytes.Invariants.Def]
  [Bytes.length.Def] [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  [Comparse.ParseableSerializeable StateT] [ExecTrace.Has (TracePart.Exec StateT)]
  [CompromisableLocalStateInv StateT]
into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable__noExecHas,
from
  State StateT,
  Compromise StateT,

end CompromisableState

end CompromisableState

end DY.PersistentLocalState
