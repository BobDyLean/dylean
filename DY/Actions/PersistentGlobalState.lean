module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.Network -- for compromise
public import DY.Actions.ProtocolEvent -- for compromise
public import DY.Comparse -- for compromise
import DY.Meta.Step

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
  (handle: Nat)
  : Traceful StateT
:= do
  let e: State.ExecEntryT StateT ← getEntry handle
  return e.st

end Execution

section Proof

public
class GlobalStateInv [ExecTraceTypes] [ProofTraceTypes] (StateT: Type) where
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
instance (StateT: Type): ExecEntryAssociatedWithProofEntry (ExecEntryT StateT) (ProofEntryT StateT) where

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  (StateT: Type)
  [GlobalStateInv StateT]
  : SubTraceInvariant (ProofEntryT StateT)
where
  invariant tr entry :=
    GlobalStateInv.invariant entry.st tr

public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT: Type)
  [ExecTraceTypes.Has (ExecEntryT StateT)]
  [ProofTraceTypes.Has (ProofEntryT StateT)]
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
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [GlobalStateInv StateT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (st: StateT)
  : HoareTriple
    (storeGlobalState st)
    (fun tr => GlobalStateInv.invariant st tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold storeGlobalState
  dsimp only
  step with ⟨ fun _ => State.ExecEntryT.mk st ⟩ by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
  trivial

@[instance]
public
theorem getGlobalState.spec
  {StateT: Type}
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [GlobalStateInv StateT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (handle: Nat)
  : HoareTriple
    (getGlobalState handle: Traceful StateT)
    (fun _ => True)
    (fun st tr => GlobalStateInv.invariant st tr)
:= by
  apply HoareTriple.mk
  unfold getGlobalState
  step
  have: GlobalStateInv.invariant e.st tr := by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]; grind
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

#combine (StateT: Type) into ExecEntryT, baseAttackerKnowledge from ProtocolEvent (CompromiseEvent StateT)

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
  let state: StateT ← getGlobalState handle
  ProtocolEvent.logEvent ({ state }: Compromise.CompromiseEvent StateT)
  Network.sendMessage (Comparse.serialize state)

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

public
instance
  {StateT: Type}
  [ExecTraceTypes] [ProofTraceTypes]
  : ProtocolEvent.EventInv (CompromiseEvent StateT)
where
  invariant _ _ := True

#combine (StateT: Type) into
  ProofEntryT,
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  ProtocolEvent (Compromise.CompromiseEvent StateT)

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
  [ExecTraceTypes] [ProofTraceTypes]
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [BytesInvariants]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
extends
  GlobalStateInv StateT
where
  invariant_implies_KnowableBy:
    ∀ (state: StateT) tr,
      GlobalStateInv.invariant state tr →
      Comparse.IsWellFormed (Bytes.KnowableBy (label state)) state tr

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
  [Comparse.ParseableSerializeable StateT]
  [CompromisableGlobalStateInv StateT]
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
  step by simp [ProtocolEvent.EventInv.invariant]
  step by
    have := CompromisableGlobalStateInv.invariant_implies_KnowableBy state tr
    have : (label state).isCorrupt tr.erase := by simp_all [label, ProtocolEvent.label_isCorrupt]
    grind [Comparse.IsWellFormed, canFlowTrans]
  trivial

end Proof

end Compromise

section CompromisableState

namespace CompromisableState

#combine (StateT: Type) into ExecEntryT, baseAttackerKnowledge from
  State StateT,
  Compromise StateT

#combine (StateT: Type) into ProofEntryT from
  State StateT,
  Compromise StateT,

#combine
  (StateT: Type)
  [BytesFunctor] [BytesInvariants] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (ExecEntryT StateT)]
  [CompromisableGlobalStateInv StateT]
into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem__noExecHas,
from
  State StateT,
  Compromise StateT,

end CompromisableState

end CompromisableState

end DY.PersistentGlobalState
