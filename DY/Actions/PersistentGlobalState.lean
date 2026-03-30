module

public import DY.Trace
public import DY.Bytes
import DY.Step.Init

namespace DY.PersistentGlobalState

section Execution

public
structure ExecEntryT (StateT: Type) where
  st: StateT

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (StateT: Type): SubBaseAttackerKnowledge (ExecEntryT StateT) where
  attackerKnows _ _ _ := False

public
def storeGlobalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (st: StateT)
  : Traceful Nat
:= do
  let entry: ExecEntryT StateT := { st }
  appendEntry entry

public
def getGlobalState
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT StateT)]
  (i: Nat)
  : Traceful StateT
:= do
  let e: ExecEntryT StateT ← getEntry i
  return e.st

end Execution

section Proof

public
abbrev ProofEntryT (StateT: Type) := ExecEntryT StateT

public
instance (StateT: Type): ErasableProofEntry (ExecEntryT StateT) (ProofEntryT StateT) := ErasableProofEntry.default (ExecEntryT StateT)

public
class GlobalStateInv [TraceTypes] (StateT: Type) where
  invariant: StateT → ProofTrace → Prop
  invariant_later: ∀ st tr1 tr2,
    tr1 ≤ tr2 →
    invariant st tr1 →
    invariant st tr2

grind_pattern GlobalStateInv.invariant_later => tr1 ≤ tr2, GlobalStateInv.invariant st tr1
grind_pattern [grind_later] GlobalStateInv.invariant_later => tr1 ≤ tr2, GlobalStateInv.invariant st tr1

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

@[instance]
public
theorem storeGlobalState.spec
  {StateT: Type}
  [TraceInvariant]
  [GlobalStateInv StateT]
  [TraceTypes.Has (ProofEntryT StateT)] [TraceInvariant.Has (ProofEntryT StateT)]
  (st: StateT)
  : HoareTriple
    (storeGlobalState st)
    (fun tr => GlobalStateInv.invariant st tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold storeGlobalState
  dsimp only
  step with ⟨ fun _ => ExecEntryT.mk st ⟩ by simp_all [ErasableProofEntry.erase, ProofEntryInvariant.invariant]
  trivial

@[instance]
public
theorem getGlobalState.spec
  {StateT: Type}
  [TraceInvariant]
  [GlobalStateInv StateT]
  [TraceTypes.Has (ProofEntryT StateT)] [TraceInvariant.Has (ProofEntryT StateT)]
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

end DY.PersistentGlobalState
