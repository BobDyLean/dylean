module

public import DY.Trace
public import DY.Bytes
import DY.Step.Init

namespace DY.Network

variable [BytesFunctor]

section Execution

public
structure ExecEntryT where
  msg: Bytes

public
def baseAttackerKnowledge [ExecTraceTypes]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := msg = entry.msg

public
def sendMessage [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.mk msg
  appendEntry entry

public
def receiveMessage [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (timestamp: Nat): Traceful Bytes :=
  do
  let msg: ExecEntryT ← getEntry timestamp
  return msg.msg

end Execution

section Proof

public
abbrev ProofEntryT := ExecEntryT

public
instance: ErasableProofEntry ExecEntryT ProofEntryT := ErasableProofEntry.default ExecEntryT

public
instance
  [TraceTypes] [BytesInvariants]
  : ProofEntryInvariant ProofEntryT
where
  invariant tr entry :=
    entry.msg.Publishable tr

public
instance baseAttackerKnowledgeTheorem
  [TraceInvariant] [BytesInvariants]
  [TraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]:
  SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    simp [ProofEntryInvariant.invariant, baseAttackerKnowledge, ErasableProofEntry.erase]
    grind

@[instance]
public
theorem sendMessage.spec
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [TraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
  (msg: Bytes)
  : HoareTriple
    (sendMessage msg)
    (fun tr => msg.Publishable tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold sendMessage
  dsimp only
  step with ⟨ fun _ => ExecEntryT.mk msg ⟩ by simp_all [ErasableProofEntry.erase, ProofEntryInvariant.invariant]
  trivial

@[instance]
public
theorem receiveMessage.spec
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [TraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
  (timestamp: Nat)
  : HoareTriple
    (receiveMessage timestamp)
    (fun _ => True)
    (fun msg tr => msg.Publishable tr)
:= by
  apply HoareTriple.mk
  unfold receiveMessage
  step
  have: msg.msg.Publishable tr := by simp_all [ErasableProofEntry.erase, ProofEntryInvariant.invariant]; grind
  rename_i h_msg; clear h_msg
  step
  grind

end Proof

end DY.Network
