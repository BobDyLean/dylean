module

public import DY.Trace
public import DY.Bytes
import DY.Step.Init

namespace DY.Network

variable [BytesFunctor]

public
structure ExecEntryT where
  msg: Bytes

public
def baseAttackerKnowledge [ExecTraceTypes]: EntryBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := msg = entry.msg

public
abbrev ProofEntryT := ExecEntryT

public
def ProofEntryFunc  := ProofEntryFun.default ExecEntryT

public
def Invariant [TraceTypes] [BytesInvariants]: TraceEntryInvariant ProofEntryFunc where
  invariant tr entry :=
    entry.msg.Publishable tr

public
theorem baseAttackerKnowledgeTheorem [TraceInvariant] [BytesInvariants] [TraceTypes.Has ProofEntryFunc] [TraceInvariant.Has Invariant]: EntryBaseAttackerKnowledgeTheorem Invariant baseAttackerKnowledge where
  pf trBefore entry b := by
    simp [Invariant, baseAttackerKnowledge, ProofEntryFunc]
    grind

public
def sendMessage [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (msg: Bytes): Traceful Nat :=
  do
  let entry: ExecEntryT := ExecEntryT.mk msg
  appendEntry entry

@[instance]
public
theorem sendMessage.spec
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [TraceTypes.Has ProofEntryFunc] [TraceInvariant.Has Invariant]
  (msg: Bytes)
  : HoareTriple
    (sendMessage msg)
    (fun tr => msg.Publishable tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold sendMessage
  dsimp only
  step with ⟨ fun _ => ExecEntryT.mk msg ⟩ by simp_all [ProofEntryFunc, Invariant]
  trivial

public
def receiveMessage [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (timestamp: Nat): Traceful Bytes :=
  do
  let msg: ExecEntryT ← getEntry timestamp
  return msg.msg

@[instance]
public
theorem receiveMessage.spec
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [TraceTypes.Has ProofEntryFunc] [TraceInvariant.Has Invariant]
  (timestamp: Nat)
  : HoareTriple
    (receiveMessage timestamp)
    (fun _ => True)
    (fun msg tr => msg.Publishable tr)
:= by
  apply HoareTriple.mk
  unfold receiveMessage
  step
  have: msg.msg.Publishable tr := by simp_all [Invariant, ProofEntryFunc]; grind
  rename_i h_msg; clear h_msg
  step
  grind

end DY.Network
