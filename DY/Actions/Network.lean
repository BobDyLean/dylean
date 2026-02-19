module

public import DY.Trace
public import DY.Bytes
public import DY.Trace.Manipulation
import DY.Step.Init

namespace DY

namespace Network

variable [BytesFunctor]

public
structure MsgSent where
  msg: Bytes

@[expose]
public
def ExecEntryT: Type :=
  MsgSent

public
def attKnows [ExecTraceTypes]: ExecEntryAttackerKnowledge ExecEntryT where
  attackerKnows _ entry msg := msg = entry.msg

@[expose]
public
def ProofEntryT: Type := MsgSent

public
def ProofEntryFunc: ProofEntryFun ExecEntryT ProofEntryT where
  erase x := x

public
def Invariant [TraceTypes] [BytesInvariants]: TraceEntryInvariant ProofEntryFunc where
  invariant tr entry :=
    entry.msg.Publishable tr

-- TODO attacker knowledge theorem

public
def sendMessage [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (msg: Bytes): Traceful Nat :=
  do
  let time ← getTimestamp
  let entry: ExecEntryT := MsgSent.mk msg
  appendEntry entry
  return time

@[instance]
public
theorem sendMessage.spec
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [TraceInvariant.Has Invariant]
  (msg: Bytes)
  : HoareTriple
    (sendMessage msg)
    (fun tr => msg.Publishable tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold sendMessage
  dsimp only
  step
  step with ⟨ MsgSent.mk msg ⟩ by simp_all [ProofEntryFunc, Invariant]
  step
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
  [TraceInvariant.Has Invariant]
  (timestamp: Nat)
  : HoareTriple
    (receiveMessage timestamp)
    (fun _ => True)
    (fun msg tr => msg.Publishable tr)
:= by
  apply HoareTriple.mk
  unfold receiveMessage
  step
  have: msg.msg.Publishable tr := by grind [Invariant, ProofEntryFunc]
  rename_i h_msg; clear h_msg
  step
  grind

end Network

end DY
