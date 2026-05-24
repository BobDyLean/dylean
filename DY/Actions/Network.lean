module

public import DY.Trace
public import DY.Bytes
import DY.Meta.Step

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
def receiveMessage [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (handle: Nat): Traceful Bytes :=
  do
  let msg: ExecEntryT ← getEntry handle
  return msg.msg

end Execution

section Proof

public
abbrev ProofEntryT := ExecEntryT

public
instance: ErasableProofEntry ExecEntryT ProofEntryT := ErasableProofEntry.default ExecEntryT

public
instance: ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT where

public
instance
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  : SubTraceInvariant ProofEntryT
where
  invariant tr entry :=
    entry.msg.Publishable tr

public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]:
  SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    simp [SubTraceInvariant.invariant, baseAttackerKnowledge, ErasableProofEntry.erase]
    grind

@[instance]
public
theorem sendMessage.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (msg: Bytes)
  : HoareTriple
    (sendMessage msg)
    (fun tr => msg.Publishable tr)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold sendMessage
  dsimp only
  step with ⟨ fun _ => ExecEntryT.mk msg ⟩ by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
  trivial

@[instance]
public
theorem receiveMessage.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (handle: Nat)
  : HoareTriple
    (receiveMessage handle)
    (fun _ => True)
    (fun msg tr => msg.Publishable tr)
:= by
  apply HoareTriple.mk
  unfold receiveMessage
  step
  have: msg.msg.Publishable tr := by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]; grind
  rename_i h_msg; clear h_msg
  step
  grind

end Proof

section Reachability

variable [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
variable [BaseAttackerKnowledge] [AttackerKnowledge]

public
abbrev reachability : ReachabilityConfig where
  Input := Bytes
  PreCond b tr := b.AttackerKnows tr
  step b := ⟨ _, sendMessage b ⟩

public
theorem receiveMessage.preservesReachability
  [BaseAttackerKnowledge.Has baseAttackerKnowledge]
  (config: ReachabilityConfig)
  (msgHandle: Nat)
  : (receiveMessage msgHandle).PreservesReachability config (fun _ => True) (fun msg tr => msg.AttackerKnows tr)
:= by
  dsimp only [receiveMessage, Traceful.PreservesReachability]
  intro tr h_reach h_pre
  apply Traceful.PreservesReachabilityFrom_bind
  · apply getEntry.preservesReachability
  · grind
  · grind
  intro entry tr h_post h_reach h_le

  apply Traceful.PreservesReachabilityFrom_pure
  · grind

  apply Bytes.AttackerKnows.prove_from_base
  apply Trace.prove_BaseAttackerKnows baseAttackerKnowledge tr entry entry.msg msgHandle
  · grind
  simp [baseAttackerKnowledge]

variable [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants] [BytesInvariantsProofs]
variable [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
variable [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

public
instance: ReachableImpliesInvariant reachability
where
  pf b := by
    apply HoareTriple.mk
    have := (sendMessage.spec b).pf
    unfold hoareTriple at *
    grind [Bytes.AttackerKnows_implies_Publishable]

end Reachability

end DY.Network
