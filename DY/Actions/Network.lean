module

public import DY.Trace
public import DY.Bytes
import DY.Meta.Step

namespace DY.Network

variable [Bytes.Def]

section Execution

public
structure TracePart.Exec where
  msg: Bytes

public
def TracePart.baseAttackerKnows [ExecTrace.Def]: Trace.BaseAttackerKnows.Part TracePart.Exec where
  attackerKnows _ entry msg := msg = entry.msg

public
def sendMessage [ExecTrace.Def] [ExecTrace has% Network] (msg: Bytes): Traceful Nat :=
  do
  let entry: TracePart.Exec := TracePart.Exec.mk msg
  appendEntry entry

public
def receiveMessage [ExecTrace.Def] [ExecTrace has% Network] (handle: Nat): Traceful Bytes :=
  do
  let msg: TracePart.Exec ← getEntry handle
  return msg.msg

public
def _root_.DY.Trace.MessageSentAt
  [ExecTrace.Def] [ExecTrace has% Network]
  (tr: ExecTrace) (b: Bytes) (i: Nat)
  : Prop
:=
  tr.at? i = some (TracePart.Exec.mk b)

public
def _root_.DY.Trace.MessageSent
  [ExecTrace.Def] [ExecTrace has% Network]
  (tr: ExecTrace) (b: Bytes)
  : Prop
:=
  exists i, tr.MessageSentAt b i

public
def _root_.DY.Trace.getMessageSentAt
  [ExecTrace.Def] [ExecTrace has% Network]
  (i: Nat)
  (tr: ExecTrace)
  : Option Bytes
:=
  match (tr.at? i: Option TracePart.Exec) with
  | none => none
  | some entry => entry.msg

public
theorem _root_.DY.Trace.MessageSentAt_eq_getMessageSentAt
  [ExecTrace.Def]
  [ExecTrace has% Network]
  (msg: Bytes) (i: Nat) (tr: ExecTrace)
  : tr.MessageSentAt msg i = (tr.getMessageSentAt i = some msg)
:= by
  dsimp only [Trace.MessageSentAt, Trace.getMessageSentAt]
  grind [cases TracePart.Exec]

public
theorem _root_.DY.Trace.MessageSentAt_implies_AttackerKnows
  [ExecTrace.Def] [ExecTrace has% Network]
  [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  [Trace.BaseAttackerKnows has% Network]
  (tr: ExecTrace) (b: Bytes) (i: Nat)
  : tr.MessageSentAt b i →
    b.AttackerKnows tr
:= by
  dsimp only [Trace.MessageSentAt]
  intro h
  apply Bytes.AttackerKnows.prove_from_base
  apply Trace.prove_BaseAttackerKnows TracePart.baseAttackerKnows tr { msg := b } b i
  · grind
  simp [TracePart.baseAttackerKnows]

end Execution

section Proof

public
abbrev TracePart.Proof := TracePart.Exec

public
instance: ProofTrace.Part TracePart.Exec TracePart.Proof := ProofTrace.Part.default TracePart.Exec

public
instance: ExecEntryAssociatedWithProofEntry TracePart.Exec TracePart.Proof where

public
instance TracePart.invariant
  [ExecTrace.Def] [ProofTrace.Def] [Bytes.Invariants.Def]
  : Trace.Invariant.Part TracePart.Proof
where
  invariant tr entry :=
    entry.msg.Publishable tr

public
instance
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def] [Bytes.Invariants.Def]
  [ExecTrace has% Network]
  [ProofTrace has% Network]
  [Trace.Invariant has% Network]:
  Trace.BaseAttackerKnows_implies_Publishable.Part TracePart.Proof TracePart.baseAttackerKnows
where
  pf trBefore entry b := by
    simp [Trace.Invariant.Part.invariant, TracePart.baseAttackerKnows, ProofTrace.Part.erase]
    grind

@[instance]
public
theorem sendMessage.proof
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [ExecTrace has% Network]
  [ProofTrace has% Network]
  [Trace.Invariant has% Network]
  (msg: Bytes)
  : HoareTriple
    (sendMessage msg)
    (fun tr => msg.Publishable tr)
    (fun _ _ => True)
:= by
  unfold sendMessage
  dsimp only
  step with ⟨ fun _ => TracePart.Exec.mk msg ⟩ by simp_all [ProofTrace.Part.erase, Trace.Invariant.Part.invariant]
  grind

@[instance]
public
theorem receiveMessage.proof
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [ExecTrace has% Network]
  [ProofTrace has% Network]
  [Trace.Invariant has% Network]
  (handle: Nat)
  : HoareTriple
    (receiveMessage handle)
    (fun _ => True)
    (fun msg tr => msg.Publishable tr)
:= by
  unfold receiveMessage
  step
  have: msg.msg.Publishable tr := by simp_all [ProofTrace.Part.erase, Trace.Invariant.Part.invariant]; grind
  rename_i h_msg; clear h_msg
  step
  grind

end Proof

section Reachability

variable [ExecTrace.Def] [ExecTrace has% Network]
variable [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]

public
abbrev transitionSystem : TransitionSystem where
  Input := Bytes
  PreCond b tr := b.AttackerKnows tr
  step b := ⟨ _, sendMessage b ⟩

public
theorem receiveMessage.preservesReachability
  [Trace.BaseAttackerKnows has% Network]
  (config: TransitionSystem)
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
  apply Trace.prove_BaseAttackerKnows TracePart.baseAttackerKnows tr entry entry.msg msgHandle
  · grind
  simp [TracePart.baseAttackerKnows]

variable [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
variable [ProofTrace has% Network] [Trace.Invariant has% Network]
variable [Trace.BaseAttackerKnows_implies_Publishable.Proof] [Bytes.AttackerKnows_implies_Publishable.Proof]

public
instance: Trace.Reachable_implies_Invariant.Part transitionSystem
where
  pf b := by
    apply HoareTriple.mk
    have := (sendMessage.proof b).pf
    unfold hoareTriple at *
    grind [Bytes.AttackerKnows_implies_Publishable]

end Reachability

end DY.Network
