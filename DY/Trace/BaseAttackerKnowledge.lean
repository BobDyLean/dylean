module

public import DY.Bytes.Basic
public import DY.Trace.Basic
import all DY.Trace.Basic

namespace DY

public
structure EntryBaseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (ExecEntryT: Type) where
  attackerKnows: ExecTrace → ExecEntryT → Bytes → Prop

public
class BaseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] where
  attackerKnows: ∀ id, EntryBaseAttackerKnowledge (ExecTraceTypes.entries id)

public
def Trace.BaseAttackerKnows
  [BytesFunctor] [ExecTraceTypes] [BaseAttackerKnowledge]
  (tr: ExecTrace) (b: Bytes)
  : Prop
:=
  match tr with
  | .nil => False
  | .snoc trBefore entry =>
    (BaseAttackerKnowledge.attackerKnows entry.id).attackerKnows trBefore entry.entry b ∨
    Trace.BaseAttackerKnows trBefore b

public
def Trace.prove_BaseAttackerKnows
  [BytesFunctor] [ExecTraceTypes] [BaseAttackerKnowledge]
  (tr: ExecTrace) (b: Bytes)
  (time: Nat) (h_time: time < tr.length)
  : (BaseAttackerKnowledge.attackerKnows (tr.at time h_time).id).attackerKnows (tr.prefix time) (tr.at time h_time).entry b
    → Trace.BaseAttackerKnows tr b
:= by
  induction tr
  · grind [Trace.length]
  simp_all only [Trace.at, Trace.prefix, Trace.length, Trace.BaseAttackerKnows]
  grind

end DY
