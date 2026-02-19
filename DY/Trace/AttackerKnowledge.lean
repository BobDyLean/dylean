module

public import DY.Bytes.Basic
public import DY.Trace.Basic

namespace DY

public
structure ExecEntryAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (ExecEntryT: Type) where
  attackerKnows: ExecTrace → ExecEntryT → Bytes → Prop

public
class ExecTraceAttackerKnowledge [BytesFunctor] [ExecTraceTypes] where
  attackerKnows: ∀ id, ExecEntryAttackerKnowledge (ExecTraceTypes.entries id)

end DY
