import DY.Bytes.Basic
import DY.Trace.Basic

namespace DY

structure ExecEntryAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (ExecEntryT: ExecEntryType) where
  attackerKnows: ExecTrace → ExecEntryT.type → Bytes → Prop

class ExecTraceAttackerKnowledge [BytesFunctor] [ExecTraceTypes] where
  attackerKnows: ∀ id, ExecEntryAttackerKnowledge (ExecTraceTypes.entries id)

end DY
