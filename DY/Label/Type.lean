import DY.Trace.Type

namespace DY

variable {CtorId} [BytesCtors CtorId]

structure Label where
  isCorrupt_: Trace Unit → Prop
  isCorruptSnoc_:
    ∀ tr e, isCorrupt_ tr → isCorrupt_ (.snoc tr e)

end DY
