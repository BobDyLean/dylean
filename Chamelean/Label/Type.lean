import Chamelean.Trace.Type

namespace Chamelean

structure Label where
  isCorrupt_: Trace Unit → Prop
  isCorruptSnoc_:
    ∀ tr e, isCorrupt_ tr → isCorrupt_ (.snoc tr e)

end Chamelean
