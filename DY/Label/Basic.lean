module

public import DY.Trace.Basic
meta import DY.Trace.Grind

namespace DY

variable [ExecTraceTypes]

public
structure Label [ExecTraceTypes] where
  isCorrupt: ExecTrace → Prop
  isCorruptLater:
    ∀ tr1 tr2, tr1 ≤ tr2 → isCorrupt tr1 → isCorrupt tr2
    := by grind

@[grind→, grind_later→]
public
theorem Label.isCorruptLater_grind (l: Label) (tr1 tr2: ExecTrace):
  tr1 ≤ tr2 →
  l.isCorrupt tr1 →
  l.isCorrupt tr2
  := by
    exact l.isCorruptLater tr1 tr2

@[ext]
public
theorem Label.ext
  [ExecTraceTypes]
  (l1 l2: Label)
  : (∀ tr: ExecTrace, l1.isCorrupt tr = l2.isCorrupt tr) →
  l1 = l2
  := by
    cases l1
    cases l2
    simp
    grind

@[expose]
public
def Label.canFlow (l1: Label) (l2: Label) (tr: ExecTrace): Prop :=
  ∀ trLater,
    tr ≤ trLater →
    l2.isCorrupt trLater → l1.isCorrupt trLater

@[grind→, grind_later→]
public
theorem Label.canFlowLater (l1: Label) (l2: Label) (tr1 tr2: ExecTrace):
  tr1 ≤ tr2 →
  l1.canFlow l2 tr1 →
  l1.canFlow l2 tr2
  := by
    unfold Label.canFlow
    grind [Trace.le_trans]

@[grind]
public
theorem canFlowRefl (l: Label) (tr: ExecTrace):
  l.canFlow l tr
  := by
    unfold Label.canFlow
    grind

-- @[grind]
public
theorem canFlowTrans (l1: Label) (l2: Label) (l3: Label) (tr: ExecTrace):
  l1.canFlow l2 tr →
  l2.canFlow l3 tr →
  l1.canFlow l3 tr
  := by
    unfold Label.canFlow
    grind

end DY
