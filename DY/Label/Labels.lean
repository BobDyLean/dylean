module

public import DY.Label.Basic
public import DY.Trace.Basic
public import DY.Trace.Invariant

namespace DY

variable [ExecTraceTypes]

public
def Label.pub : Label := {
  isCorrupt tr := True
}

@[simp, grind]
public
theorem Label.pubIsCorrupt (tr: ExecTrace): Label.pub.isCorrupt tr := by
  grind [Label.pub]

@[grind =_]
public
theorem canFlowPubEqIsCorrupt (l: Label) (tr: ExecTrace):
  l.isCorrupt tr = l.canFlow Label.pub tr
  := by
  grind [Label.canFlow]

@[grind]
public
theorem Label.pubCanFlow (l: Label) (tr: ExecTrace): Label.pub.canFlow l tr := by
  grind [Label.pub, canFlow]

public
def Label.secret : Label := {
  isCorrupt tr := False
}

@[simp, grind]
public
theorem Label.secretIsCorrupt (tr: ExecTrace): ¬ Label.secret.isCorrupt tr := by
  grind [secret]

@[grind]
public
theorem Label.secret.canFlow (l: Label) (tr: ExecTrace):
  l.canFlow secret tr
  := by
  grind [Label.canFlow]

public
def Label.join (l1 l2: Label): Label := {
  isCorrupt tr := l1.isCorrupt tr ∨ l2.isCorrupt tr
}

@[simp, grind]
public
theorem Label.joinIsCorrupt (l1 l2: Label) (tr: ExecTrace):
  (l1.join l2).isCorrupt tr = (l1.isCorrupt tr ∨ l2.isCorrupt tr)
  := by
  grind [join]

public
def Label.meet (l1 l2: Label): Label := {
  isCorrupt tr := l1.isCorrupt tr ∧ l2.isCorrupt tr
}

@[simp, grind]
public
theorem Label.meetIsCorrupt (l1 l2: Label) (tr: ExecTrace):
  (l1.meet l2).isCorrupt tr = (l1.isCorrupt tr ∧ l2.isCorrupt tr)
  := by
  grind [meet]

@[grind =]
public
theorem Label.meetEq (l1: Label) (l2: Label) (l3: Label) (tr: ExecTrace):
  (l1.meet l2).canFlow l3 tr = (l1.canFlow l3 tr ∧ l2.canFlow l3 tr)
  := by
  grind [canFlow]

@[grind =]
public
theorem Label.joinEq (l1: Label) (l2: Label) (l3: Label) (tr: ExecTrace):
  l1.canFlow (l2.join l3) tr = (l1.canFlow l2 tr ∧ l1.canFlow l3 tr)
  := by
  grind [canFlow]

@[grind]
public
theorem Label.joinCanFlowLeft (l1: Label) (l2: Label) (tr: ExecTrace):
  (l1.join l2).canFlow l1 tr
  := by
  have := joinEq (l1.join l2) l1 l2 tr
  grind

@[grind]
public
theorem Label.joinCanFlowRight (l1: Label) (l2: Label) (tr: ExecTrace):
  (l1.join l2).canFlow l2 tr
  := by
  have := joinEq (l1.join l2) l1 l2 tr
  grind

@[grind]
public
theorem Label.join_pub_left (l: Label): Label.join Label.pub l = Label.pub := by
  ext
  grind

@[grind]
public
theorem Label.join_pub_right (l: Label): Label.join l Label.pub = Label.pub := by
  ext
  grind

public
theorem Label.join_commutes (l1 l2: Label): Label.join l1 l2 = Label.join l2 l1 := by
  ext
  grind

grind_pattern Label.join_commutes => Label.join l1 l2, Label.join l2 l1

end DY
