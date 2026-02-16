module

public import DY.Label.Basic
public import DY.Trace.Basic

namespace DY

variable [BytesFunctor]

public
structure LabelCtor where
  isCorrupt: Trace Unit → Prop
  isCorruptLater:
    ∀ tr1 tr2, tr1 ≤ tr2 ∧ isCorrupt tr1 → isCorrupt tr2

public
def Label.make (l: LabelCtor): Label := {
  isCorrupt_ := l.isCorrupt
  isCorruptSnoc_ := by
    intros tr e h
    apply l.isCorruptLater tr
    constructor
    · simp [LE.le]
      apply Trace.LETrace.extend tr tr e
      apply Trace.LETrace.equal tr
    · assumption
}

public
def Label.isCorrupt (l: Label) (tr: Trace α) :=
  l.isCorrupt_ tr.erase

@[simp, grind]
public
theorem Label.makeIsCorrupt (ctor: LabelCtor) (tr: Trace α): (Label.make ctor).isCorrupt tr = ctor.isCorrupt tr.erase := by
  simp [Label.make, isCorrupt]

@[scoped grind→]
public
theorem _root_.DY.Trace.MonotoneLemmas.isCorrupt_Later (l: Label) (tr1 tr2: Trace Unit):
  tr1 ≤ tr2 →
  l.isCorrupt_ tr1 →
  l.isCorrupt_ tr2
  := by
    intro h_le
    induction h_le with
    | equal => grind
    | extend tr2 e h_le ih =>
      intro
      apply l.isCorruptSnoc_
      grind

@[scoped grind→]
public
theorem _root_.DY.Trace.MonotoneLemmas.isCorruptLater (l: Label) (tr1 tr2: Trace α):
  tr1 ≤ tr2 →
  l.isCorrupt tr1 →
  l.isCorrupt tr2
  := by
    unfold Label.isCorrupt
    intro
    apply _root_.DY.Trace.MonotoneLemmas.isCorrupt_Later
    apply Trace.erase_le
    assumption

@[ext]
public
theorem Label.ext
  (l1 l2: Label)
  : (∀ tr: Trace Unit, l1.isCorrupt tr = l2.isCorrupt tr) →
  l1 = l2
  := by
    cases l1
    cases l2
    simp only [mk.injEq, isCorrupt]
    intro
    funext tr
    have := Trace.erase_idempotent tr
    grind

@[expose]
public
def Label.canFlow (l1: Label) (l2: Label) (tr: Trace α): Prop :=
  ∀ trLater,
    tr ≤ trLater →
    l2.isCorrupt trLater → l1.isCorrupt trLater

@[scoped grind→]
public
theorem _root_.DY.Trace.MonotoneLemmas.canFlowLater (l1: Label) (l2: Label) (tr1 tr2: Trace α):
  tr1 ≤ tr2 →
  l1.canFlow l2 tr1 →
  l1.canFlow l2 tr2
  := by
    unfold Label.canFlow
    grind [Trace.trace_le_trans]

@[grind]
public
theorem canFlowRefl (l: Label) (tr: Trace α):
  l.canFlow l tr
  := by
    unfold Label.canFlow
    grind

-- @[grind]
public
theorem canFlowTrans (l1: Label) (l2: Label) (l3: Label) (tr: Trace α):
  l1.canFlow l2 tr →
  l2.canFlow l3 tr →
  l1.canFlow l3 tr
  := by
    unfold Label.canFlow
    grind

public
def Label.pub : Label := Label.make {
  isCorrupt tr := True
  isCorruptLater := by grind
}

@[simp, grind]
public
theorem Label.pubIsCorrupt (tr: Trace α): Label.pub.isCorrupt tr := by
  grind [Label.pub]

@[grind =_]
public
theorem canFlowPubEqIsCorrupt (l: Label) (tr: Trace α):
  l.isCorrupt tr = l.canFlow Label.pub tr
  := by
  -- TODO: open doesn't work?
  -- open DY.Trace.MonotoneLemmas in
  grind [Label.canFlow, DY.Trace.MonotoneLemmas.isCorruptLater]

public
def Label.secret : Label := Label.make {
  isCorrupt tr := False
  isCorruptLater := by grind
}

@[simp, grind]
public
theorem Label.secretIsCorrupt (tr: Trace α): ¬ Label.secret.isCorrupt tr := by
  grind [secret]

@[grind]
public
theorem Label.secret.canFlow (l: Label) (tr: Trace α):
  l.canFlow secret tr
  := by
  grind [Label.canFlow]

public
def Label.join (l1 l2: Label): Label := Label.make {
  isCorrupt tr := l1.isCorrupt_ tr ∨ l2.isCorrupt_ tr
  isCorruptLater := by grind
}

@[simp, grind]
public
theorem Label.joinIsCorrupt (l1 l2: Label) (tr: Trace α):
  (l1.join l2).isCorrupt tr = (l1.isCorrupt tr ∨ l2.isCorrupt tr)
  := by
  grind [join, isCorrupt]

public
def Label.meet (l1 l2: Label): Label := Label.make {
  isCorrupt tr := l1.isCorrupt_ tr ∧ l2.isCorrupt_ tr
  isCorruptLater := by grind
}

@[simp, grind]
public
theorem Label.meetIsCorrupt (l1 l2: Label) (tr: Trace α):
  (l1.meet l2).isCorrupt tr = (l1.isCorrupt tr ∧ l2.isCorrupt tr)
  := by
  grind [meet, isCorrupt]

@[grind =]
public
theorem Label.joinEq (l1: Label) (l2: Label) (l3: Label) (tr: Trace α):
  l1.canFlow (l2.join l3) tr = (l1.canFlow l2 tr ∧ l1.canFlow l3 tr)
  := by
  grind [canFlow]

@[grind]
public
theorem Label.joinCanFlowLeft (l1: Label) (l2: Label) (tr: Trace α):
  (l1.join l2).canFlow l1 tr
  := by
  have := joinEq (l1.join l2) l1 l2 tr
  grind

@[grind]
public
theorem Label.joinCanFlowRight (l1: Label) (l2: Label) (tr: Trace α):
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
