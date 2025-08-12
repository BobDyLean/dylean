import Chamelean.Label.Type
import Chamelean.Trace.Type

namespace Chamelean

structure LabelCtor where
  isCorrupt: Trace Unit → Prop
  isCorruptLater:
    ∀ tr1 tr2, tr1 ≤ tr2 ∧ isCorrupt tr1 → isCorrupt tr2

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

def Label.isCorrupt (l: Label) (tr: Trace α) :=
  l.isCorrupt_ (Functor.mapConst () tr)

@[scoped grind→]
theorem _root_.Chamelean.Trace.MonotoneLemmas.isCorruptLater (l: Label) (tr1 tr2: Trace α):
  tr1 ≤ tr2 →
  l.isCorrupt tr1 →
  l.isCorrupt tr2
  := by
    intro h_le
    induction h_le with
    | equal => grind
    | extend tr2 e h_le ih =>
      intro
      apply l.isCorruptSnoc_
      suffices l.isCorrupt tr2 by -- ugh
        simp_all [Label.isCorrupt, map_const, Functor.map] -- uggh
      grind

def Label.canFlow (l1: Label) (l2: Label) (tr: Trace α): Prop :=
  ∀ trLater,
    tr ≤ trLater →
    l2.isCorrupt trLater → l1.isCorrupt trLater

@[scoped grind→]
theorem _root_.Chamelean.Trace.MonotoneLemmas.canFlowLater (l1: Label) (l2: Label) (tr1 tr2: Trace α):
  tr1 ≤ tr2 →
  l1.canFlow l2 tr1 →
  l1.canFlow l2 tr2
  := by
    unfold Label.canFlow
    grind [Trace.trace_le_trans]

def Label.pub : Label := Label.make {
  isCorrupt tr := True
  isCorruptLater := by grind
}

def Label.secret : Label := Label.make {
  isCorrupt tr := False
  isCorruptLater := by grind
}

def Label.join (l1 l2: Label): Label := Label.make {
  isCorrupt tr := l1.isCorrupt tr ∨ l2.isCorrupt tr
  isCorruptLater := by grind
}

def Label.meet (l1 l2: Label): Label := Label.make {
  isCorrupt tr := l1.isCorrupt tr ∧ l2.isCorrupt tr
  isCorruptLater := by grind
}

end Chamelean
