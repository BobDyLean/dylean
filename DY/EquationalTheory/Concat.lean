import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.EquationalTheoryInvariants
import DY.Bytes.AttackerKnowledge
import DY.Misc

namespace DY.Concat

class CanConcat (Bytes: Type u) where
  concat: Bytes → Bytes → Bytes
  -- TODO: index
  split: Bytes → Option (Bytes × Bytes)

export CanConcat (concat)
export CanConcat (split)

-- Constructors

section Constructors

variable {CtorId} [BytesCtors CtorId] [DecidableEq CtorId]

def Concat.ctor: BytesCtor where
  data := Unit
  nBytes := 2

def Concat.View [Concat.ctor.HasCtor] := BytesView Concat.ctor.id

instance [Concat.ctor.HasCtor]: CanConcat Bytes where
  concat lhs rhs :=
    ({
      data := (),
      dataBytes := V[lhs, rhs]
    } : Concat.View).pack

  split buf :=
    match buf.view? Concat.ctor.id with
    | some { data := (), dataBytes := V[lhs, rhs] } =>
      some (lhs, rhs)
    | none => none

theorem split_concat
  [Concat.ctor.HasCtor]
  (lhs rhs: Bytes)
  : split (concat lhs rhs) = some (lhs, rhs)
  := by
    simp only [split, concat]
    grind

theorem concat_split
  [Concat.ctor.HasCtor]
  (buf lhs rhs: Bytes)
  : split buf = some (lhs, rhs) → concat lhs rhs = buf
  := by
    simp only [concat, split]
    grind

def ctors := [Concat.ctor]

instance [tc: Bytes.HasCtors ctors]: Concat.ctor.HasCtor := tc.tc (Fin.mk 0 (by simp [ctors]))

end Constructors

-- Equational theory

def attKnowsConcat {CtorId} [BytesCtors CtorId] [DecidableEq CtorId] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      p lhs ∧
      p rhs
  pred_scott_continuous := by
    sorry

def attKnowsSplitLeft {CtorId} [BytesCtors CtorId] [DecidableEq CtorId] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ inp rhs,
      some (out, rhs) = split inp ∧
      p inp
  pred_scott_continuous := by
    sorry

def attKnowsSplitRight {CtorId} [BytesCtors CtorId] [DecidableEq CtorId] [Bytes.HasCtors ctors]: AttackerKnowledge where
  pred p out :=
    ∃ inp lhs,
      some (lhs, out) = split inp ∧
      p inp
  pred_scott_continuous := by
    sorry

def Concat.equationalTheory: EquationalTheory where
  ctors := ctors
  attackerKnowledge := [attKnowsConcat, attKnowsSplitLeft, attKnowsSplitRight]

instance: EquationalTheory.CtorsEq Concat.equationalTheory ctors where pf := rfl

instance: NeZero Concat.equationalTheory.ctors.length where
  out := by simp [Concat.equationalTheory, ctors]

theorem attacker_knows_concat
  [EquationalTheories]
  [HasEquationalTheory Concat.equationalTheory]
  (lhs rhs: Bytes) (tr: Trace α)
  :
    lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
  := by
    intro h_lhs h_rhs
    apply Bytes.AttackerKnows.prove Concat.equationalTheory attKnowsConcat
    · simp [Concat.equationalTheory]
    simp only [attKnowsConcat]
    grind

theorem attacker_knows_split
  [EquationalTheories]
  [HasEquationalTheory Concat.equationalTheory]
  (buf: Bytes) (tr: Trace α)
  :
    buf.AttackerKnows tr →
    match split buf with
    | none => True
    | some (lhs, rhs) =>
      lhs.AttackerKnows tr ∧
      rhs.AttackerKnows tr
  := by
    intro h_buf
    split
    · trivial
    rename_i lhs rhs _
    constructor
    · apply Bytes.AttackerKnows.prove Concat.equationalTheory attKnowsSplitLeft
      · simp [Concat.equationalTheory]
      simp only [attKnowsSplitLeft]
      grind
    · apply Bytes.AttackerKnows.prove Concat.equationalTheory attKnowsSplitRight
      · simp [Concat.equationalTheory]
      simp only [attKnowsSplitRight]
      grind

-- Invariants

def Concat.invariants [EquationalTheories]: BytesCtorInvariants.Internal Concat.ctor where
  well_formed := {
    func := fun () V[lhs, rhs] rec tr =>
      rec lhs tr ∧ rec rhs tr
  }
  well_formed_later data dataBytes rec_wf := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [BytesWellFormedLaterT]
    grind

  usage := {
    func data dataBytes rec tr := Usage.nothing
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func := fun () V[lhs, rhs] rec tr =>
      Label.meet (rec lhs tr) (rec rhs tr)
  }
  label_later data dataBytes rec_wf rec_usg := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [GetLabelLaterT]
    grind

  invariant := {
    func := fun () V[lhs, rhs] rec tr =>
      rec lhs tr ∧ rec rhs tr
  }
  invariant_implies_wellformed data dataBytes rec_inv rec_wf := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [BytesInvariantImpliesBytesWellFormedT]
  invariant_later data dataBytes rec := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [BytesInvariantLaterT]
    grind

class abbrev Concat.HasInvariants [EquationalTheories] [Concat.ctor.HasCtor] [BytesCtorsInvariants] := HasBytesInvariants (Concat.ctor.id) Concat.invariants

@[simp]
theorem concat.WellFormed
  [EquationalTheories] [BytesCtorsInvariants]
  [Concat.ctor.HasCtor] [Concat.HasInvariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  :
    (concat lhs rhs).WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
  := by
    simp [concat, Bytes.WellFormed.eq, Concat.invariants]

@[simp]
theorem concat.label
  [EquationalTheories] [BytesCtorsInvariants]
  [Concat.ctor.HasCtor] [Concat.HasInvariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).label tr = Label.meet (lhs.label tr) (rhs.label tr)
  := by
    simp [concat, Bytes.label.eq, Concat.invariants]

@[simp]
theorem concat.Invariant
  [EquationalTheories] [BytesCtorsInvariants]
  [Concat.ctor.HasCtor] [Concat.HasInvariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).Invariant tr = (lhs.Invariant tr ∧ rhs.Invariant tr)
  := by
    simp [concat, Bytes.Invariant.eq, Concat.invariants]


@[simp]
theorem split.WellFormed
  [EquationalTheories] [BytesCtorsInvariants]
  [Concat.ctor.HasCtor] [Concat.HasInvariants]
  (buf: Bytes) (tr: ProofTrace)
  :
    match split buf with
    | none => True
    | some (lhs, rhs) =>
      buf.WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
  := by
    split
    · trivial
    rename_i lhs rhs heq
    rewrite [← concat_split buf lhs rhs heq]
    simp

@[simp]
theorem split.label
  [EquationalTheories] [BytesCtorsInvariants]
  [Concat.ctor.HasCtor] [Concat.HasInvariants]
  (buf: Bytes) (tr: ProofTrace)
  :
    match split buf with
    | none => True
    | some (lhs, rhs) =>
      buf.label tr = Label.meet (lhs.label tr) (rhs.label tr)
  := by
    split
    · trivial
    rename_i lhs rhs heq
    rewrite [← concat_split buf lhs rhs heq]
    simp

@[simp]
theorem split.Invariant
  [EquationalTheories] [BytesCtorsInvariants]
  [Concat.ctor.HasCtor] [Concat.HasInvariants]
  (buf: Bytes) (tr: ProofTrace)
  :
    buf.Invariant tr →
    match split buf with
    | none => True
    | some (lhs, rhs) =>
      lhs.Invariant tr ∧ rhs.Invariant tr
  := by
    intro h_buf
    split
    · trivial
    rename_i lhs rhs heq
    rewrite [← concat_split buf lhs rhs heq] at h_buf
    simp_all

def EquationalTheoryInvariant [EquationalTheories]: EquationalTheoryInvariants Concat.equationalTheory where
  invariant
    | 0 => Concat.invariants

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory Concat.equationalTheory] [EquationalTheoryInvariant.Has]
  : HasBytesInvariants Concat.ctor.id Concat.invariants :=
  EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 0 (by simp [Concat.equationalTheory, ctors]))

-- Preserve publishability

def attKnowsConcat.preserves_publishability
  [EquationalTheories] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Concat.HasInvariants]: attKnowsConcat.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsConcat]
    intro out tr ⟨lhs, rhs, ⟨ h_out, h_lhs, h_rhs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

def attKnowsSplitLeft.preserves_publishability
  [EquationalTheories] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Concat.HasInvariants]: attKnowsSplitLeft.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsSplitLeft]
    intro out tr ⟨inp, rhs, ⟨ h_out, h_inp ⟩⟩
    simp_all [Bytes.Publishable]
    have := split.label inp tr
    have := split.Invariant inp tr
    grind

def attKnowsSplitRight.preserves_publishability
  [EquationalTheories] [BytesCtorsInvariants]
  [Bytes.HasCtors ctors] [Concat.HasInvariants]: attKnowsSplitRight.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, attKnowsSplitRight]
    intro out tr ⟨inp, lhs, ⟨ h_out, h_inp ⟩⟩
    simp_all [Bytes.Publishable]
    have := split.label inp tr
    have := split.Invariant inp tr
    grind

def PreservesPublishability
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory Concat.equationalTheory]
  [EquationalTheoryInvariant.Has]
  : EquationalTheory.PreservesPublishability Concat.equationalTheory where
  pf := by
    unfold Concat.equationalTheory
    simp
    constructor
    · exact attKnowsConcat.preserves_publishability
    constructor
    · exact attKnowsSplitLeft.preserves_publishability
    · exact attKnowsSplitRight.preserves_publishability

end DY.Concat
