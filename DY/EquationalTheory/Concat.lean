import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.EquationalTheoryInvariants
import DY.Bytes.AttackerKnowledge

namespace DY

class CanConcat (Bytes: Type u) where
  concat: Bytes → Bytes → Bytes
  -- TODO: index
  split: Bytes → Option (Bytes × Bytes)

export CanConcat (concat)
export CanConcat (split)

instance: Ord Unit where
  compare _ _ := .eq

instance: Std.ReflOrd Unit where
  compare_self := by grind

instance: Std.LawfulEqOrd Unit where
  eq_of_compare := by grind

instance: Std.OrientedOrd Unit where
  eq_swap := by grind [Ordering.swap]

instance: Std.TransOrd Unit where
  isLE_trans := by grind

-- Constructors

abbrev Concat.ctor: BytesCtor where
  data := Unit
  nBytes := 2
  dataOrd := inferInstance
  dataReflOrd := inferInstance
  dataLawfulEqOrd := inferInstance
  dataOrientedOrd := inferInstance
  dataTransOrd := inferInstance

class abbrev Concat.HasCtor [BytesCtors] := Bytes.HasCtor Concat.ctor

abbrev Concat.id [BytesCtors] [Concat.HasCtor]: CtorId := Bytes.HasCtor.id Concat.ctor

abbrev Concat.View [BytesCtors] [Concat.HasCtor] := BytesView Concat.id

instance [BytesCtors] [Concat.HasCtor]: CanConcat Bytes where
  concat lhs rhs :=
    ({
      data := (),
      dataBytes := V[lhs, rhs]
    } : Concat.View).pack

  split buf :=
    match buf.view? Concat.id with
    | some { data := (), dataBytes := V[lhs, rhs] } =>
      some (lhs, rhs)
    | none => none

theorem split_concat
  [BytesCtors] [Concat.HasCtor]
  (lhs rhs: Bytes)
  : split (concat lhs rhs) = some (lhs, rhs)
  := by
    simp only [split, concat]
    grind

theorem concat_split
  [BytesCtors] [Concat.HasCtor]
  (buf lhs rhs: Bytes)
  : split buf = some (lhs, rhs) → concat lhs rhs = buf
  := by
    simp only [concat, split]
    grind

def Concat.ctors := [Concat.ctor]

instance [BytesCtors] [tc: Bytes.HasCtors Concat.ctors]: Bytes.HasCtor Concat.ctor := tc.tc (Fin.mk 0 (by simp [Concat.ctors]))

-- Equational theory

def Concat.attKnowsConcat [BytesCtors] [Bytes.HasCtors Concat.ctors]: AttackerKnowledge where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      p lhs ∧
      p rhs
  pred_scott_continuous := by
    sorry

def Concat.attKnowsSplitLeft [BytesCtors] [Bytes.HasCtors Concat.ctors]: AttackerKnowledge where
  pred p out :=
    ∃ inp rhs,
      some (out, rhs) = split inp ∧
      p inp
  pred_scott_continuous := by
    sorry

def Concat.attKnowsSplitRight [BytesCtors] [Bytes.HasCtors Concat.ctors]: AttackerKnowledge where
  pred p out :=
    ∃ inp lhs,
      some (lhs, out) = split inp ∧
      p inp
  pred_scott_continuous := by
    sorry

def Concat.equationalTheory: EquationalTheory where
  ctors := Concat.ctors
  attackerKnowledge := [Concat.attKnowsConcat, Concat.attKnowsSplitLeft, Concat.attKnowsSplitRight]

instance: EquationalTheory.CtorsEq Concat.equationalTheory Concat.ctors where pf := rfl

instance: NeZero Concat.equationalTheory.ctors.length where
  out := by simp [Concat.equationalTheory, Concat.ctors]

theorem Concat.attacker_knows_concat
  [EquationalTheories]
  [HasEquationalTheory Concat.equationalTheory]
  (lhs rhs: Bytes) (tr: Trace α)
  :
    lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
  := by
    intro h_lhs h_rhs
    apply Bytes.AttackerKnows.prove Concat.equationalTheory Concat.attKnowsConcat
    · simp [Concat.equationalTheory]
    simp only [Concat.attKnowsConcat]
    grind

theorem Concat.attacker_knows_split
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
    · apply Bytes.AttackerKnows.prove Concat.equationalTheory Concat.attKnowsSplitLeft
      · simp [Concat.equationalTheory]
      simp only [Concat.attKnowsSplitLeft]
      grind
    · apply Bytes.AttackerKnows.prove Concat.equationalTheory Concat.attKnowsSplitRight
      · simp [Concat.equationalTheory]
      simp only [Concat.attKnowsSplitRight]
      grind

-- Invariants

def Concat.invariants [BytesCtors]: BytesCtorInvariants.Internal Concat.ctor where
  well_formed := {
    func := fun () V[lhs, rhs] rec tr =>
      rec lhs tr ∧ rec rhs tr
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[lhs, rhs] := dataBytes
      simp_all +arith
  }

  usage := {
    func data dataBytes rec tr := Usage.nothing
    func_wf := by grind
  }
  usage_later data dataBytes rec_wf rec_usg := by grind [GetUsageLaterT]

  label := {
    func := fun () V[lhs, rhs] rec tr =>
      Label.meet (rec lhs tr) (rec rhs tr)
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[lhs, rhs] := dataBytes
      simp_all +arith
  }
  label_later data dataBytes rec_wf rec_usg := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [GetLabelLaterT]
    grind

  invariant := {
    func := fun () V[lhs, rhs] rec tr =>
      rec lhs tr ∧ rec rhs tr
    func_wf := by
      intro data dataBytes rec1 rec2
      let V[lhs, rhs] := dataBytes
      simp_all +arith
  }
  invariant_implies_wellformed data dataBytes rec_inv rec_wf := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [BytesInvariantImpliesBytesWellFormedT]
  invariant_later data dataBytes rec := by
    let V[lhs, rhs] := dataBytes
    simp_all +arith [BytesInvariantLaterT]
    grind

theorem Concat.invariants.workaround_11309.invariant
  [BytesCtors] [GetUsage] [GetLabel] [Concat.HasCtor]
  : ∀ lhs rhs rec tr,
    Concat.invariants.invariant.func () V[lhs, rhs] rec tr = (rec lhs tr ∧ rec rhs tr)
  := by
    intros
    rfl

class abbrev Concat.HasInvariants [BytesCtors] [Concat.HasCtor] [BytesCtorsInvariants] := HasBytesInvariants (Concat.id) Concat.invariants

@[simp]
theorem concat.wellFormed
  [BytesCtors] [BytesCtorsInvariants]
  [Concat.HasCtor] [Concat.HasInvariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  :
    (concat lhs rhs).wellFormed tr = (lhs.wellFormed tr ∧ rhs.wellFormed tr)
  := by
    simp [concat, Bytes.wellFormed.eq, Concat.invariants]

@[simp]
theorem concat.label
  [BytesCtors] [BytesCtorsInvariants]
  [Concat.HasCtor] [Concat.HasInvariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).label tr = Label.meet (lhs.label tr) (rhs.label tr)
  := by
    simp [concat, Bytes.label.eq, Concat.invariants]

@[simp]
theorem concat.invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Concat.HasCtor] [Concat.HasInvariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).invariant tr = (lhs.invariant tr ∧ rhs.invariant tr)
  := by
    simp [concat, Bytes.invariant.eq, Concat.invariants]


@[simp]
theorem split.wellFormed
  [BytesCtors] [BytesCtorsInvariants]
  [Concat.HasCtor] [Concat.HasInvariants]
  (buf: Bytes) (tr: ProofTrace)
  :
    match split buf with
    | none => True
    | some (lhs, rhs) =>
      buf.wellFormed tr = (lhs.wellFormed tr ∧ rhs.wellFormed tr)
  := by
    split
    · trivial
    rename_i lhs rhs heq
    rewrite [← concat_split buf lhs rhs heq]
    simp

@[simp]
theorem split.label
  [BytesCtors] [BytesCtorsInvariants]
  [Concat.HasCtor] [Concat.HasInvariants]
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
theorem split.invariant
  [BytesCtors] [BytesCtorsInvariants]
  [Concat.HasCtor] [Concat.HasInvariants]
  (buf: Bytes) (tr: ProofTrace)
  :
    buf.invariant tr →
    match split buf with
    | none => True
    | some (lhs, rhs) =>
      lhs.invariant tr ∧ rhs.invariant tr
  := by
    intro h_buf
    split
    · trivial
    rename_i lhs rhs heq
    rewrite [← concat_split buf lhs rhs heq] at h_buf
    simp_all

def Concat.EquationalTheoryInvariant [EquationalTheories]: EquationalTheoryInvariants Concat.equationalTheory where
  invariant
    | 0 => Concat.invariants

instance
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory Concat.equationalTheory] [Concat.EquationalTheoryInvariant.Has]
  : HasBytesInvariants Concat.id Concat.invariants :=
  Concat.EquationalTheoryInvariant.mkHasBytesInvariants (Fin.mk 0 (by simp [Concat.equationalTheory, Concat.ctors]))

-- Preserve publishability

def Concat.attKnowsConcat.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors Concat.ctors] [Concat.HasInvariants]: Concat.attKnowsConcat.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, Concat.attKnowsConcat]
    intro out tr ⟨lhs, rhs, ⟨ h_out, h_lhs, h_rhs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

def Concat.attKnowsSplitLeft.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors Concat.ctors] [Concat.HasInvariants]: Concat.attKnowsSplitLeft.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, Concat.attKnowsSplitLeft]
    intro out tr ⟨inp, rhs, ⟨ h_out, h_inp ⟩⟩
    simp_all [Bytes.Publishable]
    have := split.label inp tr
    have := split.invariant inp tr
    grind

def Concat.attKnowsSplitRight.preserves_publishability
  [BytesCtors] [BytesCtorsInvariants]
  [Bytes.HasCtors Concat.ctors] [Concat.HasInvariants]: Concat.attKnowsSplitRight.PreservesPublishability :=
  by
    simp only [AttackerKnowledge.PreservesPublishability, Concat.attKnowsSplitRight]
    intro out tr ⟨inp, lhs, ⟨ h_out, h_inp ⟩⟩
    simp_all [Bytes.Publishable]
    have := split.label inp tr
    have := split.invariant inp tr
    grind

def Concat.PreservesPublishability
  [EquationalTheories] [EquationalTheories.Invariants]
  [HasEquationalTheory Concat.equationalTheory]
  [Concat.EquationalTheoryInvariant.Has]
  : EquationalTheory.PreservesPublishability Concat.equationalTheory where
  pf := by
    unfold Concat.equationalTheory
    simp
    constructor
    · exact attKnowsConcat.preserves_publishability
    constructor
    · exact attKnowsSplitLeft.preserves_publishability
    · exact attKnowsSplitRight.preserves_publishability

end DY
