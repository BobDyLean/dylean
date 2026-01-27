import DY.Bytes.Type
import DY.Label.Type
import DY.Trace.Type
import DY.Bytes.Invariants
import DY.Bytes.AttackerKnowledge
import DY.Bytes.AttackerKnowledgeTheorem
import DY.Misc

namespace DY.Concat

class CanConcat (Bytes: Type u) where
  concat: Bytes → Bytes → Bytes
  -- TODO: index
  split: Bytes → Option (Bytes × Bytes)

export CanConcat (concat)
export CanConcat (split)

section Constructors

structure Concat (Bytes: Type) where
  lhs: Bytes
  rhs: Bytes

instance: ALaCarte.FunctorSizeOf Concat where
  sizeOf | {lhs, rhs} => sizeOf lhs + sizeOf rhs

instance: ALaCarte.Representable Concat where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {lhs, rhs} => {
    id := ()
    data := ()
    as := #v[lhs, rhs]
  }
  fromRepr
  | {id, data, as} =>
    let lhs := as[0]
    let rhs := as[1]
    { lhs, rhs }
  from_to | {lhs, rhs} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {lhs, rhs} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

instance: ALaCarte.RepresentableDecidableEq Concat where
instance: ALaCarte.RepresentableOrd Concat where
instance: SubBytesFunctor Concat where

abbrev SubF := Concat

variable [BytesFunctor] [BytesFunctor.Has SubF]

abbrev Concat.pack (x: Concat Bytes) := BytesView.pack x

instance: CanConcat Bytes where
  concat lhs rhs := ({lhs, rhs}: Concat Bytes).pack

  split buf :=
    match buf.view? Concat with
    | some ({ lhs, rhs }) =>
      some (lhs, rhs)
    | none => none

theorem split_concat
  (lhs rhs: Bytes)
  : split (concat lhs rhs) = some (lhs, rhs)
  := by
    simp only [split, concat]
    grind

theorem concat_split
  (buf lhs rhs: Bytes)
  : split buf = some (lhs, rhs) → concat lhs rhs = buf
  := by
    simp only [concat, split]
    grind

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]

def attKnowsConcat: SubAttackerKnowledge Concat where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      DY.Kleene.Forall p [lhs, rhs]

def attKnowsSplitLeft: SubAttackerKnowledge Concat where
  pred p out :=
    ∃ inp rhs,
      some (out, rhs) = split inp ∧
      DY.Kleene.Forall p [inp]

def attKnowsSplitRight: SubAttackerKnowledge Concat where
  pred p out :=
    ∃ inp lhs,
      some (lhs, out) = split inp ∧
      DY.Kleene.Forall p [inp]

def attackerKnowledge.internal (id: Fin 3): SubAttackerKnowledge Concat :=
  match id with
  | 0 => attKnowsConcat
  | 1 => attKnowsSplitLeft
  | 2 => attKnowsSplitRight

def attackerKnowledge: SubAttackerKnowledge Concat :=
  SubAttackerKnowledge.combine' attackerKnowledge.internal

instance: AttackerKnowledge.HasStep attKnowsConcat attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine' attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep attKnowsSplitLeft attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine' attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep attKnowsSplitRight attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 2) (SubAttackerKnowledge.combine' attackerKnowledge.internal))

variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

theorem attacker_knows_concat
  (lhs rhs: Bytes) (tr: Trace α)
  :
    lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
  := by
    intro h_lhs h_rhs
    apply Bytes.AttackerKnows.prove attKnowsConcat
    simp only [attKnowsConcat, Kleene.Forall]
    grind

theorem attacker_knows_split
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
    · apply Bytes.AttackerKnows.prove attKnowsSplitLeft
      simp only [attKnowsSplitLeft, Kleene.Forall]
      grind
    · apply Bytes.AttackerKnows.prove attKnowsSplitRight
      simp only [attKnowsSplitRight, Kleene.Forall]
      grind

end AttackerKnowledge

section Invariants

variable [BytesFunctor] [BytesFunctor.Has SubF]

def Concat.invariants: Bytes.PartialInvariants Concat where
  well_formed := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

  usage := fun {lhs, rhs} rec tr => Usage.nothing

  label := fun {lhs, rhs} rec tr =>
    Label.meet ((rec lhs) tr) ((rec rhs) tr)

  invariant := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

abbrev invariants: Bytes.PartialInvariants SubF := Concat.Concat.invariants

variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
theorem concat.WellFormed
  (lhs rhs: Bytes) (tr: ProofTrace)
  :
    (concat lhs rhs).WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
  := by
    simp [concat, Bytes.WellFormed.eq, Concat.invariants]

@[simp]
theorem concat.label
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).label tr = Label.meet (lhs.label tr) (rhs.label tr)
  := by
    simp [concat, Bytes.label.eq, Concat.invariants]

@[simp]
theorem concat.Invariant
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).Invariant tr = (lhs.Invariant tr ∧ rhs.Invariant tr)
  := by
    simp [concat, Bytes.Invariant.eq, Concat.invariants]


@[simp]
theorem split.WellFormed
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

end Invariants

section AttackerKnowledgeTheorem

variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

instance: SubAttackerKnowledgeTheorem attKnowsConcat where
  pf := by
    simp only [attKnowsConcat]
    intro out tr h_tr ⟨lhs, rhs, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    grind

instance: SubAttackerKnowledgeTheorem attKnowsSplitLeft where
  pf := by
    simp only [attKnowsSplitLeft]
    intro out tr h_tr ⟨inp, rhs, ⟨ h_out, h_inputs ⟩⟩
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have := split.label inp tr
    have := split.Invariant inp tr
    grind

instance: SubAttackerKnowledgeTheorem attKnowsSplitRight where
  pf := by
    simp only [attKnowsSplitRight]
    intro out tr h_tr ⟨inp, lhs, ⟨ h_out, h_inputs ⟩⟩
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have := split.label inp tr
    have := split.Invariant inp tr
    grind

instance: ∀ id, SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsConcat)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsSplitLeft)
  | 2 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsSplitRight)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' attackerKnowledge.internal))

end AttackerKnowledgeTheorem

end DY.Concat
