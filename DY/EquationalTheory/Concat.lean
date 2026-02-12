import DY.Trace.Basic
import DY.Label
import DY.Bytes
import DY.Misc

namespace DY.Concat

class CanConcat (Bytes: Type u) where
  concat: Bytes → Bytes → Bytes
  split: Bytes → Nat → Option (Bytes × Bytes)

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

def Concat.length [BytesFunctor]: Bytes.PartialLength Concat :=
  fun { lhs, rhs } rec =>
    rec lhs + rec rhs

abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF := Concat.length

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesLength]

abbrev Concat.pack (x: Concat Bytes) := BytesView.pack x

instance: CanConcat Bytes where
  concat lhs rhs := ({lhs, rhs}: Concat Bytes).pack

  split buf i :=
    match buf.view? Concat with
    | some ({ lhs, rhs }) =>
      if lhs.length = i then
        some (lhs, rhs)
      else
        none
    | none => none

theorem split_concat
  (lhs rhs: Bytes)
  : split (concat lhs rhs) (lhs.length) = some (lhs, rhs)
:= by
  simp only [split, concat]
  grind

theorem concat_split
  (buf: Bytes) (i: Nat) (lhs rhs: Bytes)
  : split buf i = some (lhs, rhs) → concat lhs rhs = buf
:= by
  simp only [concat, split]
  grind

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesLength]

def attKnowsConcat: SubAttackerKnowledge Concat where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      DY.Kleene.Forall p [lhs, rhs]

def attKnowsSplitLeft: SubAttackerKnowledge Concat where
  pred p out :=
    ∃ inp rhs i,
      some (out, rhs) = split inp i ∧
      DY.Kleene.Forall p [inp]

def attKnowsSplitRight: SubAttackerKnowledge Concat where
  pred p out :=
    ∃ inp lhs i,
      some (lhs, out) = split inp i ∧
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
  : lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
:= by
  intro h_lhs h_rhs
  apply Bytes.AttackerKnows.prove attKnowsConcat
  simp only [attKnowsConcat, Kleene.Forall]
  grind

theorem attacker_knows_split
  (buf: Bytes) (i: Nat) (tr: Trace α)
  : buf.AttackerKnows tr →
    match split buf i with
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

def Concat.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Concat.invariants where

abbrev invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs invariants := Concat.Concat.invariantsProofs

variable [BytesInvariants] [BytesInvariants.Has invariants]
variable [BytesLength]

@[simp]
theorem concat.WellFormed
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
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
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : match split buf i with
    | none => True
    | some (lhs, rhs) =>
      buf.WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
:= by
  split
  · trivial
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq]
  simp

@[simp]
theorem split.label
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : match split buf i with
    | none => True
    | some (lhs, rhs) =>
      buf.label tr = Label.meet (lhs.label tr) (rhs.label tr)
:= by
  split
  · trivial
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq]
  simp

@[simp]
theorem split.Invariant
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : buf.Invariant tr →
    match split buf i with
    | none => True
    | some (lhs, rhs) =>
      lhs.Invariant tr ∧ rhs.Invariant tr
:= by
  intro h_buf
  split
  · trivial
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq] at h_buf
  simp_all

end Invariants

section AttackerKnowledgeTheorem

variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesLength]
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
    intro out tr h_tr ⟨inp, rhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

instance: SubAttackerKnowledgeTheorem attKnowsSplitRight where
  pf := by
    simp only [attKnowsSplitRight]
    intro out tr h_tr ⟨inp, lhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

instance: ∀ id, SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsConcat)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsSplitLeft)
  | 2 => inferInstanceAs (SubAttackerKnowledgeTheorem attKnowsSplitRight)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' attackerKnowledge.internal))

end AttackerKnowledgeTheorem

end DY.Concat
