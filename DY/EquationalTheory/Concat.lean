module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.Concat

public
class CanConcat (Bytes: Type u) where
  concat: Bytes → Bytes → Bytes
  split: Bytes → Nat → Option (Bytes × Bytes)

export CanConcat (concat)
export CanConcat (split)

section Constructors

namespace Concat

public
structure BytesPart.Functor (Bytes: Type) where
  lhs: Bytes
  rhs: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {lhs, rhs} => sizeOf lhs + sizeOf rhs

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun { lhs, rhs } rec =>
    rec lhs + rec rhs

end Concat

#combine into Bytes, Bytes.length from
  Concat,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [Bytes.length.Def]

public
abbrev Concat.BytesPart.Functor.pack (x: Concat.BytesPart.Functor Bytes) := BytesView.pack x

public
instance: CanConcat Bytes where
  concat lhs rhs := ({lhs, rhs}: Concat.BytesPart.Functor Bytes).pack

  split buf i :=
    match buf.view? Concat.BytesPart.Functor with
    | some ({ lhs, rhs }) =>
      if lhs.length = i then
        some (lhs, rhs)
      else
        none
    | none => none

public
theorem split_concat
  (lhs rhs: Bytes)
  : split (concat lhs rhs) (lhs.length) = some (lhs, rhs)
:= by
  simp only [split, concat]
  grind

public
theorem concat_split
  (buf: Bytes) (i: Nat) (lhs rhs: Bytes)
  : split buf i = some (lhs, rhs) → concat lhs rhs = buf
:= by
  simp only [concat, split]
  grind

@[simp]
public
theorem length_concat
  [Bytes.length.Has BytesPart.length]
  (lhs rhs: Bytes)
  : Bytes.length (concat lhs rhs) = Bytes.length lhs + Bytes.length rhs
:= by
  simp only [concat]
  grind [Concat.BytesPart.length]

@[simp]
public
theorem length_split
  [Bytes.length.Has BytesPart.length]
  (buf: Bytes) (i: Nat) (lhs rhs: Bytes)
  : split buf i = some (lhs, rhs) →
    (Bytes.length lhs = i ∧ i+Bytes.length rhs = Bytes.length buf)
:= by
  simp only [split]
  grind [Concat.BytesPart.length]

end Constructors

section AttackerKnowledge

public
def concat.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor] [Bytes.length.Def]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      p lhs ∧
      p rhs

public
def splitLeft.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor] [Bytes.length.Def]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ inp rhs i,
      some (out, rhs) = split inp i ∧
      p inp

public
def splitRight.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor] [Bytes.length.Def]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ inp lhs i,
      some (lhs, out) = split inp i ∧
      p inp

#combine [Bytes.Has BytesPart.Functor] [Bytes.length.Def] into Bytes.AttackerKnows.merge from
  concat,
  splitLeft,
  splitRight


variable [Bytes.Def] [Bytes.Has BytesPart.Functor] [Bytes.length.Def]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows.Has attackerKnows]

public
theorem attacker_knows_concat
  (lhs rhs: Bytes) (tr: ExecTrace)
  : lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
:= by
  intro h_lhs h_rhs
  apply Bytes.AttackerKnows.prove concat.attackerKnows
  simp only [concat.attackerKnows]
  grind

public
theorem attacker_knows_split
  (buf: Bytes) (i: Nat) (tr: ExecTrace)
  : buf.AttackerKnows tr →
    match split buf i with
    | none => True
    | some (lhs, rhs) =>
      lhs.AttackerKnows tr ∧
      rhs.AttackerKnows tr
:= by
  intro h_buf
  split
  · grind
  rename_i lhs rhs _
  constructor
  · apply Bytes.AttackerKnows.prove splitLeft.attackerKnows
    simp only [splitLeft.attackerKnows]
    grind
  · apply Bytes.AttackerKnows.prove splitRight.attackerKnows
    simp only [splitRight.attackerKnows]
    grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]

public
def Concat.BytesPart.invariants: Bytes.Invariants.Part Concat.BytesPart.Functor where
  well_formed := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

  usage := fun {lhs, rhs} rec tr => Usage.nothing

  label := fun {lhs, rhs} rec tr =>
    Label.meet ((rec lhs) tr) ((rec rhs) tr)

  invariant := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

public
theorem Concat.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful Concat.BytesPart.invariants where

end Definition

#combine into
  Bytes.Invariants,
  Bytes.Invariants.Lawful
from
  Concat,


variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [Bytes.length.Def]

@[simp]
public
theorem concat.WellFormed
  [Bytes.WellFormed.Def] [Bytes.WellFormed.Has Concat.BytesPart.invariants.well_formed]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
:= by
  simp [concat, Bytes.WellFormed.eq, Concat.BytesPart.invariants]

@[simp]
public
theorem concat.label
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).label tr = Label.meet (lhs.label tr) (rhs.label tr)
:= by
  simp [concat, Bytes.label.eq, Concat.BytesPart.invariants]

@[simp]
public
theorem concat.Invariant
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).Invariant tr = (lhs.Invariant tr ∧ rhs.Invariant tr)
:= by
  simp [concat, Bytes.Invariant.eq, Concat.BytesPart.invariants]

@[simp]
public
theorem split.WellFormed
  [Bytes.WellFormed.Def] [Bytes.WellFormed.Has Concat.BytesPart.invariants.well_formed]
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : match split buf i with
    | none => True
    | some (lhs, rhs) =>
      buf.WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
:= by
  split
  · grind
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq]
  simp

@[simp]
public
theorem split.label
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : match split buf i with
    | none => True
    | some (lhs, rhs) =>
      buf.label tr = Label.meet (lhs.label tr) (rhs.label tr)
:= by
  split
  · grind
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq]
  simp

@[simp]
public
theorem split.Invariant
  [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : buf.Invariant tr →
    match split buf i with
    | none => True
    | some (lhs, rhs) =>
      lhs.Invariant tr ∧ rhs.Invariant tr
:= by
  intro h_buf
  split
  · grind
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq] at h_buf
  simp_all

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes.Has BytesPart.Functor]
variable [Bytes.length.Def]
variable [Bytes.Invariants.Has BytesPart.invariants]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part concat.attackerKnows where
  pf := by
    simp only [concat.attackerKnows]
    intro out tr h_tr ⟨lhs, rhs, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

public
instance: Bytes.AttackerKnows_implies_Publishable.Part splitLeft.attackerKnows where
  pf := by
    simp only [splitLeft.attackerKnows]
    intro out tr h_tr ⟨inp, rhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

public
instance: Bytes.AttackerKnows_implies_Publishable.Part splitRight.attackerKnows where
  pf := by
    simp only [splitRight.attackerKnows]
    intro out tr h_tr ⟨inp, lhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [Bytes.length.Def] [Bytes.Has BytesPart.Functor] [Bytes.Invariants.Has BytesPart.invariants] into Bytes.AttackerKnows_implies_Publishable.merge from
  concat,
  splitLeft,
  splitRight,

end AttackerKnowledgeTheorem

end DY.Concat
