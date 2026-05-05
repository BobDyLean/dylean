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
structure SubF (Bytes: Type) where
  lhs: Bytes
  rhs: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {lhs, rhs} => sizeOf lhs + sizeOf rhs

public
instance: ALaCarte.Representable SubF where
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

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { lhs, rhs } rec =>
    rec lhs + rec rhs

end Concat

#combine into BytesFunctor, BytesLength from
  Concat,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesLength]

public
abbrev Concat.SubF.pack (x: Concat.SubF Bytes) := BytesView.pack x

public
instance: CanConcat Bytes where
  concat lhs rhs := ({lhs, rhs}: Concat.SubF Bytes).pack

  split buf i :=
    match buf.view? Concat.SubF with
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
  [BytesLength.Has SubF.length]
  (lhs rhs: Bytes)
  : Bytes.length (concat lhs rhs) = Bytes.length lhs + Bytes.length rhs
:= by
  simp only [concat]
  grind [Concat.SubF.length]

@[simp]
public
theorem length_split
  [BytesLength.Has SubF.length]
  (buf: Bytes) (i: Nat) (lhs rhs: Bytes)
  : split buf i = some (lhs, rhs) →
    (Bytes.length lhs = i ∧ i+Bytes.length rhs = Bytes.length buf)
:= by
  simp only [split]
  grind [Concat.SubF.length]

end Constructors

section AttackerKnowledge

public
def concat.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      DY.Kleene.Forall p [lhs, rhs]

public
def splitLeft.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ inp rhs i,
      some (out, rhs) = split inp i ∧
      DY.Kleene.Forall p [inp]

public
def splitRight.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ inp lhs i,
      some (lhs, out) = split inp i ∧
      DY.Kleene.Forall p [inp]

#combine [BytesFunctor.Has SubF] [BytesLength] into attackerKnowledge' from
  concat,
  splitLeft,
  splitRight


variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_concat
  (lhs rhs: Bytes) (tr: ExecTrace)
  : lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
:= by
  intro h_lhs h_rhs
  apply Bytes.AttackerKnows.prove concat.attackerKnowledge
  simp only [concat.attackerKnowledge, Kleene.Forall]
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
  · trivial
  rename_i lhs rhs _
  constructor
  · apply Bytes.AttackerKnows.prove splitLeft.attackerKnowledge
    simp only [splitLeft.attackerKnowledge, Kleene.Forall]
    grind
  · apply Bytes.AttackerKnows.prove splitRight.attackerKnowledge
    simp only [splitRight.attackerKnowledge, Kleene.Forall]
    grind

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def Concat.invariants: Bytes.PartialInvariants Concat.SubF where
  well_formed := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

  usage := fun {lhs, rhs} rec tr => Usage.nothing

  label := fun {lhs, rhs} rec tr =>
    Label.meet ((rec lhs) tr) ((rec rhs) tr)

  invariant := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

public
def Concat.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Concat.invariants where

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  Concat,

variable [BytesLength]

@[simp]
public
theorem concat.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has Concat.invariants.well_formed]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
:= by
  simp [concat, Bytes.WellFormed.eq, Concat.invariants]

@[simp]
public
theorem concat.label
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).label tr = Label.meet (lhs.label tr) (rhs.label tr)
:= by
  simp [concat, Bytes.label.eq, Concat.invariants]

@[simp]
public
theorem concat.Invariant
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).Invariant tr = (lhs.Invariant tr ∧ rhs.Invariant tr)
:= by
  simp [concat, Bytes.Invariant.eq, Concat.invariants]

@[simp]
public
theorem split.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has Concat.invariants.well_formed]
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
public
theorem split.label
  [BytesInvariants] [BytesInvariants.Has invariants]
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
public
theorem split.Invariant
  [BytesInvariants] [BytesInvariants.Has invariants]
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

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesLength]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem concat.attackerKnowledge where
  pf := by
    simp only [concat.attackerKnowledge]
    intro out tr h_tr ⟨lhs, rhs, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    grind

public
instance: SubAttackerKnowledgeTheorem splitLeft.attackerKnowledge where
  pf := by
    simp only [splitLeft.attackerKnowledge]
    intro out tr h_tr ⟨inp, rhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

public
instance: SubAttackerKnowledgeTheorem splitRight.attackerKnowledge where
  pf := by
    simp only [splitRight.attackerKnowledge]
    intro out tr h_tr ⟨inp, lhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Kleene.Forall] at h_inputs
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesLength] [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  concat,
  splitLeft,
  splitRight,

end AttackerKnowledgeTheorem

end DY.Concat
