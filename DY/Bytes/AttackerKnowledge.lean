/-
  This module allows to define modularly
  the computations that may perform a Dolev-Yao attacker.
-/

module

public import DY.Misc.Fixpoint
public import DY.Bytes.Basic
public import DY.Trace.Basic
public import DY.Trace.BaseAttackerKnowledge
public meta import DY.Meta.CombineMacro

namespace DY

variable [Bytes.Def]

/--
  The attacker knowledge is ultimately defined as a fixpoint,
  and `Bytes.AttackerKnows.Part` is a component of this fixpoint computation.

  For example, to say that the attacker is allowed to concatenate bytes,
  we can write:

    -- attacker knows `out` when
    pred p out :=
      ∃ lhs rhs,
        -- `out` is the concatenation of `lhs` and `rhs` and
        out = concat lhs rhs ∧
        p lhs ∧ -- the attacker knows lhs and
        p rhs   -- the attacker knows rhs.

  The `SubF` parameter is not useful in this definition.
  It is only for hygiene, to make sure we don't miss equational theories
  by using `Bytes.AttackerKnows.combine`
-/

public
structure Bytes.AttackerKnows.Part (SubF: Type → Type) where
  pred: (Bytes → Prop) → Bytes → Prop
  pred_isMonotonic: DY.Fixpoint.IsMonotonic pred := by
    try simp [Fixpoint.IsMonotonic]
    try grind

public
class Bytes.AttackerKnows.Def where
  whole: Bytes.AttackerKnows.Part Bytes.Functor

public
class Bytes.AttackerKnows.HasStep
  {SubF1: Type → Type}
  {SubF2: semiOutParam (Type → Type)}
  (att1: Bytes.AttackerKnows.Part SubF1)
  (att2: semiOutParam (Bytes.AttackerKnows.Part SubF2))
where
  pf: ∀ p b, att1.pred p b → att2.pred p b

public
class Bytes.AttackerKnows.Has
  [Bytes.AttackerKnows.Def]
  {SubF: Type → Type}
  (att: Bytes.AttackerKnows.Part SubF)
where
  pf: ∀ p b, att.pred p b → Bytes.AttackerKnows.Def.whole.pred p b

namespace Bytes.AttackerKnows.Def

public
instance
  [Bytes.AttackerKnows.Def]
  : Bytes.AttackerKnows.Has Bytes.AttackerKnows.Def.whole
where
  pf p b := by simp

public
instance
  [Bytes.AttackerKnows.Def]
  {SubF1 SubF2: Type → Type}
  (att1: Bytes.AttackerKnows.Part SubF1)
  (att2: Bytes.AttackerKnows.Part SubF2)
  [inst1: Bytes.AttackerKnows.HasStep att1 att2]
  [inst2: Bytes.AttackerKnows.Has att2]
  : Bytes.AttackerKnows.Has att1
where
  pf p b := by simp_all [inst1.pf, inst2.pf]

end Bytes.AttackerKnows.Def

public
def Bytes.AttackerKnows.combine
  {n: Nat}
  {SubFs: Fin n → Type → Type}
  (atts: ∀ id, Bytes.AttackerKnows.Part (SubFs id))
  : Bytes.AttackerKnows.Part (Bytes.combine SubFs)
where
  pred := DY.Fixpoint.combine (fun id => (atts id).pred)
  pred_isMonotonic := DY.Fixpoint.combine_isMonotonic (fun id => (atts id).pred) (fun id => (atts id).pred_isMonotonic)

public
def Bytes.AttackerKnows.merge
  {n: Nat}
  {SubF: Type → Type}
  (atts: Fin n → Bytes.AttackerKnows.Part SubF)
  : Bytes.AttackerKnows.Part SubF
where
  pred := DY.Fixpoint.combine (fun id => (atts id).pred)
  pred_isMonotonic := DY.Fixpoint.combine_isMonotonic (fun id => (atts id).pred) (fun id => (atts id).pred_isMonotonic)

@[expose]
public
def Bytes.AttackerKnows.Part.fromPred {SubF: Type → Type} (pred: Bytes → Prop): Bytes.AttackerKnows.Part SubF where
  pred p buf := pred buf

namespace Bytes.AttackerKnows.Def

public
instance
  {n: Nat}
  {SubFs: Fin n → Type → Type}
  (atts: (id: Fin n) → Bytes.AttackerKnows.Part (SubFs id))
  (id: Fin n)
  : Bytes.AttackerKnows.HasStep (atts id) (Bytes.AttackerKnows.combine atts)
where
  pf p b := by
    simp [Bytes.AttackerKnows.combine, Fixpoint.combine]
    intro
    exists id

public
instance
  {n: Nat}
  {SubF: Type → Type}
  (atts: Fin n → Bytes.AttackerKnows.Part SubF)
  (id: Fin n)
  : Bytes.AttackerKnows.HasStep (atts id) (Bytes.AttackerKnows.merge atts)
where
  pf p b := by
    simp [Bytes.AttackerKnows.merge, Fixpoint.combine]
    intro
    exists id

end Bytes.AttackerKnows.Def

def Bytes.AttackerKnows.baseKnowledge [ExecTrace.Def] [Trace.BaseAttackerKnows.Def] (tr: ExecTrace): Bytes.AttackerKnows.Part Bytes.Functor :=
  Bytes.AttackerKnows.Part.fromPred tr.BaseAttackerKnows

def Bytes.AttackerKnows.attackerKnowledge [ExecTrace.Def] [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def] (tr: ExecTrace): Bytes.AttackerKnows.Part Bytes.Functor :=
  Bytes.AttackerKnows.merge (fun (id: Fin 2) =>
    match id with
    | 0 => Bytes.AttackerKnows.Def.whole
    | 1 => baseKnowledge tr
  )

public
def Bytes.AttackerKnows [ExecTrace.Def] [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def] (b: Bytes) (tr: ExecTrace): Prop :=
  Fixpoint.mkLeastFixpoint ((Bytes.AttackerKnows.attackerKnowledge tr).pred) b

theorem Bytes.AttackerKnows.attackerKnow.prove
  [ExecTrace.Def]
  [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  {SubF: Type → Type}
  (att: Bytes.AttackerKnows.Part SubF)
  [inst: Bytes.AttackerKnows.Has att]
  (p: Bytes → Prop)
  (b: Bytes) (tr: ExecTrace)
  : att.pred p b → (Bytes.AttackerKnows.attackerKnowledge tr).pred p b
:= by
  unfold Bytes.AttackerKnows.attackerKnowledge Bytes.AttackerKnows.merge Fixpoint.combine
  have := inst.pf p b
  simp
  grind

theorem Bytes.AttackerKnows.attackerKnow.prove_from_base
  [ExecTrace.Def] [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  (p: Bytes → Prop)
  (b: Bytes) (tr: ExecTrace)
  : tr.BaseAttackerKnows b →
    (Bytes.AttackerKnows.attackerKnowledge tr).pred p b
:= by
  unfold Bytes.AttackerKnows.attackerKnowledge Bytes.AttackerKnows.merge Fixpoint.combine
  intro h
  dsimp only
  refine ⟨ 1, ?_ ⟩
  dsimp only [baseKnowledge, Bytes.AttackerKnows.Part.fromPred]
  exact h

public
theorem Bytes.AttackerKnows_le
  [ExecTrace.Def] [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  (b: Bytes) (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    b.AttackerKnows tr1 →
    b.AttackerKnows tr2
:= by
  intro h_le
  apply Fixpoint.mkLeastFixpoint_is_least ((Bytes.AttackerKnows.attackerKnowledge tr1).pred) ((Bytes.AttackerKnows.attackerKnowledge tr1).pred_isMonotonic)
  simp only [AttackerKnows.attackerKnowledge, Bytes.AttackerKnows.merge, Fixpoint.combine, Fin.exists_fin_two]
  intro b
  intro h; cases h
  · have h2 := Fixpoint.mkLeastFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr2).pred (Bytes.AttackerKnows.attackerKnowledge tr2).pred_isMonotonic
    unfold Bytes.AttackerKnows at *
    rewrite [← h2]
    simp_all [AttackerKnows.attackerKnowledge, Bytes.AttackerKnows.merge, Fixpoint.combine]
  · have h0: Trace.BaseAttackerKnows tr2 b := by
      grind [AttackerKnows.baseKnowledge, Bytes.AttackerKnows.Part.fromPred, AttackerKnows.baseKnowledge]
    have h1 := Bytes.AttackerKnows.attackerKnow.prove_from_base (Bytes.AttackerKnows · tr2) b tr2 h0
    have h2 := Fixpoint.mkLeastFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr2).pred (Bytes.AttackerKnows.attackerKnowledge tr2).pred_isMonotonic
    unfold Bytes.AttackerKnows at *
    simp_all

grind_pattern Bytes.AttackerKnows_le => tr1 ≤ tr2, b.AttackerKnows tr1

/--
  Main theorem to prove that the attacker knows some particular value
-/
public
theorem Bytes.AttackerKnows.prove
  [ExecTrace.Def]
  [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  {SubF: Type → Type}
  (att: Bytes.AttackerKnows.Part SubF)
  [Bytes.AttackerKnows.Has att]
  (b: Bytes) (tr: ExecTrace)
  : att.pred (Bytes.AttackerKnows · tr) b →
    Bytes.AttackerKnows b tr
:= by
  intro h
  have h1 := Bytes.AttackerKnows.attackerKnow.prove att (Bytes.AttackerKnows · tr) b tr h
  have h2 := Fixpoint.mkLeastFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr).pred (Bytes.AttackerKnows.attackerKnowledge tr).pred_isMonotonic
  unfold Bytes.AttackerKnows at *
  simp_all

public
theorem Bytes.AttackerKnows.prove_from_base
  [ExecTrace.Def] [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  (b: Bytes) (tr: ExecTrace)
  : tr.BaseAttackerKnows b →
    Bytes.AttackerKnows b tr
:= by
  intro h
  have h1 := Bytes.AttackerKnows.attackerKnow.prove_from_base (Bytes.AttackerKnows · tr) b tr h
  have h2 := Fixpoint.mkLeastFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr).pred (Bytes.AttackerKnows.attackerKnowledge tr).pred_isMonotonic
  unfold Bytes.AttackerKnows at *
  simp_all

/--
  The attacker knowledge `AttackerKnows` is the weakest predicate `P` such that every sub-attacker knowledge predicate `att`,
    att.pred P b
  implies
    P b

  The attacker knowledge satisfies this property: this is the theorem by `Bytes.AttackerKnows.prove`
  The attacker knowledge is the weakest predicate: this is the theorem `Bytes.AttackerKnows.is_least_fixpoint`.
  In other words, if a predicate `P` has this property, then `Bytes.AttackerKnows b => P b`

  We can use `Bytes.AttackerKnows.Part.Implies` to modularly prove that a predicate `P` satisfy this property.
-/
@[expose]
public
def Bytes.AttackerKnows.Part.Implies {SubF: Type → Type} (att: Bytes.AttackerKnows.Part SubF) (p: Bytes → Prop): Prop :=
  ∀ b, att.pred p b → p b

public
theorem Bytes.AttackerKnows.merge.implies
  {n: Nat}
  {SubF: Type → Type}
  (atts: Fin n → Bytes.AttackerKnows.Part SubF)
  (p: Bytes → Prop)
  (pfs: ∀ id, Bytes.AttackerKnows.Part.Implies (atts id) p)
  : Bytes.AttackerKnows.Part.Implies (Bytes.AttackerKnows.merge atts) p
:= by
  intro b
  simp only [Bytes.AttackerKnows.merge, Fixpoint.combine, forall_exists_index]
  intro id
  exact pfs id b

public
theorem Bytes.AttackerKnows.combine.implies
  {n: Nat}
  {SubFs: Fin n → Type → Type}
  (atts: ∀ id, Bytes.AttackerKnows.Part (SubFs id))
  (p: Bytes → Prop)
  (pfs: ∀ id, Bytes.AttackerKnows.Part.Implies (atts id) p)
  : Bytes.AttackerKnows.Part.Implies (Bytes.AttackerKnows.combine atts) p
:= by
  intro b
  simp only [Bytes.AttackerKnows.combine, Fixpoint.combine, forall_exists_index]
  intro id
  exact pfs id b

public
theorem Bytes.AttackerKnows.is_least_fixpoint
  [ExecTrace.Def]
  [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]
  (pred: Bytes → Prop)
  (b: Bytes) (tr: ExecTrace)
  (pf1: Bytes.AttackerKnows.Part.Implies Bytes.AttackerKnows.Def.whole pred)
  (pf2: ∀ b, tr.BaseAttackerKnows b → pred b)
  : Bytes.AttackerKnows b tr →
    pred b
:=
  Fixpoint.mkLeastFixpoint_is_least ((Bytes.AttackerKnows.attackerKnowledge tr).pred) ((Bytes.AttackerKnows.attackerKnowledge tr).pred_isMonotonic) pred (by
    simp only [attackerKnowledge, baseKnowledge, Bytes.AttackerKnows.Part.fromPred, Bytes.AttackerKnows.merge, Fixpoint.combine]
    intro b
    have := pf1 b
    have := pf2 b
    grind
  ) b

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* Bytes.AttackerKnows $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.Bytes.Def]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `attackerKnows
      refereeName := `BytesPart.Functor
      combineName := ``DY.Bytes.AttackerKnows.combine
      outTypeName := ``DY.Bytes.AttackerKnows.Part
      isTheorem := false
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `attackerKnows
      combineName := ``DY.Bytes.AttackerKnows.combine
      hasStepName := ``DY.Bytes.AttackerKnows.HasStep
    }

    let attStx := Lean.mkIdent `attackerKnows
    let topLevelInst ← `(command| public instance: DY.Bytes.AttackerKnows.Def where whole := $attStx)
    let topLevelHas ← `(command| public instance: DY.Bytes.AttackerKnows.Has $attStx := inferInstanceAs (DY.Bytes.AttackerKnows.Has DY.Bytes.AttackerKnows.Def.whole))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel)

macro_rules
  | `(command| #combine_one $_options* Bytes.AttackerKnows.merge $params* from $sources,*) => do
    -- options.toplevel does not make sense in this case, hence we ignore it
    let params := #[(← `(bracketedBinder| [DY.Bytes.Def]))] ++ params
    let sources := sources.getElems

    let subfStx := Lean.mkIdent `BytesPart.Functor
    let combined ← combineExplicit params sources {
      name := `attackerKnows
      combineName := ``DY.Bytes.AttackerKnows.merge
      internalOutTypeStx := fun args _ => `(term| DY.Bytes.AttackerKnows.Part ($subfStx $args*))
      outTypeStx := fun args => `(term| DY.Bytes.AttackerKnows.Part ($subfStx $args*))
      isTheorem := false
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `attackerKnows
      combineName := ``DY.Bytes.AttackerKnows.merge
      hasStepName := ``DY.Bytes.AttackerKnows.HasStep
    }

    return Lean.mkNullNode (combined ++ hasStep)

end Meta.CombineMacro

end DY
