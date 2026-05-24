/-
  This module allows to define modularly
  the computations that may perform a Dolev-Yao attacker.
-/

module

public import DY.Kleene
public import DY.Bytes.Basic
public import DY.Trace.Basic
public import DY.Trace.BaseAttackerKnowledge
public meta import DY.Meta.CombineMacro

namespace DY

variable [BytesFunctor]

/--
  The attacker knowledge is ultimately defined as a Kleene fixpoint,
  and `SubAttackerKnowledge` is a component of this fixpoint computation.

  For example, to say that the attacker is allowed to concatenate bytes,
  we can write:

    -- attacker knows `out` when
    pred p out :=
      ∃ lhs rhs,
        -- `out` is the concatenation of `lhs` and `rhs` and
        out = concat lhs rhs ∧
        p lhs ∧ -- the attacker knows lhs and
        p rhs   -- the attacker knows rhs.

  To prove the scott-continuity of `pred` (a technical requirement for Kleene fixpoint)
  it is better to use the `Forall` predicate like this:

    pred p out :=
      ∃ lhs rhs,
        out = concat lhs rhs ∧
        DY.Kleene.Forall p [lhs, rhs]

  This allows to rely on the lemma `DY.Kleene.isScottContinuous_Forall_lemma`,
  and allow for `pred_isScottContinuous` to be proved automatically by our tactic script.

  The `SubF` parameter is not useful in this definition.
  It is only for hygiene, to make sure we don't miss equational theories
  by using `SubAttackerKnowledge.combine`
-/

public
structure SubAttackerKnowledge (SubF: Type → Type) where
  pred: (Bytes → Prop) → Bytes → Prop
  pred_isScottContinuous: DY.Kleene.IsScottContinuous pred := by
    intro chain h_chain
    funext buf
    simp only [eq_iff_iff]
    constructor
    · try simp [DY.Kleene.isScottContinuous_Forall_lemma chain h_chain]
      try simp [DY.Kleene.Chain.union, DY.Kleene.Chain.map]
      try grind
    · try simp [DY.Kleene.Forall, DY.Kleene.Chain.union, DY.Kleene.Chain.map]
      try grind

public
class AttackerKnowledge where
  attackerKnowledge: SubAttackerKnowledge BytesF

public
class AttackerKnowledge.HasStep
  {SubF1: Type → Type}
  {SubF2: semiOutParam (Type → Type)}
  (att1: SubAttackerKnowledge SubF1)
  (att2: semiOutParam (SubAttackerKnowledge SubF2))
where
  pf: ∀ p b, att1.pred p b → att2.pred p b

public
class AttackerKnowledge.Has
  [AttackerKnowledge]
  {SubF: Type → Type}
  (att: SubAttackerKnowledge SubF)
where
  pf: ∀ p b, att.pred p b → AttackerKnowledge.attackerKnowledge.pred p b

namespace AttackerKnowledge

public
instance
  [AttackerKnowledge]
  : AttackerKnowledge.Has AttackerKnowledge.attackerKnowledge
where
  pf p b := by simp

public
instance
  [AttackerKnowledge]
  {SubF1 SubF2: Type → Type}
  (att1: SubAttackerKnowledge SubF1)
  (att2: SubAttackerKnowledge SubF2)
  [inst1: AttackerKnowledge.HasStep att1 att2]
  [inst2: AttackerKnowledge.Has att2]
  : AttackerKnowledge.Has att1
where
  pf p b := by simp_all [inst1.pf, inst2.pf]

end AttackerKnowledge

public
def SubAttackerKnowledge.combine
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: ∀ id, SubAttackerKnowledge (SubFs id))
  : SubAttackerKnowledge (BytesFunctor.combine SubFs)
where
  pred := DY.Kleene.combine (fun id => (atts id).pred)
  pred_isScottContinuous := DY.Kleene.combine_isScottContinuous (fun id => (atts id).pred) (fun id => (atts id).pred_isScottContinuous)

public
def SubAttackerKnowledge.combine'
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  : SubAttackerKnowledge SubF
where
  pred := DY.Kleene.combine (fun id => (atts id).pred)
  pred_isScottContinuous := DY.Kleene.combine_isScottContinuous (fun id => (atts id).pred) (fun id => (atts id).pred_isScottContinuous)

@[expose]
public
def SubAttackerKnowledge.fromPred {SubF: Type → Type} (pred: Bytes → Prop): SubAttackerKnowledge SubF where
  pred p buf := pred buf

namespace AttackerKnowledge

public
instance
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: (id: t) → SubAttackerKnowledge (SubFs id))
  (id: t)
  : AttackerKnowledge.HasStep (atts id) (SubAttackerKnowledge.combine atts)
where
  pf p b := by
    simp [SubAttackerKnowledge.combine, Kleene.combine]
    intro
    exists id

public
instance
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  (id: t)
  : AttackerKnowledge.HasStep (atts id) (SubAttackerKnowledge.combine' atts)
where
  pf p b := by
    simp [SubAttackerKnowledge.combine', Kleene.combine]
    intro
    exists id

end AttackerKnowledge

public
def Bytes.AttackerKnows.baseKnowledge [ExecTraceTypes] [BaseAttackerKnowledge] (tr: ExecTrace): SubAttackerKnowledge BytesF :=
  SubAttackerKnowledge.fromPred tr.BaseAttackerKnows

def Bytes.AttackerKnows.attackerKnowledge [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge] (tr: ExecTrace): SubAttackerKnowledge BytesF :=
  SubAttackerKnowledge.combine' (fun (id: Fin 2) =>
    match id with
    | 0 => AttackerKnowledge.attackerKnowledge
    | 1 => baseKnowledge tr
  )

public
def Bytes.AttackerKnows [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge] (b: Bytes) (tr: ExecTrace): Prop :=
  Kleene.mkWeakestFixpoint ((Bytes.AttackerKnows.attackerKnowledge tr).pred) b

def Bytes.AttackerKnows.attackerKnow.prove
  [ExecTraceTypes]
  [BaseAttackerKnowledge] [AttackerKnowledge]
  {SubF: Type → Type}
  (att: SubAttackerKnowledge SubF)
  [inst: AttackerKnowledge.Has att]
  (p: Bytes → Prop)
  (b: Bytes) (tr: ExecTrace)
  : att.pred p b → (Bytes.AttackerKnows.attackerKnowledge tr).pred p b
:= by
  unfold Bytes.AttackerKnows.attackerKnowledge SubAttackerKnowledge.combine' Kleene.combine
  have := inst.pf p b
  simp
  grind

def Bytes.AttackerKnows.attackerKnow.prove_from_base
  [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]
  (p: Bytes → Prop)
  (b: Bytes) (tr: ExecTrace)
  : tr.BaseAttackerKnows b →
    (Bytes.AttackerKnows.attackerKnowledge tr).pred p b
:= by
  unfold Bytes.AttackerKnows.attackerKnowledge SubAttackerKnowledge.combine' Kleene.combine
  intro h
  dsimp only
  refine ⟨ 1, ?_ ⟩
  dsimp only [baseKnowledge, SubAttackerKnowledge.fromPred]
  exact h

public
theorem Bytes.AttackerKnows_le
  [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]
  (b: Bytes) (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    b.AttackerKnows tr1 →
    b.AttackerKnows tr2
:= by
  intro h_le
  apply Kleene.mkWeakestFixpoint_is_weakest ((Bytes.AttackerKnows.attackerKnowledge tr1).pred) ((Bytes.AttackerKnows.attackerKnowledge tr1).pred_isScottContinuous)
  simp only [Subset, AttackerKnows.attackerKnowledge, SubAttackerKnowledge.combine', Kleene.combine, Fin.exists_fin_two]
  intro b
  intro h; cases h
  · have h2 := Kleene.mkWeakestFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr2).pred (Bytes.AttackerKnows.attackerKnowledge tr2).pred_isScottContinuous
    unfold Bytes.AttackerKnows at *
    rewrite [← h2]
    simp_all [AttackerKnows.attackerKnowledge, SubAttackerKnowledge.combine', Kleene.combine]
  · have h0: Trace.BaseAttackerKnows tr2 b := by
      grind [AttackerKnows.baseKnowledge, SubAttackerKnowledge.fromPred, AttackerKnows.baseKnowledge]
    have h1 := Bytes.AttackerKnows.attackerKnow.prove_from_base (Bytes.AttackerKnows · tr2) b tr2 h0
    have h2 := Kleene.mkWeakestFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr2).pred (Bytes.AttackerKnows.attackerKnowledge tr2).pred_isScottContinuous
    unfold Bytes.AttackerKnows at *
    simp_all

grind_pattern Bytes.AttackerKnows_le => tr1 ≤ tr2, b.AttackerKnows tr1

/--
  Main theorem to prove that the attacker knows some particular value
-/
public
theorem Bytes.AttackerKnows.prove
  [ExecTraceTypes]
  [BaseAttackerKnowledge] [AttackerKnowledge]
  {SubF: Type → Type}
  (att: SubAttackerKnowledge SubF)
  [AttackerKnowledge.Has att]
  (b: Bytes) (tr: ExecTrace)
  : att.pred (Bytes.AttackerKnows · tr) b →
    Bytes.AttackerKnows b tr
:= by
  intro h
  have h1 := Bytes.AttackerKnows.attackerKnow.prove att (Bytes.AttackerKnows · tr) b tr h
  have h2 := Kleene.mkWeakestFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr).pred (Bytes.AttackerKnows.attackerKnowledge tr).pred_isScottContinuous
  unfold Bytes.AttackerKnows at *
  simp_all

public
theorem Bytes.AttackerKnows.prove_from_base
  [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]
  (b: Bytes) (tr: ExecTrace)
  : tr.BaseAttackerKnows b →
    Bytes.AttackerKnows b tr
:= by
  intro h
  have h1 := Bytes.AttackerKnows.attackerKnow.prove_from_base (Bytes.AttackerKnows · tr) b tr h
  have h2 := Kleene.mkWeakestFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr).pred (Bytes.AttackerKnows.attackerKnowledge tr).pred_isScottContinuous
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

  We can use `SubAttackerKnowledge.Implies` to modularly prove that a predicate `P` satisfy this property.
-/
@[expose]
public
def SubAttackerKnowledge.Implies {SubF: Type → Type} (att: SubAttackerKnowledge SubF) (p: Bytes → Prop): Prop :=
  ∀ b, att.pred p b → p b

public
theorem SubAttackerKnowledge.combine'.implies
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  (p: Bytes → Prop)
  (pfs: ∀ id, SubAttackerKnowledge.Implies (atts id) p)
  : SubAttackerKnowledge.Implies (SubAttackerKnowledge.combine' atts) p
:= by
  intro b
  simp only [SubAttackerKnowledge.combine', Kleene.combine, forall_exists_index]
  intro id
  exact pfs id b

public
theorem SubAttackerKnowledge.combine.implies
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: ∀ id, SubAttackerKnowledge (SubFs id))
  (p: Bytes → Prop)
  (pfs: ∀ id, SubAttackerKnowledge.Implies (atts id) p)
  : SubAttackerKnowledge.Implies (SubAttackerKnowledge.combine atts) p
:= by
  intro b
  simp only [SubAttackerKnowledge.combine, Kleene.combine, forall_exists_index]
  intro id
  exact pfs id b

public
theorem Bytes.AttackerKnows.is_least_fixpoint
  [ExecTraceTypes]
  [BaseAttackerKnowledge] [AttackerKnowledge]
  (pred: Bytes → Prop)
  (b: Bytes) (tr: ExecTrace)
  (pf1: SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge pred)
  (pf2: SubAttackerKnowledge.Implies (Bytes.AttackerKnows.baseKnowledge tr) pred)
  : Bytes.AttackerKnows b tr →
    pred b
:=
  Kleene.mkWeakestFixpoint_is_weakest ((Bytes.AttackerKnows.attackerKnowledge tr).pred) ((Bytes.AttackerKnows.attackerKnowledge tr).pred_isScottContinuous) pred (by
    simp [Subset, attackerKnowledge, SubAttackerKnowledge.combine', Kleene.combine]
    intro b
    have := pf1 b
    have := pf2 b
    grind
  ) b

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* attackerKnowledge $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `attackerKnowledge
      refereeName := `SubF
      combineName := ``DY.SubAttackerKnowledge.combine
      outTypeName := ``DY.SubAttackerKnowledge
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine
      hasStepName := ``DY.AttackerKnowledge.HasStep
    }

    let attStx := Lean.mkIdent `attackerKnowledge
    let topLevelInst ← `(command| public instance: DY.AttackerKnowledge where attackerKnowledge := $attStx)
    let topLevelHas ← `(command| public instance: DY.AttackerKnowledge.Has $attStx := inferInstanceAs (DY.AttackerKnowledge.Has DY.AttackerKnowledge.attackerKnowledge))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel)

macro_rules
  | `(command| #combine_one $_options* attackerKnowledge' $params* from $sources,*) => do
    -- options.toplevel does not make sense in this case, hence we ignore it
    let params := #[(← `(bracketedBinder| [DY.BytesFunctor]))] ++ params
    let sources := sources.getElems

    let subfStx := Lean.mkIdent `SubF
    let combined ← combineExplicit params sources {
      name := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine'
      internalOutTypeStx := fun args _ => `(term| DY.SubAttackerKnowledge ($subfStx $args*))
      outTypeStx := fun args => `(term| DY.SubAttackerKnowledge ($subfStx $args*))
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine'
      hasStepName := ``DY.AttackerKnowledge.HasStep
    }

    return Lean.mkNullNode (combined ++ hasStep)

end Meta.CombineMacro

end DY
