import DY.Kleene
import DY.Bytes.Type
import DY.Trace.Type

/-
  This module allows to define modularly
  the computations that may perform a Dolev-Yao attacker.
-/

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

class AttackerKnowledge where
  attackerKnowledge: SubAttackerKnowledge BytesF

class AttackerKnowledge.HasStep
  {SubF1: Type → Type}
  {SubF2: semiOutParam (Type → Type)}
  (att1: SubAttackerKnowledge SubF1)
  (att2: semiOutParam (SubAttackerKnowledge SubF2))
where
  pf: ∀ p b, att1.pred p b → att2.pred p b

class AttackerKnowledge.Has
  [AttackerKnowledge]
  {SubF: Type → Type}
  (att: SubAttackerKnowledge SubF)
where
  pf: ∀ p b, att.pred p b → AttackerKnowledge.attackerKnowledge.pred p b

namespace AttackerKnowledge

instance
  [AttackerKnowledge]
  : AttackerKnowledge.Has AttackerKnowledge.attackerKnowledge
where
  pf p b := by simp

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

def SubAttackerKnowledge.combine
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: ∀ id, SubAttackerKnowledge (SubFs id))
  : SubAttackerKnowledge (BytesFunctor.combine SubFs)
where
  pred := DY.Kleene.combine (fun id => (atts id).pred)
  pred_isScottContinuous := DY.Kleene.combine_isScottContinuous (fun id => (atts id).pred) (fun id => (atts id).pred_isScottContinuous)

def SubAttackerKnowledge.combine'
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  : SubAttackerKnowledge SubF
where
  pred := DY.Kleene.combine (fun id => (atts id).pred)
  pred_isScottContinuous := DY.Kleene.combine_isScottContinuous (fun id => (atts id).pred) (fun id => (atts id).pred_isScottContinuous)

def SubAttackerKnowledge.fromPred {SubF: Type → Type} (pred: Bytes → Prop): SubAttackerKnowledge SubF where
  pred p buf := pred buf

namespace AttackerKnowledge

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

-- TODO
opaque Trace.MessageSent (tr: Trace α) (b: Bytes): Prop
axiom Trace.MessageSent_erase (tr: Trace α) (b: Bytes): tr.MessageSent b = tr.erase.MessageSent b

def Bytes.AttackerKnows.baseKnowledge (tr: Trace α): SubAttackerKnowledge BytesF :=
  SubAttackerKnowledge.fromPred tr.MessageSent

def Bytes.AttackerKnows.attackerKnowledge [AttackerKnowledge] (tr: Trace α): SubAttackerKnowledge BytesF :=
  SubAttackerKnowledge.combine' (fun (id: Fin 2) =>
    match id with
    | 0 => AttackerKnowledge.attackerKnowledge
    | 1 => baseKnowledge tr
  )

def Bytes.AttackerKnows [AttackerKnowledge] (b: Bytes) (tr: Trace α): Prop :=
  Kleene.mkWeakestFixpoint ((Bytes.AttackerKnows.attackerKnowledge tr).pred) b

def Bytes.AttackerKnows.attackerKnow.prove
  [AttackerKnowledge]
  {SubF: Type → Type}
  (att: SubAttackerKnowledge SubF)
  [inst: AttackerKnowledge.Has att]
  (p: Bytes → Prop)
  (b: Bytes) (tr: Trace α)
  : att.pred p b → (Bytes.AttackerKnows.attackerKnowledge tr).pred p b
:= by
  unfold Bytes.AttackerKnows.attackerKnowledge SubAttackerKnowledge.combine' Kleene.combine
  have := inst.pf p b
  simp
  grind

/--
  Main theorem to prove that the attacker knows some particular value
-/
theorem Bytes.AttackerKnows.prove
  [AttackerKnowledge]
  {SubF: Type → Type}
  (att: SubAttackerKnowledge SubF)
  [AttackerKnowledge.Has att]
  (b: Bytes) (tr: Trace α)
  : att.pred (Bytes.AttackerKnows · tr) b →
    Bytes.AttackerKnows b tr
:= by
  intro h
  have h1 := Bytes.AttackerKnows.attackerKnow.prove att (Bytes.AttackerKnows · tr) b tr h
  have h2 := Kleene.mkWeakestFixpoint_is_fixpoint (Bytes.AttackerKnows.attackerKnowledge tr).pred (Bytes.AttackerKnows.attackerKnowledge tr).pred_isScottContinuous
  unfold Bytes.AttackerKnows at *
  grind

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
def SubAttackerKnowledge.Implies {SubF: Type → Type} (att: SubAttackerKnowledge SubF) (p: Bytes → Prop): Prop :=
  ∀ b, att.pred p b → p b

def SubAttackerKnowledge.combine'.implies
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

def SubAttackerKnowledge.combine.implies
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

theorem Bytes.AttackerKnows.is_least_fixpoint
  [AttackerKnowledge]
  (pred: Bytes → Prop)
  (b: Bytes) (tr: Trace α)
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

theorem Bytes.AttackerKnows.pred_trace_erase [AttackerKnowledge] (tr: Trace α) (b: Bytes):
  b.AttackerKnows tr = b.AttackerKnows (tr.erase)
:= by
  simp only [Bytes.AttackerKnows, Bytes.AttackerKnows.attackerKnowledge]
  congr
  funext
  split
  · rfl
  · simp only [Bytes.AttackerKnows.baseKnowledge]
    congr 1
    funext
    apply Trace.MessageSent_erase

end DY
