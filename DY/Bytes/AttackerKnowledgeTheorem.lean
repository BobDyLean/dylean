/-
  This module allows to modularly prove the attacker knowledge theorem:
  this is a key theorem in the DyLean methodology,
  saying for traces that satisfy the trace invariant,
  if the attacker knows a `Bytes`,
  then this `Bytes` must be publishable.
-/

module

public import DY.Bytes.Basic
public import DY.Bytes.Invariants
public import DY.Bytes.AttackerKnowledge
public import DY.Trace
public meta import DY.Meta.CombineMacro

namespace DY

variable [Bytes.Def]
variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Invariants.Def]

public
class Bytes.AttackerKnows_implies_Publishable.Part {SubF: Type → Type} (att: Bytes.AttackerKnows.Part SubF) where
  pf: ∀ b: Bytes, ∀ tr: ProofTrace, tr.Invariant → att.pred (·.Publishable tr) b → b.Publishable tr

public
class Bytes.AttackerKnows_implies_Publishable.Proof [Bytes.AttackerKnows.Def] where
  whole: Bytes.AttackerKnows_implies_Publishable.Part (Bytes.AttackerKnows.Def.whole)

section AttackerKnowledgeTheorem

public
instance
  {SubF: Type → Type}
  {n: Nat}
  (atts: Fin n → Bytes.AttackerKnows.Part SubF)
  [pfs: ∀ id, Bytes.AttackerKnows_implies_Publishable.Part (atts id)]
  : Bytes.AttackerKnows_implies_Publishable.Part (Bytes.AttackerKnows.merge atts)
where
  pf := by
    intro b tr h_tr
    apply Bytes.AttackerKnows.merge.implies
    intro id b
    exact (pfs id).pf b tr h_tr

public
instance
  {n: Nat}
  {SubFs: Fin n → Type → Type}
  (atts: ∀ id, Bytes.AttackerKnows.Part (SubFs id))
  [pfs: ∀ id, Bytes.AttackerKnows_implies_Publishable.Part (atts id)]
  : Bytes.AttackerKnows_implies_Publishable.Part (Bytes.AttackerKnows.combine atts)
where
  pf := by
    intro b tr h_tr
    apply Bytes.AttackerKnows.combine.implies
    intro id b
    exact (pfs id).pf b tr h_tr

end AttackerKnowledgeTheorem

public
theorem Bytes.AttackerKnows_implies_Publishable
  [Bytes.Invariants.Lawful]
  [Bytes.AttackerKnows.Def] [Trace.BaseAttackerKnows.Def]
  [inst: Bytes.AttackerKnows_implies_Publishable.Proof]
  [Trace.BaseAttackerKnows_implies_Publishable.Proof]
  (b: Bytes) (tr: ProofTrace)
  : tr.Invariant →
    Bytes.AttackerKnows b tr.erase →
    b.Publishable tr
:= by
  intro h_tr
  apply Bytes.AttackerKnows.is_least_fixpoint (·.Publishable tr) b tr.erase
  · intro b
    exact inst.whole.pf b tr h_tr
  · intro b
    apply Trace.BaseAttackerKnows_implies_Publishable
    assumption

grind_pattern Bytes.AttackerKnows_implies_Publishable => Bytes.AttackerKnows b tr.erase

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* Bytes.AttackerKnows_implies_Publishable $params* from $sources,*) => do
    let options := parseOptions options
    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.Bytes.Def])),
      (← `(bracketedBinder| [DY.ExecTrace.Def])),
      (← `(bracketedBinder| [DY.ProofTrace.Def])),
      (← `(bracketedBinder| [DY.Trace.Invariant.Def])),
      (← `(bracketedBinder| [DY.Bytes.Invariants.Def])),
    ]
    let params := if options.toplevel then params else baseGlobalInstances ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources <| .makeSimple {
      refereeName := `attackerKnows
      combineName := ``DY.Bytes.AttackerKnows.combine
      outTypeName := ``DY.Bytes.AttackerKnows_implies_Publishable.Part
    }

    let attStx := Lean.mkIdent `attackerKnows
    let topLevelInst ← `(command| public instance: DY.Bytes.AttackerKnows_implies_Publishable.Proof where whole := inferInstanceAs (DY.Bytes.AttackerKnows_implies_Publishable.Part $attStx))
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)

macro_rules
  | `(command| #combine_one $_options* Bytes.AttackerKnows_implies_Publishable.merge $params* from $sources,*) => do
    -- options.toplevel does not make sense in this case, hence we ignore it
    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.Bytes.Def])),
      (← `(bracketedBinder| [DY.ExecTrace.Def])),
      (← `(bracketedBinder| [DY.ProofTrace.Def])),
      (← `(bracketedBinder| [DY.Trace.Invariant.Def])),
      (← `(bracketedBinder| [DY.Bytes.Invariants.Def])),
    ]
    let params := baseGlobalInstances ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources <| .makeSimple {
      refereeName := `attackerKnows
      combineName := ``DY.Bytes.AttackerKnows.merge
      outTypeName := ``DY.Bytes.AttackerKnows_implies_Publishable.Part
    }

    return Lean.mkNullNode (combined)

end Meta.CombineMacro

end DY
