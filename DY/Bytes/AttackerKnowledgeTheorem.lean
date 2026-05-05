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
import all DY.Bytes.AttackerKnowledge
public import DY.Trace
public meta import DY.Meta.CombineMacro

namespace DY

variable [BytesFunctor]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants]

public
class SubAttackerKnowledgeTheorem {SubF: Type → Type} (att: SubAttackerKnowledge SubF) where
  pf: ∀ b: Bytes, ∀ tr: ProofTrace, tr.Invariant → att.pred (·.Publishable tr) b → b.Publishable tr

public
class AttackerKnowledgeTheorem [AttackerKnowledge] where
  inst: SubAttackerKnowledgeTheorem (AttackerKnowledge.attackerKnowledge)

section AttackerKnowledgeTheorem

public
instance
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  [pfs: ∀ id, SubAttackerKnowledgeTheorem (atts id)]
  : SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' atts)
where
  pf := by
    intro b tr h_tr
    apply SubAttackerKnowledge.combine'.implies
    intro id b
    exact (pfs id).pf b tr h_tr

public
instance
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: ∀ id, SubAttackerKnowledge (SubFs id))
  [pfs: ∀ id, SubAttackerKnowledgeTheorem (atts id)]
  : SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine atts)
where
  pf := by
    intro b tr h_tr
    apply SubAttackerKnowledge.combine.implies
    intro id b
    exact (pfs id).pf b tr h_tr

end AttackerKnowledgeTheorem

public
theorem Bytes.AttackerKnows_implies_Publishable
  [BytesInvariantsProofs]
  [AttackerKnowledge] [BaseAttackerKnowledge]
  [inst: AttackerKnowledgeTheorem]
  [BaseAttackerKnowledgeTheorem]
  (b: Bytes) (tr: ProofTrace)
  : tr.Invariant →
    Bytes.AttackerKnows b tr.erase →
    b.Publishable tr
:= by
  intro h_tr
  apply Bytes.AttackerKnows.is_least_fixpoint (·.Publishable tr) b tr.erase
  · intro b
    exact inst.inst.pf b tr h_tr
  · intro b
    simp only [AttackerKnows.baseKnowledge, SubAttackerKnowledge.fromPred]
    apply Trace.BaseAttackerKnows_implies_Publishable
    assumption

grind_pattern Bytes.AttackerKnows_implies_Publishable => Bytes.AttackerKnows b tr.erase

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* SubAttackerKnowledgeTheorem $params* from $sources,*) => do
    let options := parseOptions options
    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.BytesFunctor])),
      (← `(bracketedBinder| [DY.ExecTraceTypes])),
      (← `(bracketedBinder| [DY.ProofTraceTypes])),
      (← `(bracketedBinder| [DY.TraceInvariant])),
      (← `(bracketedBinder| [DY.BytesInvariants])),
    ]
    let params := if options.toplevel then params else baseGlobalInstances ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources <| .makeSimple {
      refereeName := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine
      outTypeName := ``DY.SubAttackerKnowledgeTheorem
    }

    let attStx := Lean.mkIdent `attackerKnowledge
    let topLevelInst ← `(command| public instance: DY.AttackerKnowledgeTheorem where inst := inferInstanceAs (DY.SubAttackerKnowledgeTheorem $attStx))
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)

macro_rules
  | `(command| #combine_one $_options* SubAttackerKnowledgeTheorem' $params* from $sources,*) => do
    -- options.toplevel does not make sense in this case, hence we ignore it
    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.BytesFunctor])),
      (← `(bracketedBinder| [DY.ExecTraceTypes])),
      (← `(bracketedBinder| [DY.ProofTraceTypes])),
      (← `(bracketedBinder| [DY.TraceInvariant])),
      (← `(bracketedBinder| [DY.BytesInvariants])),
    ]
    let params := baseGlobalInstances ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources <| .makeSimple {
      refereeName := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine'
      outTypeName := ``DY.SubAttackerKnowledgeTheorem
    }

    return Lean.mkNullNode (combined)

end Meta.CombineMacro

end DY
