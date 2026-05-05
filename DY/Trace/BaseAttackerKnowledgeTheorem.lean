module

public import DY.Bytes.Basic
public import DY.Bytes.Invariants
public import DY.Trace.Basic
public import DY.Trace.Invariant
public import DY.Trace.BaseAttackerKnowledge
import all DY.Trace.Invariant
import all DY.Trace.BaseAttackerKnowledge
public meta import DY.Meta.CombineMacro

namespace DY

public
class SubBaseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesFunctor] [BytesInvariants]
  {ExecEntryT: Type}
  (ProofEntryT: Type)
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [SubTraceInvariant ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (att: SubBaseAttackerKnowledge ExecEntryT)
where
  pf: ∀ trBefore (entry: ProofEntryT) (b: Bytes),
    SubTraceInvariant.invariant trBefore entry →
    att.attackerKnows trBefore.erase (ErasableProofEntry.erase entry) b →
    b.Publishable trBefore -- could also be `b.Publishable (trBefore.append entry)` if needed

public
class BaseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesFunctor] [BytesInvariants]
  [BaseAttackerKnowledge]
where
  pf: SubBaseAttackerKnowledgeTheorem ProofTrace.Entry BaseAttackerKnowledge.attackerKnows

public
instance instSubBaseAttackerKnowledgeTheoremCombine
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesFunctor] [BytesInvariants]
  {n: Nat}
  {ExecTypes: Fin n → Type} {ProofTypes: Fin n → Type}
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  [∀ id, SubTraceInvariant (ProofTypes id)]
  [ExecTraceTypes.Has (ExecTraceTypes.combine ExecTypes)]
  [ProofTraceTypes.Has (ProofTraceTypes.combine ProofTypes)]
  [TraceInvariant.Has (ProofTraceTypes.combine ProofTypes)]
  (atts: (id: Fin n) → SubBaseAttackerKnowledge (ExecTypes id))
  [attThms: (id: Fin n) → SubBaseAttackerKnowledgeTheorem (ProofTypes id) (atts id)]
  : SubBaseAttackerKnowledgeTheorem (ProofTraceTypes.combine ProofTypes) (SubBaseAttackerKnowledge.combine atts)
where
  pf := fun trBefore { id, entry } b =>
    (attThms id).pf trBefore entry b

public
theorem Trace.BaseAttackerKnows_implies_Publishable
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesFunctor] [BytesInvariants] [BytesInvariantsProofs]
  [BaseAttackerKnowledge] [BaseAttackerKnowledgeTheorem]
  (tr: ProofTrace) (b: Bytes)
  : Trace.Invariant tr →
    Trace.BaseAttackerKnows tr.erase b →
    b.Publishable tr
:= by
  induction tr
  · simp [Trace.BaseAttackerKnows, Trace.erase]
  rename_i trBefore entry ih
  have h_le: trBefore ≤ trBefore.snoc entry := by apply Trace.le.extend; apply Trace.le.equal
  simp only [Trace.Invariant, Trace.BaseAttackerKnows, Trace.erase]
  intro h_inv h_att
  cases h_att
  · have := BaseAttackerKnowledgeTheorem.pf.pf trBefore entry b (by grind [ProofTrace.Entry.Invariant]) (by grind [ProofTrace.Entry.erase])
    grind
  · grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* SubBaseAttackerKnowledgeTheorem__expertMode $params* from $sources,*) => do
    let options := parseOptions options
    let proofInternalStx := Lean.mkIdent `ProofEntryT.internal
    let proofStx := Lean.mkIdent `ProofEntryT
    let baseAttInternalStx := Lean.mkIdent `baseAttackerKnowledge.internal
    let baseAttStx := Lean.mkIdent `baseAttackerKnowledge

    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.ExecTraceTypes])),
      (← `(bracketedBinder| [DY.ProofTraceTypes])),
      (← `(bracketedBinder| [DY.BytesFunctor])),
      (← `(bracketedBinder| [DY.TraceInvariant])),
      (← `(bracketedBinder| [DY.BytesInvariants])),
    ]

    let params := if options.toplevel then params else baseGlobalInstances ++ params

    let sources := sources.getElems

    let combined ← combineTypeclass params sources {
      internalIdStx args id := `(term| DY.SubBaseAttackerKnowledgeTheorem ($proofInternalStx $args* $id) ($baseAttInternalStx $args* $id))
      internalStx name args := do
        let internalProofStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `ProofEntryT)
        let internalBaseAttStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `baseAttackerKnowledge)
        `(term| DY.SubBaseAttackerKnowledgeTheorem ($internalProofStx $args*) ($internalBaseAttStx $args*))
      combineStx args := `(term| DY.SubBaseAttackerKnowledgeTheorem (DY.ProofTraceTypes.combine ($proofInternalStx $args*)) (DY.SubBaseAttackerKnowledge.combine ($baseAttInternalStx $args*)))
      finalStx args := `(term| DY.SubBaseAttackerKnowledgeTheorem ($proofStx $args*) ($baseAttStx $args*))
      useInferInstanceAs := false
    }

    let topLevelInst ← `(command| public instance: DY.BaseAttackerKnowledgeTheorem where pf := inferInstanceAs (DY.SubBaseAttackerKnowledgeTheorem $proofStx $baseAttStx))
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)

macro_rules
  | `(command| #combine_one $options* SubBaseAttackerKnowledgeTheorem__noExecHas $params* from $sources,*) => do
    let proofStx := Lean.mkIdent `ProofEntryT

    let argsTarget := params.flatMap explicitNameOfBracketedBinder
    let hasInstances := #[
      (← `(bracketedBinder| [DY.ProofTraceTypes.Has ($proofStx $argsTarget*)])),
      (← `(bracketedBinder| [DY.TraceInvariant.Has ($proofStx $argsTarget*)]))
    ]
    `(command| #combine_one $options* SubBaseAttackerKnowledgeTheorem__expertMode $params* $hasInstances* from $sources,*)

macro_rules
  | `(command| #combine_one $options* SubBaseAttackerKnowledgeTheorem $params* from $sources,*) => do
    let opts := parseOptions options
    let execStx := Lean.mkIdent `ExecEntryT
    let proofStx := Lean.mkIdent `ProofEntryT

    let argsTarget := params.flatMap explicitNameOfBracketedBinder
    let hasInstances := #[
      (← `(bracketedBinder| [DY.ExecTraceTypes.Has ($execStx $argsTarget*)])),
      (← `(bracketedBinder| [DY.ProofTraceTypes.Has ($proofStx $argsTarget*)])),
      (← `(bracketedBinder| [DY.TraceInvariant.Has ($proofStx $argsTarget*)]))
    ]

    let params := if opts.toplevel then params else params ++ hasInstances

    `(command| #combine_one $options* SubBaseAttackerKnowledgeTheorem__expertMode $params* from $sources,*)

end Meta.CombineMacro

end DY
