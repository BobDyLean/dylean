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
class Trace.BaseAttackerKnows_implies_Publishable.Part
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Def] [Bytes.Invariants.Def]
  {ExecEntryT: Type}
  (ProofEntryT: Type)
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [Trace.Invariant.Part ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  [Trace.Invariant.Has ProofEntryT]
  (att: Trace.BaseAttackerKnows.Part ExecEntryT)
where
  pf: ∀ trBefore (entry: ProofEntryT) (b: Bytes),
    Trace.Invariant.Part.invariant trBefore entry →
    att.attackerKnows trBefore.erase (ProofTrace.Part.erase entry) b →
    b.Publishable trBefore -- could also be `b.Publishable (trBefore.append entry)` if needed

public
class Trace.BaseAttackerKnows_implies_Publishable.Proof
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Def] [Bytes.Invariants.Def]
  [Trace.BaseAttackerKnows.Def]
where
  whole: Trace.BaseAttackerKnows_implies_Publishable.Part ProofTrace.Entry Trace.BaseAttackerKnows.Def.whole

public
instance instTraceBaseAttackerKnowsImpliesPublishablePartCombine
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Def] [Bytes.Invariants.Def]
  {n: Nat}
  {ExecTypes: Fin n → Type} {ProofTypes: Fin n → Type}
  [∀ id, ProofTrace.Part (ExecTypes id) (ProofTypes id)]
  [∀ id, Trace.Invariant.Part (ProofTypes id)]
  [ExecTrace.Has (ExecTrace.combine ExecTypes)]
  [ProofTrace.Has (ProofTrace.combine ProofTypes)]
  [Trace.Invariant.Has (ProofTrace.combine ProofTypes)]
  (atts: (id: Fin n) → Trace.BaseAttackerKnows.Part (ExecTypes id))
  [attThms: (id: Fin n) → Trace.BaseAttackerKnows_implies_Publishable.Part (ProofTypes id) (atts id)]
  : Trace.BaseAttackerKnows_implies_Publishable.Part (ProofTrace.combine ProofTypes) (Trace.BaseAttackerKnows.combine atts)
where
  pf := fun trBefore { id, entry } b =>
    (attThms id).pf trBefore entry b

public
theorem Trace.BaseAttackerKnows_implies_Publishable
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Def] [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Trace.BaseAttackerKnows.Def] [Trace.BaseAttackerKnows_implies_Publishable.Proof]
  (tr: ProofTrace) (b: Bytes)
  : Trace.Invariant tr →
    Trace.BaseAttackerKnows tr.erase b →
    b.Publishable tr
:= by
  dsimp only [Trace.Invariant, Trace.BaseAttackerKnows]
  intro h_inv ⟨ i, h_i, h_att ⟩
  suffices b.Publishable (tr.prefix i) by grind
  refine Trace.BaseAttackerKnows_implies_Publishable.Proof.whole.pf (tr.prefix i) (tr.at i (by grind)) b ?_ ?_
  · grind [ProofTrace.Entry.Invariant]
  · simp_all only [Trace.erase_at, Trace.prefix_erase]
    grind [ProofTrace.Entry.erase]

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* Trace.BaseAttackerKnows_implies_Publishable__expertMode $params* from $sources,*) => do
    let options := parseOptions options
    let proofInternalStx := Lean.mkIdent `TracePart.Proof.internal
    let proofStx := Lean.mkIdent `TracePart.Proof
    let baseAttInternalStx := Lean.mkIdent `TracePart.baseAttackerKnows.internal
    let baseAttStx := Lean.mkIdent `TracePart.baseAttackerKnows

    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.ExecTrace.Def])),
      (← `(bracketedBinder| [DY.ProofTrace.Def])),
      (← `(bracketedBinder| [DY.Bytes.Def])),
      (← `(bracketedBinder| [DY.Trace.Invariant.Def])),
      (← `(bracketedBinder| [DY.Bytes.Invariants.Def])),
    ]

    let params := if options.toplevel then params else baseGlobalInstances ++ params

    let sources := sources.getElems

    let combined ← combineTypeclass params sources {
      internalIdStx args id := `(term| DY.Trace.BaseAttackerKnows_implies_Publishable.Part ($proofInternalStx $args* $id) ($baseAttInternalStx $args* $id))
      internalStx name args := do
        let internalProofStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `TracePart.Proof)
        let internalBaseAttStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `TracePart.baseAttackerKnows)
        `(term| DY.Trace.BaseAttackerKnows_implies_Publishable.Part ($internalProofStx $args*) ($internalBaseAttStx $args*))
      combineStx args := `(term| DY.Trace.BaseAttackerKnows_implies_Publishable.Part (DY.ProofTrace.combine ($proofInternalStx $args*)) (DY.Trace.BaseAttackerKnows.combine ($baseAttInternalStx $args*)))
      finalStx args := `(term| DY.Trace.BaseAttackerKnows_implies_Publishable.Part ($proofStx $args*) ($baseAttStx $args*))
      useInferInstanceAs := false
    }

    let topLevelInst ← `(command| public instance: DY.Trace.BaseAttackerKnows_implies_Publishable.Proof where whole := inferInstanceAs (DY.Trace.BaseAttackerKnows_implies_Publishable.Part $proofStx $baseAttStx))
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)

macro_rules
  | `(command| #combine_one $options* Trace.BaseAttackerKnows_implies_Publishable__noExecHas $params* from $sources,*) => do
    let proofStx := Lean.mkIdent `TracePart.Proof

    let argsTarget := params.flatMap explicitNameOfBracketedBinder
    let hasInstances := #[
      (← `(bracketedBinder| [DY.ProofTrace.Has ($proofStx $argsTarget*)])),
      (← `(bracketedBinder| [DY.Trace.Invariant.Has ($proofStx $argsTarget*)]))
    ]
    `(command| #combine_one $options* Trace.BaseAttackerKnows_implies_Publishable__expertMode $params* $hasInstances* from $sources,*)

macro_rules
  | `(command| #combine_one $options* Trace.BaseAttackerKnows_implies_Publishable $params* from $sources,*) => do
    let opts := parseOptions options
    let execStx := Lean.mkIdent `TracePart.Exec
    let proofStx := Lean.mkIdent `TracePart.Proof

    let argsTarget := params.flatMap explicitNameOfBracketedBinder
    let hasInstances := #[
      (← `(bracketedBinder| [DY.ExecTrace.Has ($execStx $argsTarget*)])),
      (← `(bracketedBinder| [DY.ProofTrace.Has ($proofStx $argsTarget*)])),
      (← `(bracketedBinder| [DY.Trace.Invariant.Has ($proofStx $argsTarget*)]))
    ]

    let params := if opts.toplevel then params else params ++ hasInstances

    `(command| #combine_one $options* Trace.BaseAttackerKnows_implies_Publishable__expertMode $params* from $sources,*)

end Meta.CombineMacro

end DY
