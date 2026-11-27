module

public import DY.Trace.Basic
import all DY.Trace.Basic
public meta import DY.Trace.Grind
public meta import DY.Meta.CombineMacro

namespace DY

public
class ProofTrace.Part (ExecEntryT: outParam Type) (ProofEntryT: Type) where
  erase: ProofEntryT → ExecEntryT

public
abbrev ProofTrace.Part.default (ExecEntryT: Type): ProofTrace.Part ExecEntryT ExecEntryT where
  erase x := x

public
class ExecEntryAssociatedWithProofEntry (ExecEntryT: Type) (ProofEntryT: outParam Type) where

public
class ProofTrace.Def [ExecTrace.Def] where
  whole: Type
  [part: ProofTrace.Part ExecTrace.Def.whole whole]

@[expose]
public
def ProofTrace.Entry [ExecTrace.Def] [ProofTrace.Def] := ProofTrace.Def.whole

public
instance [ExecTrace.Def] [ProofTrace.Def]: ProofTrace.Part ExecTrace.Entry ProofTrace.Entry where
  erase entry := ProofTrace.Def.part.erase entry

public
abbrev ProofTrace [ExecTrace.Def] [ProofTrace.Def] := Trace ProofTrace.Entry

@[expose]
public
def ProofTrace.Entry.erase
  [ExecTrace.Def] [ProofTrace.Def]
  (entry: ProofTrace.Entry)
  : ExecTrace.Entry
:=
  ProofTrace.Part.erase entry

public
def Trace.erase
  [ExecTrace.Def] [ProofTrace.Def]
  (tr: ProofTrace)
  : ExecTrace
:=
  ⟨ tr.toArray.map ProofTrace.Entry.erase ⟩

public
theorem Trace.erase_le
  [ExecTrace.Def] [ProofTrace.Def]
  (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    tr1.erase ≤ tr2.erase
:= by
  cases tr1; cases tr2
  dsimp only [Trace.erase, LE.le]
  grind

grind_pattern Trace.erase_le => tr1 ≤ tr2, tr1.erase
grind_pattern [grind_later] Trace.erase_le => tr1 ≤ tr2, tr1.erase

@[simp]
public
theorem Trace.erase_length
  [ExecTrace.Def] [ProofTrace.Def]
  (tr: ProofTrace)
  : tr.erase.length = tr.length
:= by
  cases tr
  dsimp only [Trace.erase, Trace.length, LE.le]
  grind

grind_pattern Trace.erase_length => tr.erase.length

public
theorem Trace.erase_at
  [ExecTrace.Def] [ProofTrace.Def]
  (tr: ProofTrace)
  (i: Nat) (h_i: i < tr.erase.length)
  : tr.erase.at i h_i = (tr.at i (Trace.erase_length tr ▸ h_i)).erase
:= by
  revert h_i
  cases tr
  dsimp only [Trace.length, Trace.erase, Trace.length, Trace.at, LE.le]
  grind

@[simp]
public
theorem Trace.prefix_erase
  [ExecTrace.Def] [ProofTrace.Def]
  (tr: ProofTrace)
  (i: Nat)
  : (tr.prefix i).erase = tr.erase.prefix i
:= by
  cases tr
  dsimp only [Trace.prefix, Trace.erase]
  grind

-- TODO test coercion
example [ExecTrace.Def] [ProofTrace.Def]: Coe ProofTrace ExecTrace where
  coe tr := tr.erase

@[has_suffix TracePart.Proof]
public
class ProofTrace.Has
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT: outParam Type} (ProofEntryT: Type)
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
extends TraceEntryHas ProofEntryT ProofTrace.Entry
where
  proj_none_eq_erase: ∀ x: ProofTrace.Entry, ((TraceEntryHas.proj x: Option ProofEntryT) = none) = ((TraceEntryHas.proj x.erase: Option ExecEntryT) = none)
  erase_commutes: ∀ entry: ProofEntryT, (TraceEntryHas.inj entry: ProofTrace.Entry).erase = TraceEntryHas.inj (ProofTrace.Part.erase entry)

public
class ProofTrace.HasStep
  {ExecEntryT1 ExecEntryT2: outParam Type}
  (ProofEntryT1: Type) (ProofEntryT2: semiOutParam Type)
  [ProofTrace.Part ExecEntryT1 ProofEntryT1]
  [ProofTrace.Part ExecEntryT2 ProofEntryT2]
  [ExecTrace.HasStep ExecEntryT1 ExecEntryT2]
where
  proofInj: ProofEntryT1 → ProofEntryT2
  proofProj: ProofEntryT2 → Option ProofEntryT1
  proof_inj_proj_eq: ∀ x y, (proofProj x = some y) = (x = proofInj y)
  proofProj_none_eq_erase: ∀ x, ((proofProj x: Option ProofEntryT1) = none) = ((ExecTrace.HasStep.proj (ProofTrace.Part.erase x): Option ExecEntryT1) = none)
  erase_commutes: ∀ entry, ProofTrace.Part.erase (proofInj entry) = ExecTrace.HasStep.inj (ProofTrace.Part.erase entry)

public
instance instProofTraceHasItself
  [ExecTrace.Def] [ProofTrace.Def]
  : ProofTrace.Has ProofTrace.Entry
where
  inj entry := entry
  proj entry := some entry
  inj_proj_eq := by grind
  proj_none_eq_erase := by simp [TraceEntryHas.proj]
  erase_commutes := by simp [TraceEntryHas.inj, ProofTrace.Entry.erase]

public
instance instProofTraceHasStep
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT1 ExecEntryT2: Type}
  (ProofEntryT1 ProofEntryT2: Type)
  [ProofTrace.Part ExecEntryT1 ProofEntryT1]
  [ProofTrace.Part ExecEntryT2 ProofEntryT2]
  [ExecTrace.HasStep ExecEntryT1 ExecEntryT2]
  [ProofTrace.HasStep ProofEntryT1 ProofEntryT2]
  [ExecTrace.Has ExecEntryT2]
  [ProofTrace.Has ProofEntryT2]
  : ProofTrace.Has ProofEntryT1
where
  inj entry := TraceEntryHas.inj (ProofTrace.HasStep.proofInj (ProofEntryT2 := ProofEntryT2) entry)
  proj entry :=
    match TraceEntryHas.proj (EntryT := ProofEntryT2) entry with
    | none => none
    | some y => ProofTrace.HasStep.proofProj y

  inj_proj_eq x y := by
    have := TraceEntryHas.inj_proj_eq (EntryT := ProofEntryT2) x
    have := ProofTrace.HasStep.proof_inj_proj_eq (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    grind
  proj_none_eq_erase := by
    intro x
    have := TraceEntryHas.inj_proj_eq (EntryT := ExecEntryT2) (α := ExecTrace.Entry)
    have := TraceEntryHas.inj_proj_eq (EntryT := ProofEntryT2) (α := ProofTrace.Entry)
    have := ProofTrace.Has.proj_none_eq_erase (ProofEntryT := ProofEntryT2)
    have := ProofTrace.HasStep.proofProj_none_eq_erase (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    have := ProofTrace.Has.erase_commutes (ProofEntryT := ProofEntryT2)
    simp [TraceEntryHas.proj]
    grind
  erase_commutes := by
    have := ProofTrace.Has.erase_commutes (ProofEntryT := ProofEntryT2)
    have := ProofTrace.HasStep.erase_commutes (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    simp [TraceEntryHas.inj]
    grind

public
structure ProofTrace.combine {n: Nat} (ProofTypes: Fin n → Type): Type where
  id: Fin n
  entry: ProofTypes id

public
instance instProofTracePartCombine
  {n: Nat}
  (ExecTypes: Fin n → Type)
  (ProofTypes: Fin n → Type)
  [∀ id, ProofTrace.Part (ExecTypes id) (ProofTypes id)]
  : ProofTrace.Part (ExecTrace.combine ExecTypes) (ProofTrace.combine ProofTypes)
where
  erase := fun { id, entry } => { id, entry := ProofTrace.Part.erase entry }

public
instance instProofTraceCombineHasStep
  {n: Nat}
  (ExecTypes: Fin n → Type)
  (ProofTypes: Fin n → Type)
  [∀ id, ProofTrace.Part (ExecTypes id) (ProofTypes id)]
  (id: Fin n):
  ProofTrace.HasStep (ProofTypes id) (ProofTrace.combine ProofTypes)
where
  proofInj entry := { id, entry }
  proofProj entry :=
    if h: entry.id = id then
      some (h ▸ entry.entry)
    else
      none
  proof_inj_proj_eq x y := by
    cases x
    grind
  proofProj_none_eq_erase x := by
    simp [ExecTrace.HasStep.proj, ProofTrace.Part.erase]
  erase_commutes _ := rfl

public
theorem ProofTrace.Entry.erase_eq_imp_exists
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT ProofEntryT: Type}
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  {entry: ProofTrace.Entry}
  {result: ExecEntryT}
  : entry.erase = TraceEntryHas.inj result ↔ (
      ∃ result': ProofEntryT,
      entry = TraceEntryHas.inj result' ∧
      ProofTrace.Part.erase result' = result
    )
:= by
  cases h: (TraceEntryHas.proj entry: Option ProofEntryT)
  · have := ProofTrace.Has.proj_none_eq_erase (ProofEntryT := ProofEntryT) entry
    rewrite [← TraceEntryHas.inj_proj_eq]
    simp_all only [reduceCtorEq, false_iff, not_exists]
    intro x
    have := TraceEntryHas.inj_proj_eq entry x
    grind
  · rename_i result'
    rewrite [TraceEntryHas.inj_proj_eq] at h
    grind [ProofTrace.Has.erase_commutes]

public
theorem ProofTrace.Entry.at?_eq_none_erase
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT ProofEntryT: Type}
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  (tr: ProofTrace) (i: Nat)
  : (tr.at? i = (none: Option ProofEntryT)) =
    (tr.erase.at? i = (none: Option ExecEntryT))
:= by
  simp only [Trace.at?, dite_eq_right_iff, Trace.erase_length, eq_iff_iff]
  constructor
  all_goals
    intro _ h_i
    have := ProofTrace.Has.proj_none_eq_erase (ProofEntryT := ProofEntryT) (tr.at i h_i)
    have := Trace.erase_at tr i (by grind)
    grind

public
theorem ProofTrace.Entry.at?_eq_some_erase
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT ProofEntryT: Type}
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  (tr: ProofTrace) (i: Nat) (entry: ProofEntryT)
  : (tr.at? i = some entry) →
    (tr.erase.at? i = some (ProofTrace.Part.erase entry))
:= by
  simp only [Trace.at?, Option.dite_none_right_eq_some, Trace.erase_length, forall_exists_index]
  intro h_i h
  have := ProofTrace.Has.erase_commutes entry
  have := TraceEntryHas.inj_proj_eq (tr.at i (by grind)) entry
  have := TraceEntryHas.inj_proj_eq (tr.erase.at i (by grind)) (ProofTrace.Part.erase entry)
  have := Trace.erase_at tr i (by grind)
  grind

public
theorem Trace.erase_empty
  [ExecTrace.Def] [ProofTrace.Def]
  : (Trace.empty: ProofTrace).erase = (Trace.empty: ExecTrace)
:= by
  simp [Trace.erase, Trace.empty]

public
theorem Trace.erase_append
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT ProofEntryT: Type}
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).erase = tr.erase.append (ProofTrace.Part.erase entry)
:= by
  cases tr
  dsimp only [Trace.append, Trace.erase]
  simp [ProofTrace.Has.erase_commutes]

-- Invariant

public
class Trace.Invariant.Part [ExecTrace.Def] [ProofTrace.Def] {ExecEntryT: outParam Type} (ProofEntryT: Type) [ProofTrace.Part ExecEntryT ProofEntryT] where
  invariant: ProofTrace → ProofEntryT → Prop

public
class Trace.Invariant.Def [ExecTrace.Def] [ProofTrace.Def] where
  whole: Trace.Invariant.Part ProofTrace.Entry

public
instance [ExecTrace.Def] [ProofTrace.Def] [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]: Trace.Invariant.Part ProofTrace.Entry where
  invariant := Trace.Invariant.Def.whole.invariant

public
def ProofTrace.Entry.Invariant
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  (trBefore: ProofTrace)
  (entry: ProofTrace.Entry)
  : Prop
:=
  Trace.Invariant.Part.invariant trBefore entry

public
def Trace.Invariant
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  (tr: ProofTrace)
  : Prop
:=
  ∀ i h_i, (tr.at i h_i).Invariant (tr.prefix i)

@[has_suffix TracePart.Proof]
public
class Trace.Invariant.Has
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  {ExecEntryT: outParam Type}
  (ProofEntryT: Type)
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  [Trace.Invariant.Part ProofEntryT]
where
  inv_commutes: ∀ trBefore: ProofTrace, ∀ entry: ProofEntryT, (TraceEntryHas.inj entry: ProofTrace.Entry).Invariant trBefore = Trace.Invariant.Part.invariant trBefore entry

public
class Trace.Invariant.HasStep
  [ExecTrace.Def] [ProofTrace.Def]
  {ExecEntryT1 ExecEntryT2: outParam Type}
  (ProofEntryT1 ProofEntryT2: Type)
  [ProofTrace.Part ExecEntryT1 ProofEntryT1]
  [ProofTrace.Part ExecEntryT2 ProofEntryT2]
  [ExecTrace.HasStep ExecEntryT1 ExecEntryT2]
  [ProofTrace.HasStep ProofEntryT1 ProofEntryT2]
  [Trace.Invariant.Part ProofEntryT1]
  [Trace.Invariant.Part ProofEntryT2]
where
  inv_commutes: ∀ trBefore: ProofTrace, ∀ entry: ProofEntryT1, Trace.Invariant.Part.invariant trBefore (ProofTrace.HasStep.proofInj entry: ProofEntryT2) = Trace.Invariant.Part.invariant trBefore entry

public
instance instTraceInvariantHasItself
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  : Trace.Invariant.Has ProofTrace.Entry
where
  inv_commutes := by simp [TraceEntryHas.inj, ProofTrace.Entry.Invariant]

public
instance instTraceInvariantHasStep
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  {ExecEntryT1 ProofEntryT1: Type}
  {ExecEntryT2 ProofEntryT2: Type}
  [ProofTrace.Part ExecEntryT1 ProofEntryT1]
  [ProofTrace.Part ExecEntryT2 ProofEntryT2]
  [ExecTrace.HasStep ExecEntryT1 ExecEntryT2]
  [ProofTrace.HasStep ProofEntryT1 ProofEntryT2]
  [ExecTrace.Has ExecEntryT2]
  [ProofTrace.Has ProofEntryT2]
  [Trace.Invariant.Part ProofEntryT1]
  [Trace.Invariant.Part ProofEntryT2]
  [Trace.Invariant.HasStep ProofEntryT1 ProofEntryT2]
  [Trace.Invariant.Has ProofEntryT2]
  : Trace.Invariant.Has ProofEntryT1
where
  inv_commutes := by
    have := Trace.Invariant.HasStep.inv_commutes (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    have := Trace.Invariant.Has.inv_commutes (ProofEntryT := ProofEntryT2)
    simp_all [TraceEntryHas.inj]

public
instance Trace.Invariant.combine
  [ExecTrace.Def] [ProofTrace.Def]
  {n: Nat}
  {ExecTypes: Fin n → Type}
  {ProofTypes: Fin n → Type}
  [∀ id, ProofTrace.Part (ExecTypes id) (ProofTypes id)]
  [∀ id, Trace.Invariant.Part (ProofTypes id)]
  : Trace.Invariant.Part (ProofTrace.combine ProofTypes)
where
  invariant := fun trBefore { id := _, entry } =>
    Trace.Invariant.Part.invariant trBefore entry

public
instance instTraceInvariantCombineHasStep
  [ExecTrace.Def] [ProofTrace.Def]
  {n: Nat}
  {ExecTypes: Fin n → Type}
  (ProofTypes: Fin n → Type)
  [∀ id, ProofTrace.Part (ExecTypes id) (ProofTypes id)]
  [∀ id, Trace.Invariant.Part (ProofTypes id)]
  (id: Fin n)
  : Trace.Invariant.HasStep (ProofTypes id) (ProofTrace.combine ProofTypes)
where
  inv_commutes trBefore entry := by rfl

public
theorem Trace.invariant_empty
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  : (Trace.empty: ProofTrace).Invariant
:= by
  simp [Trace.Invariant, Trace.empty, Trace.length]

public
theorem Trace.invariant_append
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  {ExecEntryT ProofEntryT: Type}
  [ProofTrace.Part ExecEntryT ProofEntryT]
  [ExecTrace.Has ExecEntryT]
  [ProofTrace.Has ProofEntryT]
  [Trace.Invariant.Part ProofEntryT]
  [Trace.Invariant.Has ProofEntryT]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).Invariant = (tr.Invariant ∧ Trace.Invariant.Part.invariant tr entry)
:= by
  dsimp only [Trace.Invariant]
  rewrite [← Trace.Invariant.Has.inv_commutes (ProofEntryT := ProofEntryT) tr entry]
  have: (append tr entry).at (length tr) (by grind) = TraceEntryHas.inj entry := by grind [Trace.at?_append, Trace.at?_eq_some]
  have: ∀ i, i ≤ tr.length → (tr.append entry).prefix i = tr.prefix i := by grind [Trace.append_prefix]
  have: (tr.append entry).prefix tr.length = tr := by grind
  grind

public
theorem Trace.invariant_at
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  (tr: ProofTrace)
  (i: Nat)
  (h_i: i < tr.length)
  : tr.Invariant →
    (tr.at i h_i).Invariant (tr.prefix i)
:= by
  cases tr
  dsimp only [Trace.append, Trace.Invariant]
  grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* ProofTrace $params* from $sources,*) => do
    let options := parseOptions options
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `TracePart.Proof
      combineName := ``DY.ProofTrace.combine
      internalOutTypeStx := fun _ _ => `(term| Type)
      outTypeStx := fun _ => `(term| Type)
      isTheorem := false
    }

    let execInternalStx := Lean.mkIdent `TracePart.Exec.internal
    let execStx := Lean.mkIdent `TracePart.Exec
    let proofInternalStx := Lean.mkIdent `TracePart.Proof.internal
    let proofStx := Lean.mkIdent `TracePart.Proof
    let erasable ← combineTypeclass params sources {
      internalIdStx args id := `(term| ProofTrace.Part ($execInternalStx $args* $id) ($proofInternalStx $args* $id))
      internalStx name args := do
        let internalExecStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `TracePart.Exec)
        let internalProofStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `TracePart.Proof)
        `(term| DY.ProofTrace.Part ($internalExecStx $args*) ($internalProofStx $args*))
      combineStx args := `(term| DY.ProofTrace.Part (DY.ExecTrace.combine ($execInternalStx $args*)) (DY.ProofTrace.combine ($proofInternalStx $args*)))
      finalStx args := `(term| DY.ProofTrace.Part ($execStx $args*) ($proofStx $args*))
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `TracePart.Proof
      combineName := ``DY.ProofTrace.combine
      hasStepName := ``DY.ProofTrace.HasStep
    }

    let topLevelInst ← `(command| public instance: DY.ProofTrace.Def where whole := $proofStx)
    let topLevelHas ← `(command| public instance: DY.ProofTrace.Has $proofStx := inferInstanceAs (DY.ProofTrace.Has ProofTrace.Entry))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    let hasCombine ← mkHasCombine params {
      hasCombineStx args := `(term| DY.ProofTrace.Has (DY.ProofTrace.combine ($proofInternalStx $args*)))
      hasStx args := `(term| DY.ProofTrace.Has ($proofStx $args*))
    }
    let hasCombine := if options.toplevel then hasCombine else #[]

    return Lean.mkNullNode (combined ++ erasable ++ hasStep ++ topLevel ++ hasCombine)

macro_rules
  | `(command| #combine_one $options* Trace.Invariant $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.ExecTrace.Def])), (← `(bracketedBinder| [DY.ProofTrace.Def]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources  <| .makeSimple {
      refereeName := `TracePart.Proof
      combineName := ``DY.ProofTrace.combine
      outTypeName := ``DY.Trace.Invariant.Part
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `TracePart.Proof
      combineName := ``DY.ProofTrace.combine
      hasStepName := ``DY.Trace.Invariant.HasStep
    }

    let proofInternalStx := Lean.mkIdent `TracePart.Proof.internal
    let proofStx := Lean.mkIdent `TracePart.Proof
    let topLevelInst1 ← `(command| public instance: DY.Trace.Invariant.Part $proofStx := (inferInstanceAs (DY.Trace.Invariant.Part (DY.ProofTrace.combine $proofInternalStx))))
    let topLevelInst2 ← `(command| public instance : DY.Trace.Invariant.Def where whole := inferInstanceAs (DY.Trace.Invariant.Part $proofStx))
    let topLevelHas ← `(command| public instance: DY.Trace.Invariant.Has $proofStx := inferInstanceAs (DY.Trace.Invariant.Has DY.ProofTrace.Entry))
    let topLevel := if options.toplevel then #[topLevelInst1, topLevelInst2, topLevelHas] else #[]

    let hasCombine ← mkHasCombine params {
      hasCombineStx args := `(term| DY.Trace.Invariant.Has (DY.ProofTrace.combine ($proofInternalStx $args*)))
      hasStx args := `(term| DY.Trace.Invariant.Has ($proofStx $args*))
    }
    let hasCombine := if options.toplevel then hasCombine else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel ++ hasCombine)

end Meta.CombineMacro

end DY
