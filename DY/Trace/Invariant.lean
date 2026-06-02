module

public import DY.Trace.Basic
import all DY.Trace.Basic
public meta import DY.Trace.Grind
public meta import DY.Meta.CombineMacro

namespace DY

public
class ErasableProofEntry (ExecEntryT: outParam Type) (ProofEntryT: Type) where
  erase: ProofEntryT → ExecEntryT

public
abbrev ErasableProofEntry.default (ExecEntryT: Type): ErasableProofEntry ExecEntryT ExecEntryT where
  erase x := x

public
class ExecEntryAssociatedWithProofEntry (ExecEntryT: Type) (ProofEntryT: outParam Type) where

public
class ProofTraceTypes [ExecTraceTypes] where
  ProofT: Type
  [tc: ErasableProofEntry ExecTraceTypes.ExecT ProofT]

@[expose]
public
def ProofTrace.Entry [ExecTraceTypes] [ProofTraceTypes] := ProofTraceTypes.ProofT

public
instance [ExecTraceTypes] [ProofTraceTypes]: ErasableProofEntry ExecTrace.Entry ProofTrace.Entry where
  erase entry := ProofTraceTypes.tc.erase entry

public
abbrev ProofTrace [ExecTraceTypes] [ProofTraceTypes] := Trace ProofTrace.Entry

@[expose]
public
def ProofTrace.Entry.erase
  [ExecTraceTypes] [ProofTraceTypes]
  (entry: ProofTrace.Entry)
  : ExecTrace.Entry
:=
  ErasableProofEntry.erase entry

public
def Trace.erase
  [ExecTraceTypes] [ProofTraceTypes]
  (tr: ProofTrace)
  : ExecTrace
:=
  match tr with
  | .nil => .nil
  | .snoc trBefore entry => .snoc trBefore.erase entry.erase

public
theorem Trace.erase_le
  [ExecTraceTypes] [ProofTraceTypes]
  (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    tr1.erase ≤ tr2.erase
:= by
  intro h_le
  induction h_le
  · apply Trace.le.equal
  · apply Trace.le.extend
    assumption

grind_pattern Trace.erase_le => tr1 ≤ tr2, tr1.erase
grind_pattern [grind_later] Trace.erase_le => tr1 ≤ tr2, tr1.erase

@[simp]
public
theorem Trace.erase_length
  [ExecTraceTypes] [ProofTraceTypes]
  (tr: ProofTrace)
  : tr.erase.length = tr.length
:= by
  induction tr <;>
  simp_all [Trace.length, Trace.erase]

grind_pattern Trace.erase_length => tr.erase.length

public
def Trace.erase_at
  [ExecTraceTypes] [ProofTraceTypes]
  (tr: ProofTrace)
  (i: Nat) (h_i: i < tr.erase.length)
  : tr.erase.at i h_i = (tr.at i (Trace.erase_length tr ▸ h_i)).erase
:= by
  induction tr <;>
  simp only [Trace.at, Trace.erase]
  · grind
  split <;>
  grind [Trace.erase_length]

@[simp]
public
def Trace.prefix_erase
  [ExecTraceTypes] [ProofTraceTypes]
  (tr: ProofTrace)
  (i: Nat)
  : (tr.prefix i).erase = tr.erase.prefix i
:= by
  induction tr
  · unfold Trace.prefix Trace.erase
    simp
  rename_i trBefore entry ih
  unfold Trace.prefix Trace.erase
  simp_all [Trace.length]
  split
  · split
    · simp_all
    · simp_all [Trace.erase]
  · split
    · simp_all
    · simp_all [Trace.erase]

-- TODO test coercion
example [ExecTraceTypes] [ProofTraceTypes]: Coe ProofTrace ExecTrace where
  coe tr := tr.erase

public
class ProofTraceTypes.Has
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT: outParam Type} (ProofEntryT: Type)
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
extends TraceEntryHas ProofEntryT ProofTrace.Entry
where
  proj_none_eq_erase: ∀ x: ProofTrace.Entry, ((TraceEntryHas.proj x: Option ProofEntryT) = none) = ((TraceEntryHas.proj x.erase: Option ExecEntryT) = none)
  erase_commutes: ∀ entry: ProofEntryT, (TraceEntryHas.inj entry: ProofTrace.Entry).erase = TraceEntryHas.inj (ErasableProofEntry.erase entry)

public
class ProofTraceTypes.HasStep
  {ExecEntryT1 ExecEntryT2: outParam Type}
  (ProofEntryT1: Type) (ProofEntryT2: semiOutParam Type)
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
where
  proofInj: ProofEntryT1 → ProofEntryT2
  proofProj: ProofEntryT2 → Option ProofEntryT1
  proof_inj_proj_eq: ∀ x y, (proofProj x = some y) = (x = proofInj y)
  proofProj_none_eq_erase: ∀ x, ((proofProj x: Option ProofEntryT1) = none) = ((ExecTraceTypes.HasStep.proj (ErasableProofEntry.erase x): Option ExecEntryT1) = none)
  erase_commutes: ∀ entry, ErasableProofEntry.erase (proofInj entry) = ExecTraceTypes.HasStep.inj (ErasableProofEntry.erase entry)

public
instance instProofTraceTypesHasItself
  [ExecTraceTypes] [ProofTraceTypes]
  : ProofTraceTypes.Has ProofTrace.Entry
where
  inj entry := entry
  proj entry := some entry
  inj_proj_eq := by grind
  proj_none_eq_erase := by simp [TraceEntryHas.proj]
  erase_commutes := by simp [TraceEntryHas.inj, ProofTrace.Entry.erase]

public
instance instProofTraceTypesHasStep
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT1 ExecEntryT2: Type}
  (ProofEntryT1 ProofEntryT2: Type)
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
  [ProofTraceTypes.HasStep ProofEntryT1 ProofEntryT2]
  [ExecTraceTypes.Has ExecEntryT2]
  [ProofTraceTypes.Has ProofEntryT2]
  : ProofTraceTypes.Has ProofEntryT1
where
  inj entry := TraceEntryHas.inj (ProofTraceTypes.HasStep.proofInj (ProofEntryT2 := ProofEntryT2) entry)
  proj entry :=
    match TraceEntryHas.proj (EntryT := ProofEntryT2) entry with
    | none => none
    | some y => ProofTraceTypes.HasStep.proofProj y

  inj_proj_eq x y := by
    have := TraceEntryHas.inj_proj_eq (EntryT := ProofEntryT2) x
    have := ProofTraceTypes.HasStep.proof_inj_proj_eq (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    grind
  proj_none_eq_erase := by
    intro x
    have := TraceEntryHas.inj_proj_eq (EntryT := ExecEntryT2) (α := ExecTrace.Entry)
    have := TraceEntryHas.inj_proj_eq (EntryT := ProofEntryT2) (α := ProofTrace.Entry)
    have := ProofTraceTypes.Has.proj_none_eq_erase (ProofEntryT := ProofEntryT2)
    have := ProofTraceTypes.HasStep.proofProj_none_eq_erase (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    have := ProofTraceTypes.Has.erase_commutes (ProofEntryT := ProofEntryT2)
    simp [TraceEntryHas.proj]
    grind
  erase_commutes := by
    have := ProofTraceTypes.Has.erase_commutes (ProofEntryT := ProofEntryT2)
    have := ProofTraceTypes.HasStep.erase_commutes (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    simp [TraceEntryHas.inj]
    grind

public
structure ProofTraceTypes.combine {n: Nat} (ProofTypes: Fin n → Type): Type where
  id: Fin n
  entry: ProofTypes id

public
instance instErasableProofEntryCombine
  {n: Nat}
  (ExecTypes: Fin n → Type)
  (ProofTypes: Fin n → Type)
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  : ErasableProofEntry (ExecTraceTypes.combine ExecTypes) (ProofTraceTypes.combine ProofTypes)
where
  erase := fun { id, entry } => { id, entry := ErasableProofEntry.erase entry }

public
instance instProofTraceTypesCombineHasStep
  {n: Nat}
  (ExecTypes: Fin n → Type)
  (ProofTypes: Fin n → Type)
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  (id: Fin n):
  ProofTraceTypes.HasStep (ProofTypes id) (ProofTraceTypes.combine ProofTypes)
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
    simp [ExecTraceTypes.HasStep.proj, ErasableProofEntry.erase]
  erase_commutes _ := rfl

public
theorem ProofTrace.Entry.erase_eq_imp_exists
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  {entry: ProofTrace.Entry}
  {result: ExecEntryT}
  : entry.erase = TraceEntryHas.inj result ↔ (
      ∃ result': ProofEntryT,
      entry = TraceEntryHas.inj result' ∧
      ErasableProofEntry.erase result' = result
    )
:= by
  cases h: (TraceEntryHas.proj entry: Option ProofEntryT)
  · have := ProofTraceTypes.Has.proj_none_eq_erase (ProofEntryT := ProofEntryT) entry
    rewrite [← TraceEntryHas.inj_proj_eq]
    simp_all only [reduceCtorEq, false_iff, not_exists]
    intro x
    have := TraceEntryHas.inj_proj_eq entry x
    grind
  · rename_i result'
    rewrite [TraceEntryHas.inj_proj_eq] at h
    grind [ProofTraceTypes.Has.erase_commutes]

public
theorem ProofTrace.Entry.at?_eq_none_erase
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  (tr: ProofTrace) (i: Nat)
  : (tr.at? i = (none: Option ProofEntryT)) =
    (tr.erase.at? i = (none: Option ExecEntryT))
:= by
  simp only [Trace.at?, dite_eq_right_iff, Trace.erase_length, eq_iff_iff]
  constructor
  all_goals
    intro _ h_i
    have := ProofTraceTypes.Has.proj_none_eq_erase (ProofEntryT := ProofEntryT) (tr.at i h_i)
    have := Trace.erase_at tr i (by grind)
    grind

public
theorem ProofTrace.Entry.at?_eq_some_erase
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  (tr: ProofTrace) (i: Nat) (entry: ProofEntryT)
  : (tr.at? i = some entry) →
    (tr.erase.at? i = some (ErasableProofEntry.erase entry))
:= by
  simp only [Trace.at?, Option.dite_none_right_eq_some, Trace.erase_length, forall_exists_index]
  intro h_i h
  have := ProofTraceTypes.Has.erase_commutes entry
  have := TraceEntryHas.inj_proj_eq (tr.at i (by grind)) entry
  have := TraceEntryHas.inj_proj_eq (tr.erase.at i (by grind)) (ErasableProofEntry.erase entry)
  have := Trace.erase_at tr i (by grind)
  grind

public
theorem Trace.append_erase
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).erase = tr.erase.append (ErasableProofEntry.erase entry)
:= by
  simp [Trace.append, Trace.erase, ProofTraceTypes.Has.erase_commutes]

-- Invariant

public
class SubTraceInvariant [ExecTraceTypes] [ProofTraceTypes] {ExecEntryT: outParam Type} (ProofEntryT: Type) [ErasableProofEntry ExecEntryT ProofEntryT] where
  invariant: ProofTrace → ProofEntryT → Prop

public
class TraceInvariant [ExecTraceTypes] [ProofTraceTypes] where
  tc_inv: SubTraceInvariant ProofTrace.Entry

public
instance [ExecTraceTypes] [ProofTraceTypes] [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]: SubTraceInvariant ProofTrace.Entry where
  invariant := TraceInvariant.tc_inv.invariant

public
def ProofTrace.Entry.Invariant
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  (trBefore: ProofTrace)
  (entry: ProofTrace.Entry)
  : Prop
:=
  SubTraceInvariant.invariant trBefore entry

public
def Trace.Invariant
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  (tr: ProofTrace)
  : Prop
:=
  match tr with
  | .nil => True
  | .snoc trBefore entry =>
    trBefore.Invariant ∧
    entry.Invariant trBefore

public
class TraceInvariant.Has
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT: outParam Type}
  (ProofEntryT: Type)
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [SubTraceInvariant ProofEntryT]
where
  inv_commutes: ∀ trBefore: ProofTrace, ∀ entry: ProofEntryT, (TraceEntryHas.inj entry: ProofTrace.Entry).Invariant trBefore = SubTraceInvariant.invariant trBefore entry

public
class TraceInvariant.HasStep
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT1 ExecEntryT2: outParam Type}
  (ProofEntryT1 ProofEntryT2: Type)
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
  [ProofTraceTypes.HasStep ProofEntryT1 ProofEntryT2]
  [SubTraceInvariant ProofEntryT1]
  [SubTraceInvariant ProofEntryT2]
where
  inv_commutes: ∀ trBefore: ProofTrace, ∀ entry: ProofEntryT1, SubTraceInvariant.invariant trBefore (ProofTraceTypes.HasStep.proofInj entry: ProofEntryT2) = SubTraceInvariant.invariant trBefore entry

public
instance instTraceInvariantHasItself
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  : TraceInvariant.Has ProofTrace.Entry
where
  inv_commutes := by simp [TraceEntryHas.inj, ProofTrace.Entry.Invariant]

public
instance instTraceInvariantHasStep
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT1 ProofEntryT1: Type}
  {ExecEntryT2 ProofEntryT2: Type}
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
  [ProofTraceTypes.HasStep ProofEntryT1 ProofEntryT2]
  [ExecTraceTypes.Has ExecEntryT2]
  [ProofTraceTypes.Has ProofEntryT2]
  [SubTraceInvariant ProofEntryT1]
  [SubTraceInvariant ProofEntryT2]
  [TraceInvariant.HasStep ProofEntryT1 ProofEntryT2]
  [TraceInvariant.Has ProofEntryT2]
  : TraceInvariant.Has ProofEntryT1
where
  inv_commutes := by
    have := TraceInvariant.HasStep.inv_commutes (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    have := TraceInvariant.Has.inv_commutes (ProofEntryT := ProofEntryT2)
    simp_all [TraceEntryHas.inj]

public
instance SubTraceInvariant.combine
  [ExecTraceTypes] [ProofTraceTypes]
  {n: Nat}
  {ExecTypes: Fin n → Type}
  {ProofTypes: Fin n → Type}
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  [∀ id, SubTraceInvariant (ProofTypes id)]
  : SubTraceInvariant (ProofTraceTypes.combine ProofTypes)
where
  invariant := fun trBefore { id := _, entry } =>
    SubTraceInvariant.invariant trBefore entry

public
instance instTraceInvariantCombineHasStep
  [ExecTraceTypes] [ProofTraceTypes]
  {n: Nat}
  {ExecTypes: Fin n → Type}
  (ProofTypes: Fin n → Type)
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  [∀ id, SubTraceInvariant (ProofTypes id)]
  (id: Fin n)
  : TraceInvariant.HasStep (ProofTypes id) (ProofTraceTypes.combine ProofTypes)
where
  inv_commutes trBefore entry := by rfl

public
theorem Trace.invariant_append
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [SubTraceInvariant ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).Invariant = (tr.Invariant ∧ SubTraceInvariant.invariant tr entry)
:= by
  have := TraceInvariant.Has.inv_commutes (ProofEntryT := ProofEntryT)
  simp_all [Trace.Invariant, Trace.append]

public
theorem Trace.invariant_at
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  (tr: ProofTrace)
  (i: Nat)
  (h_i: i < tr.length)
  : tr.Invariant →
    (tr.at i h_i).Invariant (tr.prefix i)
:= by
  fun_induction Trace.at <;>
  grind [Trace.Invariant, Trace.prefix, Trace.length]

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* ProofEntryT $params* from $sources,*) => do
    let options := parseOptions options
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `ProofEntryT
      combineName := ``DY.ProofTraceTypes.combine
      internalOutTypeStx := fun _ _ => `(term| Type)
      outTypeStx := fun _ => `(term| Type)
    }

    let execInternalStx := Lean.mkIdent `ExecEntryT.internal
    let execStx := Lean.mkIdent `ExecEntryT
    let proofInternalStx := Lean.mkIdent `ProofEntryT.internal
    let proofStx := Lean.mkIdent `ProofEntryT
    let erasable ← combineTypeclass params sources {
      internalIdStx args id := `(term| ErasableProofEntry ($execInternalStx $args* $id) ($proofInternalStx $args* $id))
      internalStx name args := do
        let internalExecStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `ExecEntryT)
        let internalProofStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ `ProofEntryT)
        `(term| DY.ErasableProofEntry ($internalExecStx $args*) ($internalProofStx $args*))
      combineStx args := `(term| DY.ErasableProofEntry (DY.ExecTraceTypes.combine ($execInternalStx $args*)) (DY.ProofTraceTypes.combine ($proofInternalStx $args*)))
      finalStx args := `(term| DY.ErasableProofEntry ($execStx $args*) ($proofStx $args*))
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `ProofEntryT
      combineName := ``DY.ProofTraceTypes.combine
      hasStepName := ``DY.ProofTraceTypes.HasStep
    }

    let topLevelInst ← `(command| public instance: DY.ProofTraceTypes where ProofT := $proofStx)
    let topLevelHas ← `(command| public instance: DY.ProofTraceTypes.Has $proofStx := inferInstanceAs (DY.ProofTraceTypes.Has ProofTrace.Entry))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    let hasCombine ← mkHasCombine params {
      hasCombineStx args := `(term| DY.ProofTraceTypes.Has (DY.ProofTraceTypes.combine ($proofInternalStx $args*)))
      hasStx args := `(term| DY.ProofTraceTypes.Has ($proofStx $args*))
    }
    let hasCombine := if options.toplevel then hasCombine else #[]

    return Lean.mkNullNode (combined ++ erasable ++ hasStep ++ topLevel ++ hasCombine)

macro_rules
  | `(command| #combine_one $options* SubTraceInvariant $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources  <| .makeSimple {
      refereeName := `ProofEntryT
      combineName := ``DY.ProofTraceTypes.combine
      outTypeName := ``DY.SubTraceInvariant
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `ProofEntryT
      combineName := ``DY.ProofTraceTypes.combine
      hasStepName := ``DY.TraceInvariant.HasStep
    }

    let proofInternalStx := Lean.mkIdent `ProofEntryT.internal
    let proofStx := Lean.mkIdent `ProofEntryT
    let topLevelInst1 ← `(command| public instance: DY.SubTraceInvariant $proofStx := (inferInstanceAs (DY.SubTraceInvariant (DY.ProofTraceTypes.combine $proofInternalStx))))
    let topLevelInst2 ← `(command| public instance : DY.TraceInvariant where tc_inv := inferInstanceAs (DY.SubTraceInvariant $proofStx))
    let topLevelHas ← `(command| public instance: DY.TraceInvariant.Has $proofStx := inferInstanceAs (DY.TraceInvariant.Has DY.ProofTrace.Entry))
    let topLevel := if options.toplevel then #[topLevelInst1, topLevelInst2, topLevelHas] else #[]

    let hasCombine ← mkHasCombine params {
      hasCombineStx args := `(term| DY.TraceInvariant.Has (DY.ProofTraceTypes.combine ($proofInternalStx $args*)))
      hasStx args := `(term| DY.TraceInvariant.Has ($proofStx $args*))
    }
    let hasCombine := if options.toplevel then hasCombine else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel ++ hasCombine)

end Meta.CombineMacro

end DY
