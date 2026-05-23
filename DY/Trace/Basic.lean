module

meta import DY.Trace.Grind
public meta import DY.Meta.CombineMacro

namespace DY

-- Generic trace definition

public
inductive Trace (α: Type) where
  | nil: Trace α
  | snoc: Trace α -> α -> Trace α

public
inductive Trace.le {α: Type} : Trace α -> Trace α -> Prop where
  | equal: (tr: Trace α) -> Trace.le tr tr
  | extend: (tr1: Trace α) -> (tr2: Trace α) -> (e: α) -> Trace.le tr1 tr2 -> Trace.le tr1 (.snoc tr2 e)

public
instance {α: Type}: LE (Trace α) where
  le := Trace.le

@[refl]
public
theorem Trace.le_refl
  {α: Type}
  (tr: Trace α)
  : tr ≤ tr
:=
  Trace.le.equal tr

grind_pattern Trace.le_refl => tr ≤ tr

public
theorem Trace.le_trans
  {α: Type}
  (tr1 tr2 tr3: Trace α)
  : tr1 ≤ tr2 → tr2 ≤ tr3 → tr1 ≤ tr3
:= by
  intros hxy hyz
  induction hyz with
  | equal => exact hxy
  | extend tr3 e _ ih =>
    exact (Trace.le.extend tr1 tr3 e ih)

public
class TraceEntryHas (EntryT: Type) (α: Type) where
  inj: EntryT → α
  proj: α → Option EntryT
  inj_proj_eq: ∀ x y, (proj x = some y) = (x = inj y)

public
def Trace.append
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr: Trace α) (entry: EntryT)
  : Trace α
:=
  .snoc tr (TraceEntryHas.inj entry)

public
def Trace.append_le
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr: Trace α) (entry: EntryT)
  : tr ≤ tr.append entry
:= by
  apply Trace.le.extend
  apply Trace.le.equal

public
def Trace.length {α: Type} (tr: Trace α) : Nat :=
  match tr with
  | .nil => 0
  | .snoc trBefore _ => trBefore.length + 1

public
theorem Trace.length_le
  {α: Type} (tr1 tr2: Trace α)
  : tr1 ≤ tr2 →
    tr1.length ≤ tr2.length
:= by
  intro h
  induction h <;>
  grind [Trace.length]

grind_pattern Trace.length_le => tr1 ≤ tr2, tr1.length

public
def Trace.prefix {α: Type} (tr: Trace α) (i: Nat): Trace α :=
  if i = tr.length then
    tr
  else
    match tr with
    | .nil => .nil
    | .snoc trBefore _ => trBefore.prefix i

public
theorem Trace.prefix_le
  {α: Type}
  (tr: Trace α) (i: Nat)
  : tr.prefix i ≤ tr
:= by
  fun_induction Trace.prefix
  · apply Trace.le_refl
  · apply Trace.le_refl
  · apply Trace.le.extend
    assumption

grind_pattern Trace.prefix_le => tr.prefix i

@[simp, grind =]
public
theorem Trace.prefix_eq
  {α: Type}
  (tr: Trace α)
  : tr.prefix tr.length = tr
:= by
  unfold Trace.prefix
  simp

public
def Trace.at {α: Type} (tr: Trace α) (i: Nat) (h_i: i < tr.length): α :=
  match tr with
  | .nil => False.elim (by simp_all [Trace.length])
  | .snoc trBefore entry =>
    if h: i = trBefore.length then
      entry
    else
      trBefore.at i (by grind [Trace.length])

public
theorem Trace.at_le
  {α: Type} (tr1 tr2: Trace α) (i: Nat) (h_i: i < tr1.length)
  (h_le: tr1 ≤ tr2)
  : tr1.at i h_i = tr2.at i (by grind)
:= by
  induction h_le <;>
  grind [Trace.at]

grind_pattern Trace.at_le => tr1 ≤ tr2, tr1.at i h_i
grind_pattern [grind_later] Trace.at_le => tr1 ≤ tr2, tr1.at i h_i

@[expose]
public
def Trace.at?
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr: Trace α) (i: Nat)
  : Option EntryT
:=
  if h_i: i < tr.length then
    TraceEntryHas.proj (tr.at i h_i)
  else
    none

public
theorem Trace.at?_le
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr1 tr2: Trace α) (i: Nat)
  : tr1 ≤ tr2 →
    match (tr1.at? i: Option EntryT) with
    | some res => tr2.at? i = some res
    | none => True
:= by
  simp only [Trace.at?]
  grind

grind_pattern Trace.at?_le => tr1 ≤ tr2, tr1.at? (EntryT := EntryT) i
grind_pattern [grind_later] Trace.at?_le => tr1 ≤ tr2, tr1.at? (EntryT := EntryT) i

public
theorem Trace.at?_append
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr: Trace α) (entry: EntryT)
  : (tr.append entry).at? tr.length = some entry
:= by
  grind [Trace.append, Trace.at?, Trace.at, Trace.length, TraceEntryHas.inj_proj_eq]

public
theorem Trace.at?_eq_some
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr: Trace α) (i: Nat) (entry: EntryT)
  : (tr.at? i = some entry) = (∃ h_i: i < tr.length, tr.at i h_i = TraceEntryHas.inj entry)
:= by
  grind [Trace.at?, TraceEntryHas.inj_proj_eq]

public
theorem Trace.at?_eq_some_implies_length_le
  {EntryT α: Type} [TraceEntryHas EntryT α]
  (tr: Trace α) (i: Nat)
  : match (tr.at? i: Option EntryT) with
    | some _ => i < tr.length
    | none => True
:= by
  grind [Trace.at?]

grind_pattern Trace.at?_eq_some_implies_length_le => (tr.at? i: Option EntryT)

-- Execution trace

public
class ExecTraceTypes where
  ExecT: Type

@[expose]
public
def ExecTrace.Entry [ExecTraceTypes] := ExecTraceTypes.ExecT

public
abbrev ExecTrace [ExecTraceTypes] := Trace ExecTrace.Entry

public
class ExecTraceTypes.Has [ExecTraceTypes] (ExecEntryT: Type)
  extends TraceEntryHas ExecEntryT ExecTrace.Entry

public
class ExecTraceTypes.HasStep (ExecEntryT1: Type) (ExecEntryT2: semiOutParam Type) where
  inj: ExecEntryT1 → ExecEntryT2
  proj: ExecEntryT2 → Option ExecEntryT1
  inj_proj_eq: ∀ x y, (proj x = some y) = (x = inj y)

public
instance instExecTraceTypesHasItself [ExecTraceTypes]: ExecTraceTypes.Has ExecTrace.Entry where
  inj x := x
  proj x := some x
  inj_proj_eq := by grind

public
instance instExecTraceTypesHasStep
  [ExecTraceTypes]
  (ExecEntryT1 ExecEntryT2: Type)
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
  [ExecTraceTypes.Has ExecEntryT2]
  : ExecTraceTypes.Has ExecEntryT1
where
  inj x := TraceEntryHas.inj (ExecTraceTypes.HasStep.inj (ExecEntryT2 := ExecEntryT2) x)
  proj x :=
    match TraceEntryHas.proj (EntryT := ExecEntryT2) x with
    | none => none
    | some y => ExecTraceTypes.HasStep.proj y
  inj_proj_eq x y := by
    have := TraceEntryHas.inj_proj_eq (EntryT := ExecEntryT2) x
    have := ExecTraceTypes.HasStep.inj_proj_eq (ExecEntryT1 := ExecEntryT1) (ExecEntryT2 := ExecEntryT2)
    grind

public
instance [ExecTraceTypes] (ExecEntryT: Type) [inst: ExecTraceTypes.Has ExecEntryT]: TraceEntryHas ExecEntryT ExecTrace.Entry where
  inj := inst.inj
  proj := inst.proj
  inj_proj_eq := inst.inj_proj_eq

@[grind inj]
public
theorem TraceEntryHas.inj_injective
  (EntryT: Type) (α: Type)
  [TraceEntryHas EntryT α]
  : Function.Injective (TraceEntryHas.inj (EntryT := EntryT) (α := α))
:= by
  intro x1 x2
  have := TraceEntryHas.inj_proj_eq (EntryT := EntryT) (α := α) (TraceEntryHas.inj x1) x1
  have := TraceEntryHas.inj_proj_eq (EntryT := EntryT) (α := α) (TraceEntryHas.inj x2) x2
  grind

public
structure ExecTraceTypes.combine {n: Nat} (ExecTypes: Fin n → Type): Type where
  id: Fin n
  entry: ExecTypes id

public
instance instExecTraceTypesCombineHasStep
  {n: Nat}
  (Types: Fin n → Type)
  (id: Fin n)
  : ExecTraceTypes.HasStep (Types id) (ExecTraceTypes.combine Types) where
  inj entry := { id, entry }
  proj entry :=
    if h: entry.id = id then
      some (h ▸ entry.entry)
    else
      none
  inj_proj_eq x y := by
    cases x
    grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* ExecEntryT $params* from $sources,*) => do
    let options := parseOptions options
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `ExecEntryT
      combineName := ``DY.ExecTraceTypes.combine
      internalOutTypeStx := fun _ _ => `(term| Type)
      outTypeStx := fun _ => `(term| Type)
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `ExecEntryT
      combineName := ``DY.ExecTraceTypes.combine
      hasStepName := ``DY.ExecTraceTypes.HasStep
    }

    let execInternalStx := Lean.mkIdent `ExecEntryT.internal
    let execStx := Lean.mkIdent `ExecEntryT
    let topLevelInst ← `(command| public instance: DY.ExecTraceTypes where ExecT := $execStx)
    let topLevelHas ← `(command| public instance: DY.ExecTraceTypes.Has $execStx := inferInstanceAs (DY.ExecTraceTypes.Has DY.ExecTrace.Entry))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    let hasCombine ← mkHasCombine params {
      hasCombineStx args := `(term| DY.ExecTraceTypes.Has (DY.ExecTraceTypes.combine ($execInternalStx $args*)))
      hasStx args := `(term| DY.ExecTraceTypes.Has ($execStx $args*))
    }
    let hasCombine := if options.toplevel then hasCombine else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel ++ hasCombine)

end Meta.CombineMacro

end DY
