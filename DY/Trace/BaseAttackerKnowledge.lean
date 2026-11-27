module

public import DY.Bytes.Basic
public import DY.Trace.Basic
import all DY.Trace.Basic
public meta import DY.Meta.CombineMacro

namespace DY

public
structure Trace.BaseAttackerKnows.Part [Bytes.Def] [ExecTrace.Def] (ExecEntryT: Type) where
  attackerKnows: ExecTrace → ExecEntryT → Bytes → Prop

public
class Trace.BaseAttackerKnows.Def [Bytes.Def] [ExecTrace.Def] where
  whole: Trace.BaseAttackerKnows.Part ExecTrace.Entry

public
class Trace.BaseAttackerKnows.Has
  [Bytes.Def] [ExecTrace.Def]
  [Trace.BaseAttackerKnows.Def]
  {ExecEntryT: Type}
  [ExecTrace.Has ExecEntryT]
  (sub: Trace.BaseAttackerKnows.Part ExecEntryT)
where
  pf: ∀ tr entry b,
    sub.attackerKnows tr entry b →
    Trace.BaseAttackerKnows.Def.whole.attackerKnows tr (TraceEntryHas.inj entry) b

public
class Trace.BaseAttackerKnows.HasStep
  [Bytes.Def] [ExecTrace.Def]
  {ExecEntryT1: Type} {ExecEntryT2: semiOutParam Type}
  [ExecTrace.HasStep ExecEntryT1 ExecEntryT2]
  (sub1: Trace.BaseAttackerKnows.Part ExecEntryT1)
  (sub2: semiOutParam (Trace.BaseAttackerKnows.Part ExecEntryT2))
where
  pf: ∀ tr entry b,
    sub1.attackerKnows tr entry b →
    sub2.attackerKnows tr (ExecTrace.HasStep.inj entry) b

public
instance instTraceBaseAttackerKnowsHasItself
  [Bytes.Def] [ExecTrace.Def]
  [Trace.BaseAttackerKnows.Def]
  : Trace.BaseAttackerKnows.Has (Trace.BaseAttackerKnows.Def.whole)
where
  pf := by simp [TraceEntryHas.inj]

public
instance instTraceBaseAttackerKnowsHasStep
  [Bytes.Def] [ExecTrace.Def]
  [Trace.BaseAttackerKnows.Def]
  {ExecEntryT1 ExecEntryT2: Type}
  [ExecTrace.HasStep ExecEntryT1 ExecEntryT2]
  [ExecTrace.Has ExecEntryT2]
  (sub1: Trace.BaseAttackerKnows.Part ExecEntryT1)
  (sub2: Trace.BaseAttackerKnows.Part ExecEntryT2)
  [Trace.BaseAttackerKnows.HasStep sub1 sub2]
  [Trace.BaseAttackerKnows.Has sub2]
  : Trace.BaseAttackerKnows.Has sub1
where
  pf := by
    have := Trace.BaseAttackerKnows.HasStep.pf (sub1 := sub1) (sub2 := sub2)
    have := Trace.BaseAttackerKnows.Has.pf (sub := sub2)
    simp [TraceEntryHas.inj]
    grind

public
def Trace.BaseAttackerKnows.combine
  [Bytes.Def] [ExecTrace.Def]
  {n: Nat}
  {Types: Fin n → Type}
  (subs: (id: Fin n) → Trace.BaseAttackerKnows.Part (Types id))
  : Trace.BaseAttackerKnows.Part (ExecTrace.combine Types)
where
  attackerKnows := fun tr {id, entry} b =>
    (subs id).attackerKnows tr entry b

public
instance instTraceBaseAttackerKnowsCombineHasStep
  [Bytes.Def] [ExecTrace.Def]
  {n: Nat}
  {Types: Fin n → Type}
  (subs: (id: Fin n) → Trace.BaseAttackerKnows.Part (Types id))
  (id: Fin n)
  : Trace.BaseAttackerKnows.HasStep (subs id) (Trace.BaseAttackerKnows.combine subs)
where
  pf := by
    simp [ExecTrace.HasStep.inj, Trace.BaseAttackerKnows.combine]

public
def Trace.BaseAttackerKnows
  [Bytes.Def] [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
  (tr: ExecTrace) (b: Bytes)
  : Prop
:=
  ∃ i h_i, Trace.BaseAttackerKnows.Def.whole.attackerKnows (tr.prefix i) (tr.at i h_i) b

public
theorem Trace.BaseAttackerKnows_le
  [Bytes.Def] [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
  (b: Bytes) (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    Trace.BaseAttackerKnows tr1 b →
    Trace.BaseAttackerKnows tr2 b
:= by
  grind [Trace.BaseAttackerKnows]

grind_pattern Trace.BaseAttackerKnows_le => tr1 ≤ tr2, Trace.BaseAttackerKnows tr1 b

public
theorem Trace.prove_BaseAttackerKnows
  [Bytes.Def] [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
  {ExecEntryT: Type}
  [ExecTrace.Has ExecEntryT]
  (sub: Trace.BaseAttackerKnows.Part ExecEntryT)
  [Trace.BaseAttackerKnows.Has sub]
  (tr: ExecTrace) (entry: ExecEntryT) (b: Bytes)
  (time: Nat)
  : tr.at? time = some entry →
    sub.attackerKnows (tr.prefix time) entry b →
    Trace.BaseAttackerKnows tr b
:= by
  dsimp only [Trace.BaseAttackerKnows]
  simp only [Trace.at?_eq_some]
  have := Trace.BaseAttackerKnows.Has.pf (sub := sub) (tr.prefix time) entry b
  grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* Trace.BaseAttackerKnows $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.Bytes.Def])), (← `(bracketedBinder| [DY.ExecTrace.Def]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `TracePart.baseAttackerKnows
      refereeName := `TracePart.Exec
      combineName := ``DY.Trace.BaseAttackerKnows.combine
      outTypeName := ``DY.Trace.BaseAttackerKnows.Part
      isTheorem := false
    }


    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `TracePart.baseAttackerKnows
      combineName := ``DY.Trace.BaseAttackerKnows.combine
      hasStepName := ``DY.Trace.BaseAttackerKnows.HasStep
    }

    let baseAttStx := Lean.mkIdent `TracePart.baseAttackerKnows
    let topLevelInst ← `(command| public instance: DY.Trace.BaseAttackerKnows.Def where whole := $baseAttStx)
    let topLevelHas ← `(command| public instance: DY.Trace.BaseAttackerKnows.Has $baseAttStx := inferInstanceAs (DY.Trace.BaseAttackerKnows.Has DY.Trace.BaseAttackerKnows.Def.whole))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel)

end Meta.CombineMacro

end DY
