module

public import DY.Bytes.Basic
public import DY.Trace.Basic
import all DY.Trace.Basic
public meta import DY.Meta.CombineMacro

namespace DY

public
structure SubBaseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (ExecEntryT: Type) where
  attackerKnows: ExecTrace → ExecEntryT → Bytes → Prop

public
class BaseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] where
  attackerKnows: SubBaseAttackerKnowledge ExecTrace.Entry

public
class BaseAttackerKnowledge.Has
  [BytesFunctor] [ExecTraceTypes]
  [BaseAttackerKnowledge]
  {ExecEntryT: Type}
  [ExecTraceTypes.Has ExecEntryT]
  (sub: SubBaseAttackerKnowledge ExecEntryT)
where
  pf: ∀ tr entry b,
    sub.attackerKnows tr entry b →
    BaseAttackerKnowledge.attackerKnows.attackerKnows tr (TraceEntryHas.inj entry) b

public
class BaseAttackerKnowledge.HasStep
  [BytesFunctor] [ExecTraceTypes]
  {ExecEntryT1: Type} {ExecEntryT2: semiOutParam Type}
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
  (sub1: SubBaseAttackerKnowledge ExecEntryT1)
  (sub2: semiOutParam (SubBaseAttackerKnowledge ExecEntryT2))
where
  pf: ∀ tr entry b,
    sub1.attackerKnows tr entry b →
    sub2.attackerKnows tr (ExecTraceTypes.HasStep.inj entry) b

public
instance instBaseAttackerKnowledgeHasItself
  [BytesFunctor] [ExecTraceTypes]
  [BaseAttackerKnowledge]
  : BaseAttackerKnowledge.Has (BaseAttackerKnowledge.attackerKnows)
where
  pf := by simp [TraceEntryHas.inj]

public
instance instBaseAttackerKnowledgeHasStep
  [BytesFunctor] [ExecTraceTypes]
  [BaseAttackerKnowledge]
  {ExecEntryT1 ExecEntryT2: Type}
  [ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2]
  [ExecTraceTypes.Has ExecEntryT2]
  (sub1: SubBaseAttackerKnowledge ExecEntryT1)
  (sub2: SubBaseAttackerKnowledge ExecEntryT2)
  [BaseAttackerKnowledge.HasStep sub1 sub2]
  [BaseAttackerKnowledge.Has sub2]
  : BaseAttackerKnowledge.Has sub1
where
  pf := by
    have := BaseAttackerKnowledge.HasStep.pf (sub1 := sub1) (sub2 := sub2)
    have := BaseAttackerKnowledge.Has.pf (sub := sub2)
    simp [TraceEntryHas.inj]
    grind

public
def SubBaseAttackerKnowledge.combine
  [BytesFunctor] [ExecTraceTypes]
  {n: Nat}
  {Types: Fin n → Type}
  (subs: (id: Fin n) → SubBaseAttackerKnowledge (Types id))
  : SubBaseAttackerKnowledge (ExecTraceTypes.combine Types)
where
  attackerKnows := fun tr {id, entry} b =>
    (subs id).attackerKnows tr entry b

public
instance instBaseAttackerKnowledgeCombineHasStep
  [BytesFunctor] [ExecTraceTypes]
  {n: Nat}
  {Types: Fin n → Type}
  (subs: (id: Fin n) → SubBaseAttackerKnowledge (Types id))
  (id: Fin n)
  : BaseAttackerKnowledge.HasStep (subs id) (SubBaseAttackerKnowledge.combine subs)
where
  pf := by
    simp [ExecTraceTypes.HasStep.inj, SubBaseAttackerKnowledge.combine]

public
def Trace.BaseAttackerKnows
  [BytesFunctor] [ExecTraceTypes] [BaseAttackerKnowledge]
  (tr: ExecTrace) (b: Bytes)
  : Prop
:=
  match tr with
  | .nil => False
  | .snoc trBefore entry =>
    BaseAttackerKnowledge.attackerKnows.attackerKnows trBefore entry b ∨
    Trace.BaseAttackerKnows trBefore b

public
theorem Trace.BaseAttackerKnows_le
  [BytesFunctor] [ExecTraceTypes] [BaseAttackerKnowledge]
  (b: Bytes) (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    Trace.BaseAttackerKnows tr1 b →
    Trace.BaseAttackerKnows tr2 b
:= by
  intro h
  induction h <;>
  grind [Trace.BaseAttackerKnows]

grind_pattern Trace.BaseAttackerKnows_le => tr1 ≤ tr2, Trace.BaseAttackerKnows tr1 b

public
theorem Trace.prove_BaseAttackerKnows
  [BytesFunctor] [ExecTraceTypes] [BaseAttackerKnowledge]
  {ExecEntryT: Type}
  [ExecTraceTypes.Has ExecEntryT]
  (sub: SubBaseAttackerKnowledge ExecEntryT)
  [BaseAttackerKnowledge.Has sub]
  (tr: ExecTrace) (entry: ExecEntryT) (b: Bytes)
  (time: Nat)
  : tr.at? time = some entry →
    sub.attackerKnows (tr.prefix time) entry b →
    Trace.BaseAttackerKnows tr b
:= by
  simp only [tr.at?_eq_some]
  induction tr
  · grind [Trace.length]
  rename_i tr entry' ih
  have := BaseAttackerKnowledge.Has.pf (sub := sub) tr entry b
  simp_all [Trace.prefix, Trace.at, Trace.BaseAttackerKnows]
  grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* baseAttackerKnowledge $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `baseAttackerKnowledge
      refereeName := `ExecEntryT
      combineName := ``DY.SubBaseAttackerKnowledge.combine
      outTypeName := ``DY.SubBaseAttackerKnowledge
    }


    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `baseAttackerKnowledge
      combineName := ``DY.SubBaseAttackerKnowledge.combine
      hasStepName := ``DY.BaseAttackerKnowledge.HasStep
    }

    let baseAttStx := Lean.mkIdent `baseAttackerKnowledge
    let topLevelInst ← `(command| public instance: DY.BaseAttackerKnowledge where attackerKnows := $baseAttStx)
    let topLevelHas ← `(command| public instance: DY.BaseAttackerKnowledge.Has $baseAttStx := inferInstanceAs (DY.BaseAttackerKnowledge.Has DY.BaseAttackerKnowledge.attackerKnows))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel)

end Meta.CombineMacro

end DY
