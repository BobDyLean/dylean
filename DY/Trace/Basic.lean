module

meta import DY.Trace.Grind

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

-- TODO: is there a typeclass about this?
@[grind ., refl]
public
theorem Trace.le_refl
  {α: Type}
  (tr: Trace α)
  : tr ≤ tr
:=
  Trace.le.equal tr

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
instance {α: Type} : Trans (· ≤ · : Trace α → Trace α → Prop) (· ≤ ·) (· ≤ ·) where
  trans {x y z} := Trace.le_trans x y z

public
class IntoTraceEntry (EntryT: Type) (α: Type) where
  make: EntryT → α

-- instance {α: Type}: IntoTraceEntry α α where
--   make x := x

public
def Trace.append
  {EntryT α: Type} [IntoTraceEntry EntryT α]
  (tr: Trace α) (entry: EntryT)
  : Trace α
:=
  .snoc tr (IntoTraceEntry.make entry)

public
def Trace.append_le
  {EntryT α: Type} [IntoTraceEntry EntryT α]
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
def Trace.at_is
  {EntryT α: Type} [IntoTraceEntry EntryT α]
  (tr: Trace α) (i: Nat) (entry: EntryT)
  : Prop
:=
  exists h: i < tr.length,
  tr.at i h = IntoTraceEntry.make entry

public
theorem Trace.at_is_le
  {EntryT α: Type} [IntoTraceEntry EntryT α]
  (tr1 tr2: Trace α) (i: Nat) (entry: EntryT)
  : tr1 ≤ tr2 →
    tr1.at_is i entry →
    tr2.at_is i entry
:= by
  simp only [Trace.at_is]
  grind

grind_pattern Trace.at_is_le => tr1 ≤ tr2, tr1.at_is i entry
grind_pattern [grind_later] Trace.at_is_le => tr1 ≤ tr2, tr1.at_is i entry

public
theorem Trace.at_is_append
  {EntryT α: Type} [IntoTraceEntry EntryT α]
  (tr: Trace α) (entry: EntryT)
  : (tr.append entry).at_is tr.length entry
:= by
  grind [Trace.append, Trace.at_is, Trace.at, Trace.length]

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
class ExecTraceTypes.Has [ExecTraceTypes] (ExecEntryT: Type) where
  inj: ExecEntryT → ExecTrace.Entry
  proj: ExecTrace.Entry → Option ExecEntryT
  inj_proj_eq: ∀ x y, (proj x = some y) = (x = inj y)

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
  inj x := ExecTraceTypes.Has.inj (ExecTraceTypes.HasStep.inj (ExecEntryT2 := ExecEntryT2) x)
  proj x :=
    match ExecTraceTypes.Has.proj (ExecEntryT := ExecEntryT2) x with
    | none => none
    | some y => ExecTraceTypes.HasStep.proj y
  inj_proj_eq x y := by
    have := ExecTraceTypes.Has.inj_proj_eq (ExecEntryT := ExecEntryT2) x
    have := ExecTraceTypes.HasStep.inj_proj_eq (ExecEntryT1 := ExecEntryT1) (ExecEntryT2 := ExecEntryT2)
    grind

public
instance [ExecTraceTypes] (ExecEntryT: Type) [ExecTraceTypes.Has ExecEntryT]: IntoTraceEntry ExecEntryT ExecTrace.Entry where
  make entry := ExecTraceTypes.Has.inj entry

@[grind inj]
public
theorem ExecTraceTypes.Has.inj_injective
  [ExecTraceTypes] (ExecEntryT: Type) [ExecTraceTypes.Has ExecEntryT]
  : Function.Injective (ExecTraceTypes.Has.inj (ExecEntryT := ExecEntryT))
:= by
  intro x1 x2
  have := ExecTraceTypes.Has.inj_proj_eq (ExecTraceTypes.Has.inj x1) x1
  have := ExecTraceTypes.Has.inj_proj_eq (ExecTraceTypes.Has.inj x2) x2
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

end DY
