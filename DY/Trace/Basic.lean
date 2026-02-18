module

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
  | equal => simp_all
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

-- Execution trace

public
structure ExecEntryType where
  type: Type

public
class ExecTraceTypes where
  n: Nat
  entries: Fin n → ExecEntryType

public
structure ExecTrace.Entry [ExecTraceTypes] where
  id: Fin ExecTraceTypes.n
  entry: (ExecTraceTypes.entries id).type

public
abbrev ExecTrace [ExecTraceTypes] := Trace ExecTrace.Entry

-- class ExecTraceEntry [ExecTraceTypes] (Entry: ExecEntryType) extends IntoTraceEntry Entry.type ExecTrace.Entry
--
-- example
--   [ExecTraceTypes] {Entry: ExecEntryType} [ExecTraceEntry Entry]
--   (tr: ExecTrace) (entry: Entry.type)
--   : ExecTrace
-- :=
--   tr.append entry

end DY
