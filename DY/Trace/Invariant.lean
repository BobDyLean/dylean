module

public import DY.Trace.Basic
import all DY.Trace.Basic

namespace DY

public
structure ProofEntryFun (ExecEntryT ProofEntryT: Type) where
  erase: ProofEntryT → ExecEntryT

public
class TraceTypes extends ExecTraceTypes where
  proofEntries: Fin ExecTraceTypes.n → Type
  funs: ∀ id, ProofEntryFun (ExecTraceTypes.entries id) (proofEntries id)

public
structure ProofTrace.Entry [TraceTypes] where
  id: Fin ExecTraceTypes.n
  entry: (TraceTypes.proofEntries id)

public
abbrev ProofTrace [TraceTypes] := Trace ProofTrace.Entry

@[expose]
public
def ProofTrace.Entry.erase
  [TraceTypes]
  (entry: ProofTrace.Entry)
  : ExecTrace.Entry
where
  id := entry.id
  entry := (TraceTypes.funs entry.id).erase entry.entry

public
def Trace.erase
  [TraceTypes]
  (tr: ProofTrace)
  : ExecTrace
:=
  match tr with
  | .nil => .nil
  | .snoc trBefore entry => .snoc trBefore.erase entry.erase

public
theorem Trace.erase_le
  [TraceTypes]
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

public
theorem Trace.erase_length
  [TraceTypes]
  (tr: ProofTrace)
  : tr.erase.length = tr.length
:= by
  induction tr <;>
  simp_all [Trace.length, Trace.erase]

public
def Trace.erase_at
  [TraceTypes]
  (tr: ProofTrace)
  (i: Nat) (h_i: i < tr.erase.length)
  : tr.erase.at i h_i = (tr.at i (Trace.erase_length tr ▸ h_i)).erase
:= by
  induction tr <;>
  simp only [Trace.at, Trace.erase]
  · grind
  split <;>
  grind [Trace.erase_length]

public
class TraceTypes.Has [TraceTypes] {ExecEntryT: outParam Type} {ProofEntryT: Type} (func: outParam (ProofEntryFun ExecEntryT ProofEntryT)) extends ExecTraceTypes.Has ExecEntryT where
  proofInj: ProofEntryT → ProofTrace.Entry
  proofProj: ProofTrace.Entry → Option ProofEntryT
  proof_inj_proj_eq: ∀ x y, (proofProj x = some y) = (x = proofInj y)
  proofProj_none_eq_erase: ∀ x, ((proofProj x: Option ProofEntryT) = none) = ((proj x.erase: Option ExecEntryT) = none)
  erase_commutes: ∀ entry, (proofInj entry).erase = inj (func.erase entry)

public
instance [TraceTypes] (id: Fin ExecTraceTypes.n): TraceTypes.Has (TraceTypes.funs id) where
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
    simp [ExecTraceTypes.Has.proj, ProofTrace.Entry.erase]
  erase_commutes _ := rfl

public
instance [TraceTypes] {ExecEntryT ProofEntryT: Type} (func: ProofEntryFun ExecEntryT ProofEntryT) [TraceTypes.Has func]: IntoTraceEntry ProofEntryT ProofTrace.Entry where
  make entry := TraceTypes.Has.proofInj entry

public
theorem Trace.append_erase
  [TraceTypes]
  {ExecEntryT ProofEntryT: Type}
  {func: ProofEntryFun ExecEntryT ProofEntryT}
  [TraceTypes.Has func]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).erase = tr.erase.append (func.erase entry)
:= by
  simp [Trace.append, Trace.erase, IntoTraceEntry.make, TraceTypes.Has.erase_commutes]

-- Invariant

public
structure TraceEntryInvariant [TraceTypes] {ExecEntryT ProofEntryT: Type} (func: ProofEntryFun ExecEntryT ProofEntryT) where
  invariant: ProofTrace → ProofEntryT → Prop

public
class TraceInvariant extends TraceTypes where
  invs: ∀ id, TraceEntryInvariant (TraceTypes.funs id)

-- TODO test coercion
example [TraceInvariant]: Coe ProofTrace ExecTrace where
  coe tr := tr.erase

public
def ProofTrace.Entry.Invariant
  [TraceInvariant]
  (trBefore: ProofTrace)
  (entry: ProofTrace.Entry)
  : Prop
:=
  (TraceInvariant.invs entry.id).invariant trBefore entry.entry

public
def Trace.Invariant
  [TraceInvariant]
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
  [TraceInvariant]
  {ExecEntryT: Type} {ProofEntryT: Type}
  {func: ProofEntryFun ExecEntryT ProofEntryT}
  (inv: outParam (TraceEntryInvariant func))
  extends toTraceTypes: TraceTypes.Has func
  where
  inv_commutes: ∀ trBefore entry, (proofInj entry).Invariant trBefore = inv.invariant trBefore entry

public
theorem Trace.invariant_append
  [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  {func: ProofEntryFun ExecEntryT ProofEntryT}
  {inv: TraceEntryInvariant func}
  [TraceInvariant.Has inv]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).Invariant = (tr.Invariant ∧ inv.invariant tr entry)
:= by
  simp [Trace.Invariant, Trace.append, IntoTraceEntry.make, TraceInvariant.Has.inv_commutes]

public
theorem Trace.invariant_at
  [TraceInvariant]
  (tr: ProofTrace)
  (i: Nat)
  (h_i: i < tr.length)
  : tr.Invariant →
    (tr.at i h_i).Invariant (tr.prefix i)
:= by
  fun_induction Trace.at <;>
  grind [Trace.Invariant, Trace.prefix, Trace.length]

end DY
