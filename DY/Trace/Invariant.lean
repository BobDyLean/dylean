module

public import DY.Trace.Basic

namespace DY

public
structure ProofEntryType (ExecEntryT: ExecEntryType) where
  type: [ExecTraceTypes] → Type
  erase: ∀ [ExecTraceTypes], type → ExecEntryT.type

public
class ProofTraceTypes [ExecTraceTypes] where
  proofEntries: ∀ id, ProofEntryType (ExecTraceTypes.entries id)

public
class abbrev TraceTypes := ExecTraceTypes, ProofTraceTypes

public
structure ProofTrace.Entry [TraceTypes] where
  id: Fin ExecTraceTypes.n
  entry: (ProofTraceTypes.proofEntries id).type

public
abbrev ProofTrace [TraceTypes] := Trace ProofTrace.Entry

public
def ProofTrace.Entry.erase
  [TraceTypes]
  (entry: ProofTrace.Entry)
  : ExecTrace.Entry
where
  id := entry.id
  entry := (ProofTraceTypes.proofEntries entry.id).erase entry.entry

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
theorem Trace.erase_le [TraceTypes] (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    tr1.erase ≤ tr2.erase
:= by
  intro h_le
  induction h_le
  · apply Trace.le.equal
  · apply Trace.le.extend
    assumption

grind_pattern Trace.erase_le => tr1 ≤ tr2, tr1.erase

-- public
-- theorem Trace.erase_append
--   [TraceTypes]
--   (tr: ProofTrace) (entry: ProofTrace.Entry)
--   : (tr.append entry).erase = tr.erase.append entry.erase
-- := by
--   rfl

-- TODO test coercion
example [TraceTypes]: Coe ProofTrace ExecTrace where
  coe tr := tr.erase

-- Invariant

public
structure ProofTraceEntryInvariant
  [TraceTypes]
  {ExecEntryT: ExecEntryType}
  (ProofEntryT: ProofEntryType ExecEntryT)
where
  invariant: ProofTrace → ProofEntryT.type → Prop

public
class ProofTraceInvariants [TraceTypes] where
  invariants: ∀ id, ProofTraceEntryInvariant (ProofTraceTypes.proofEntries id)

public
def Trace.Invariant
  [TraceTypes] [ProofTraceInvariants]
  (tr: ProofTrace)
  : Prop
:=
  match tr with
  | .nil => True
  | .snoc trBefore entry =>
    trBefore.Invariant ∧
    (ProofTraceInvariants.invariants entry.id).invariant trBefore entry.entry

end DY
