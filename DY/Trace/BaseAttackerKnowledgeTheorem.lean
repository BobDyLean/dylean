module

public import DY.Bytes.Basic
public import DY.Bytes.Invariants
public import DY.Trace.Basic
public import DY.Trace.Invariant
public import DY.Trace.BaseAttackerKnowledge
import all DY.Trace.Invariant
import all DY.Trace.BaseAttackerKnowledge

namespace DY

public
structure EntryBaseAttackerKnowledgeTheorem
  [TraceInvariant]
  [BytesFunctor] [BytesInvariants]
  {ExecEntryT: Type} {ProofEntryT: Type}
  {func: ProofEntryFun ExecEntryT ProofEntryT}
  (inv: TraceEntryInvariant func)
  [TraceTypes.Has func] [TraceInvariant.Has inv]
  (att: EntryBaseAttackerKnowledge ExecEntryT)
where
  pf: ∀ trBefore entry (b: Bytes),
    inv.invariant trBefore entry →
    att.attackerKnows trBefore.erase (func.erase entry) b →
    b.Publishable trBefore -- could also be `b.Publishable (trBefore.append entry)` if needed

public
class BaseAttackerKnowledgeTheorem
  [TraceInvariant]
  [BytesFunctor] [BytesInvariants]
  [BaseAttackerKnowledge]
where
  pfs: ∀ id, EntryBaseAttackerKnowledgeTheorem (TraceInvariant.invs id) (BaseAttackerKnowledge.attackerKnows id)

public
theorem Trace.BaseAttackerKnows_implies_Publishable
  [TraceInvariant]
  [BytesFunctor] [BytesInvariants] [BytesInvariantsProofs]
  [BaseAttackerKnowledge] [BaseAttackerKnowledgeTheorem]
  (tr: ProofTrace) (b: Bytes)
  : Trace.Invariant tr →
    Trace.BaseAttackerKnows tr.erase b →
    b.Publishable tr
:= by
  induction tr
  · simp [Trace.BaseAttackerKnows, Trace.erase]
  rename_i trBefore entry ih
  have h_le: trBefore ≤ trBefore.snoc entry := by apply Trace.le.extend; apply Trace.le.equal
  simp only [Trace.Invariant, Trace.BaseAttackerKnows, Trace.erase]
  intro h_inv h_att
  cases h_att
  · have := (BaseAttackerKnowledgeTheorem.pfs entry.id).pf trBefore entry.entry b (by grind [ProofTrace.Entry.Invariant]) (by grind [ProofTrace.Entry.erase])
    grind
  · grind

end DY
