module

public import DY.Trace
public import DY.Bytes
import DY.Meta.Step

namespace DY.ProtocolEvent

public
structure ExecEntryT (EventT: Type) where
  ev: EventT

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (EventT: Type): SubBaseAttackerKnowledge (ExecEntryT EventT) where
  attackerKnows _ _ _ := False

public
abbrev ProofEntryT (EventT: Type) := ExecEntryT EventT

public
instance (EventT: Type): ErasableProofEntry (ExecEntryT EventT) (ProofEntryT EventT) := ErasableProofEntry.default (ExecEntryT EventT)

public
instance (EventT: Type): ExecEntryAssociatedWithProofEntry (ExecEntryT EventT) (ProofEntryT EventT) where

public
class EventInv [ExecTraceTypes] [ProofTraceTypes] (EventT: Type) where
  invariant: ProofTrace → EventT → Prop

public
instance
  [ExecTraceTypes] [ProofTraceTypes] (EventT: Type) [EventInv EventT]
  : SubTraceInvariant (ProofEntryT EventT)
where
  invariant tr entry :=
    EventInv.invariant tr entry.ev

public
instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (EventT: Type)
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  [ProofTraceTypes.Has (ProofEntryT EventT)]
  [EventInv EventT]
  [TraceInvariant.Has (ProofEntryT EventT)]
  : SubBaseAttackerKnowledgeTheorem (ProofEntryT EventT) (baseAttackerKnowledge EventT)
where
  pf trBefore entry b := by
    simp [baseAttackerKnowledge]

public
def _root_.DY.Trace.EventLoggedAt
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT) (time: Nat)
  (tr: ExecTrace)
  : Prop
:=
  tr.at? time = some (ExecEntryT.mk ev)

public
theorem _root_.DY.Trace.EventLoggedAt_implies_i_le_length
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT) (i: Nat)
  (tr: ExecTrace)
  : tr.EventLoggedAt ev i →
    i < tr.length
:= by
  grind [Trace.EventLoggedAt]

grind_pattern DY.Trace.EventLoggedAt_implies_i_le_length => tr.EventLoggedAt ev i

public
def _root_.DY.Trace.getEventAt
  (EventT: Type)
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (i: Nat)
  (tr: ExecTrace)
  : Option EventT
:=
  match (tr.at? i: Option (ExecEntryT EventT)) with
  | none => none
  | some entry => entry.ev

public
theorem _root_.DY.Trace.EventLoggedAt_eq_getEventAt
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT) (i: Nat) (tr: ExecTrace)
  : tr.EventLoggedAt ev i = (tr.getEventAt EventT i = some ev)
:= by
  dsimp only [Trace.EventLoggedAt, Trace.getEventAt]
  grind [cases ExecEntryT]

public
theorem _root_.DY.Trace.EventLoggedAt_le
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT) (time: Nat)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    tr1.EventLoggedAt ev time →
    tr2.EventLoggedAt ev time
:= by
  grind [Trace.EventLoggedAt]

grind_pattern Trace.EventLoggedAt_le => tr1 ≤ tr2, tr1.EventLoggedAt ev time
grind_pattern [grind_later] Trace.EventLoggedAt_le => tr1 ≤ tr2, tr1.EventLoggedAt ev time

@[grind]
public
def _root_.DY.Trace.EventLogged
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT)
  (tr: ExecTrace)
  : Prop
:=
  ∃ i, tr.EventLoggedAt ev i

public
theorem _root_.DY.Trace.EventLogged_le
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    tr1.EventLogged ev →
    tr2.EventLogged ev
:= by
  grind [Trace.EventLoggedAt]

grind_pattern Trace.EventLogged_le => tr1 ≤ tr2, tr1.EventLogged ev
grind_pattern [grind_later] Trace.EventLogged_le => tr1 ≤ tr2, tr1.EventLogged ev

public
theorem _root_.DY.Trace.EventLoggedAt_imp_EventInv
  {EventT: Type}
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [EventInv EventT]
  [ExecTraceTypes.Has (ExecEntryT EventT)] [ProofTraceTypes.Has (ProofEntryT EventT)] [TraceInvariant.Has (ProofEntryT EventT)]
  (ev: EventT)
  (i: Nat)
  (tr: ProofTrace)
  : tr.Invariant →
    tr.erase.EventLoggedAt ev i →
    EventInv.invariant (tr.prefix i) ev
:= by
  intro h_inv h_ev
  have := Trace.invariant_at tr i (by grind [Trace.EventLoggedAt]) h_inv
  suffices SubTraceInvariant.invariant (tr.prefix i) (ExecEntryT.mk ev) by
    simp_all [SubTraceInvariant.invariant]
  rewrite [← TraceInvariant.Has.inv_commutes]
  simp [Trace.EventLoggedAt, Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ErasableProofEntry.erase] at h_ev
  grind

public
def logEvent
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT): Traceful Unit
:= do
  let entry: ExecEntryT EventT := { ev }
  let _i ← appendEntry entry
  return ()

@[instance]
public
theorem logEvent.spec
  {EventT: Type}
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [EventInv EventT]
  [ExecTraceTypes.Has (ExecEntryT EventT)] [ProofTraceTypes.Has (ProofEntryT EventT)] [TraceInvariant.Has (ProofEntryT EventT)]
  (ev: EventT)
  : HoareTriple
    (logEvent ev)
    (fun tr => EventInv.invariant tr ev)
    (fun _ tr => tr.erase.EventLogged ev)
:= by
  apply HoareTriple.mk
  unfold logEvent
  dsimp only
  unfold hoareTriple
  intro tr h_pre h_inv
  mark_non_monotone h_pre
  step with ⟨ fun _ => ExecEntryT.mk ev ⟩ by simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
  step
  simp only [Trace.EventLogged, Trace.EventLoggedAt]
  exists _i
  have := ProofTrace.Entry.at?_eq_some_erase tr _i (ExecEntryT.mk ev)
  simp_all [ErasableProofEntry.erase]

public
def label
  {EventT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT)
  : Label
where
  isCorrupt tr := tr.EventLogged ev

public
theorem label_isCorrupt
  {EventT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT) (tr: ExecTrace)
  : (label ev).isCorrupt tr = tr.EventLogged ev
:= by
  rfl

grind_pattern label_isCorrupt => (label ev).isCorrupt tr

end DY.ProtocolEvent
