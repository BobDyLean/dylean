module

public import DY.Trace
public import DY.Bytes
import DY.Step.Init
import all DY.Trace
public import DY.Step.Init
import all DY.Step.Init

namespace DY.ProtocolEvent

public
structure ExecEntryT (EventT: Type) where
  ev: EventT

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes] (EventT: Type): EntryBaseAttackerKnowledge (ExecEntryT EventT) where
  attackerKnows _ _ _ := False

public
abbrev ProofEntryT (EventT: Type) := ExecEntryT EventT

public
def ProofEntryFunc (EventT: Type) := ProofEntryFun.default (ExecEntryT EventT)

public
class EventInv [TraceTypes] (EventT: Type) where
  invariant: ProofTrace → EventT→ Prop

public
def Invariant [TraceTypes] (EventT: Type) [EventInv EventT]: TraceEntryInvariant (ProofEntryFunc EventT) where
  invariant tr entry :=
    EventInv.invariant tr entry.ev

public
theorem baseAttackerKnowledgeTheorem [TraceInvariant] [BytesFunctor] [BytesInvariants] (EventT: Type) [TraceTypes.Has (ProofEntryFunc EventT)] [EventInv EventT] [TraceInvariant.Has (Invariant EventT)]: EntryBaseAttackerKnowledgeTheorem (Invariant EventT) (baseAttackerKnowledge EventT) where
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
  tr.at_is time (ExecEntryT.mk ev)

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

public
abbrev _root_.DY.Trace.EventLogged
  {EventT: Type}
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ExecEntryT EventT)]
  (ev: EventT)
  (tr: ExecTrace)
  : Prop
:=
  ∃ i, tr.EventLoggedAt ev i

public
theorem _root_.DY.Trace.EventLoggedAt_imp_EventInv
  {EventT: Type}
  [TraceInvariant]
  [EventInv EventT]
  [TraceTypes.Has (ProofEntryFunc EventT)] [TraceInvariant.Has (Invariant EventT)]
  (ev: EventT)
  (i: Nat)
  (tr: ProofTrace)
  : tr.Invariant →
    tr.erase.EventLoggedAt ev i →
    EventInv.invariant (tr.prefix i) ev
:= by
  intro h_inv h_ev
  have := Trace.invariant_at tr i (by grind [Trace.EventLoggedAt, Trace.at_is]) h_inv
  suffices (Invariant EventT).invariant (tr.prefix i) (ExecEntryT.mk ev) by
    simp_all [Invariant]
  rewrite [← TraceInvariant.Has.inv_commutes]
  simp [Trace.EventLoggedAt, Trace.at_is, IntoTraceEntry.make, Trace.erase_at] at h_ev
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
  [TraceInvariant]
  [EventInv EventT]
  [TraceTypes.Has (ProofEntryFunc EventT)] [TraceInvariant.Has (Invariant EventT)]
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
  step with ⟨ ExecEntryT.mk ev ⟩ by simp_all [ProofEntryFunc, Invariant]
  step
  simp only [Trace.EventLogged, Trace.EventLoggedAt]
  exists _i
  have := Trace.at_is_erase tr _i (ExecEntryT.mk ev)
  grind [ProofEntryFunc]

end DY.ProtocolEvent
