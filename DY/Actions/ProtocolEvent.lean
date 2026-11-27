module

public import DY.Trace
public import DY.Bytes
import DY.Meta.Step

namespace DY.ProtocolEvent

public
structure TracePart.Exec (EventT: Type) where
  ev: EventT

public
def TracePart.baseAttackerKnows [Bytes.Def] [ExecTrace.Def] (EventT: Type): Trace.BaseAttackerKnows.Part (TracePart.Exec EventT) where
  attackerKnows _ _ _ := False

public
abbrev TracePart.Proof (EventT: Type) := TracePart.Exec EventT

public
instance (EventT: Type): ProofTrace.Part (TracePart.Exec EventT) (TracePart.Proof EventT) := ProofTrace.Part.default (TracePart.Exec EventT)

public
instance (EventT: Type): ExecEntryAssociatedWithProofEntry (TracePart.Exec EventT) (TracePart.Proof EventT) where

public
class EventInv [ExecTrace.Def] [ProofTrace.Def] (EventT: Type) where
  invariant: ProofTrace → EventT → Prop

public
instance TracePart.invariant
  [ExecTrace.Def] [ProofTrace.Def] (EventT: Type) [EventInv EventT]
  : Trace.Invariant.Part (TracePart.Proof EventT)
where
  invariant tr entry :=
    EventInv.invariant tr entry.ev

public
instance
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def] [Bytes.Def] [Bytes.Invariants.Def]
  (EventT: Type)
  [ExecTrace.Has (TracePart.Exec EventT)]
  [ProofTrace.Has (TracePart.Proof EventT)]
  [EventInv EventT]
  [Trace.Invariant.Has (TracePart.Proof EventT)]
  : Trace.BaseAttackerKnows_implies_Publishable.Part (TracePart.Proof EventT) (TracePart.baseAttackerKnows EventT)
where
  pf trBefore entry b := by
    simp [TracePart.baseAttackerKnows]

public
def _root_.DY.Trace.EventLoggedAt
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT) (time: Nat)
  (tr: ExecTrace)
  : Prop
:=
  tr.at? time = some (TracePart.Exec.mk ev)

public
theorem _root_.DY.Trace.EventLoggedAt_implies_i_le_length
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
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
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (i: Nat)
  (tr: ExecTrace)
  : Option EventT
:=
  match (tr.at? i: Option (TracePart.Exec EventT)) with
  | none => none
  | some entry => entry.ev

public
theorem _root_.DY.Trace.EventLoggedAt_eq_getEventAt
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT) (i: Nat) (tr: ExecTrace)
  : tr.EventLoggedAt ev i = (tr.getEventAt EventT i = some ev)
:= by
  dsimp only [Trace.EventLoggedAt, Trace.getEventAt]
  grind [cases TracePart.Exec]

public
theorem _root_.DY.Trace.EventLoggedAt_le
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT) (time: Nat)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    tr1.EventLoggedAt ev time →
    tr2.EventLoggedAt ev time
:= by
  grind [Trace.EventLoggedAt]

grind_pattern Trace.EventLoggedAt_le => tr1 ≤ tr2, tr1.EventLoggedAt ev time
grind_pattern [grind_later] Trace.EventLoggedAt_le => tr1 ≤ tr2, tr1.EventLoggedAt ev time

public
theorem _root_.DY.Trace.EventLoggedAt_le'
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT) (time: Nat)
  (tr1 tr2: ExecTrace)
  : time < tr1.length →
    tr1 ≤ tr2 →
    tr2.EventLoggedAt ev time →
    tr1.EventLoggedAt ev time
:= by
  grind [Trace.EventLoggedAt, Trace.at?_eq_some]

grind_pattern Trace.EventLoggedAt_le => tr1 ≤ tr2, tr1.EventLoggedAt ev time
grind_pattern [grind_later] Trace.EventLoggedAt_le => tr1 ≤ tr2, tr1.EventLoggedAt ev time

@[expose, grind]
public
def _root_.DY.Trace.EventLogged
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT)
  (tr: ExecTrace)
  : Prop
:=
  ∃ i, tr.EventLoggedAt ev i

public
theorem _root_.DY.Trace.EventLogged_le
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
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
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [EventInv EventT]
  [ExecTrace.Has (TracePart.Exec EventT)] [ProofTrace.Has (TracePart.Proof EventT)] [Trace.Invariant.Has (TracePart.Proof EventT)]
  (ev: EventT)
  (i: Nat)
  (tr: ProofTrace)
  : tr.Invariant →
    tr.erase.EventLoggedAt ev i →
    EventInv.invariant (tr.prefix i) ev
:= by
  intro h_inv h_ev
  have := Trace.invariant_at tr i (by grind [Trace.EventLoggedAt]) h_inv
  suffices Trace.Invariant.Part.invariant (tr.prefix i) (TracePart.Exec.mk ev) by
    simp_all [Trace.Invariant.Part.invariant]
  rewrite [← Trace.Invariant.Has.inv_commutes]
  simp [Trace.EventLoggedAt, Trace.at?_eq_some, Trace.erase_at, ProofTrace.Entry.erase_eq_imp_exists, ProofTrace.Part.erase] at h_ev
  grind

public
theorem _root_.DY.Trace.EventLogged_imp_EventInv
  {EventT: Type}
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [EventInv EventT]
  [ExecTrace.Has (TracePart.Exec EventT)] [ProofTrace.Has (TracePart.Proof EventT)] [Trace.Invariant.Has (TracePart.Proof EventT)]
  (ev: EventT)
  (tr: ProofTrace)
  : tr.Invariant →
    tr.erase.EventLogged ev →
    ∃ i, EventInv.invariant (tr.prefix i) ev
:= by
  intro h_inv ⟨ i, h_ev ⟩
  exact ⟨ i, DY.Trace.EventLoggedAt_imp_EventInv ev i tr h_inv h_ev ⟩

public
def logEvent
  {EventT: Type}
  [ExecTrace.Def]
  [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT): Traceful Unit
:= do
  let entry: TracePart.Exec EventT := { ev }
  let _i ← appendEntry entry
  return ()

@[instance]
public
theorem logEvent.proof
  {EventT: Type}
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [EventInv EventT]
  [ExecTrace.Has (TracePart.Exec EventT)] [ProofTrace.Has (TracePart.Proof EventT)] [Trace.Invariant.Has (TracePart.Proof EventT)]
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
  step with ⟨ fun _ => TracePart.Exec.mk ev ⟩ by simp_all [ProofTrace.Part.erase, Trace.Invariant.Part.invariant]
  step
  simp only [Trace.EventLogged, Trace.EventLoggedAt]
  exists _i
  have := ProofTrace.Entry.at?_eq_some_erase tr _i (TracePart.Exec.mk ev)
  simp_all [ProofTrace.Part.erase]

public
def label
  {EventT: Type}
  [ExecTrace.Def] [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT)
  : Label
where
  isCorrupt tr := tr.EventLogged ev

public
theorem label_isCorrupt
  {EventT: Type}
  [ExecTrace.Def] [ExecTrace.Has (TracePart.Exec EventT)]
  (ev: EventT) (tr: ExecTrace)
  : (label ev).isCorrupt tr = tr.EventLogged ev
:= by
  rfl

grind_pattern label_isCorrupt => (label ev).isCorrupt tr

end DY.ProtocolEvent
