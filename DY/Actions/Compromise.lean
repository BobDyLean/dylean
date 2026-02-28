module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.PersistentGlobalState
public import DY.Actions.ProtocolEvent
public import DY.Actions.Network
public import DY.Comparse
import DY.Step

namespace DY.Compromise

public
structure CompromiseEvent (StateT: Type) where
  state: StateT

public
def compromise
  (StateT: Type)
  [BytesFunctor]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has (PersistentGlobalState.ExecEntryT StateT)]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CompromiseEvent StateT))]
  (i: Nat)
  : Traceful Nat
:= do
  let state: StateT ← PersistentGlobalState.getGlobalState i
  ProtocolEvent.logEvent ({ state }: CompromiseEvent StateT)
  Network.sendMessage (Comparse.ParseableSerializeable.serialize state)

public
def GlobalStateCompromised
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CompromiseEvent StateT))]
  (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  tr.EventLogged ({ state }: CompromiseEvent StateT)

public
theorem GlobalStateCompromised_le
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CompromiseEvent StateT))]
  (state: StateT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    GlobalStateCompromised state tr1 →
    GlobalStateCompromised state tr2
:= by
  simp [GlobalStateCompromised]
  grind

grind_pattern GlobalStateCompromised_le => tr1 ≤ tr2, GlobalStateCompromised state tr1

public
def label
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CompromiseEvent StateT))]
  (state: StateT)
:=
  ProtocolEvent.label ({ state }: CompromiseEvent StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CompromiseEvent StateT))]
  (state: StateT)
  (tr: ExecTrace)
  : (label state).isCorrupt tr = GlobalStateCompromised state tr
:= by
  grind [label, GlobalStateCompromised]

grind_pattern label_isCorrupt => (label state).isCorrupt tr

public
class CompromisableStateInv
  (StateT: Type)
  [TraceTypes]
  [BytesFunctor] [BytesInvariants]
  [Comparse.ParseableSerializeable StateT]
  [PersistentGlobalState.GlobalStateInv StateT]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CompromiseEvent StateT))]
where
  invariant_implies_KnowableBy:
    ∀ (state: StateT) tr,
      PersistentGlobalState.GlobalStateInv.invariant state tr →
      Comparse.isWellFormed (Bytes.KnowableBy (label state)) state tr

public
instance
  {StateT: Type}
  [TraceTypes]
  : ProtocolEvent.EventInv (CompromiseEvent StateT)
where
  invariant _ _ := True

@[instance]
public
theorem compromise.spec
  {StateT: Type}
  [TraceInvariant]
  [BytesFunctor] [BytesInvariants] [BytesInvariantsProofs]
  [PersistentGlobalState.GlobalStateInv StateT]
  [Comparse.ParseableSerializeable StateT]
  [TraceTypes.Has Network.ProofEntryFunc] [TraceInvariant.Has Network.Invariant]
  [TraceTypes.Has (PersistentGlobalState.ProofEntryFunc StateT)] [TraceInvariant.Has (PersistentGlobalState.Invariant StateT)]
  [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (CompromiseEvent StateT))] [TraceInvariant.Has (ProtocolEvent.Invariant (CompromiseEvent StateT))]
  [CompromisableStateInv StateT]
  (i: Nat)
  : HoareTriple
    (compromise StateT i)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold compromise
  step
  step by simp [ProtocolEvent.EventInv.invariant]
  step by
    have := CompromisableStateInv.invariant_implies_KnowableBy state tr
    have : (label state).isCorrupt tr.erase := by simp_all [label, ProtocolEvent.label_isCorrupt]
    grind [Comparse.isWellFormed, canFlowTrans]
  trivial

end DY.Compromise
