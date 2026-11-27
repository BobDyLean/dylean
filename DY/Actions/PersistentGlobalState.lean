module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.Network -- for compromise
public import DY.Actions.ProtocolEvent -- for compromise
public import DY.Comparse -- for compromise
import DY.Meta.Step

namespace DY.PersistentGlobalState

section State

section Execution

namespace State

public
structure TracePart.Exec (StateT: Type) where
  st: StateT

public
def TracePart.baseAttackerKnows [Bytes.Def] [ExecTrace.Def] (StateT: Type): Trace.BaseAttackerKnows.Part (TracePart.Exec StateT) where
  attackerKnows _ _ _ := False

end State

public
def storeGlobalState
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace has% State StateT]
  (st: StateT)
  : Traceful Nat
:= do
  let entry: State.TracePart.Exec StateT := { st }
  appendEntry entry

public
def getGlobalState
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace has% State StateT]
  (handle: Nat)
  : Traceful StateT
:= do
  let e: State.TracePart.Exec StateT ← getEntry handle
  return e.st

end Execution

section Proof

public
class GlobalStateInv [ExecTrace.Def] [ProofTrace.Def] (StateT: Type) where
  invariant: StateT → ProofTrace → Prop
  invariant_later: ∀ st tr1 tr2,
    tr1 ≤ tr2 →
    invariant st tr1 →
    invariant st tr2

grind_pattern GlobalStateInv.invariant_later => tr1 ≤ tr2, GlobalStateInv.invariant st tr1
grind_pattern [grind_later] GlobalStateInv.invariant_later => tr1 ≤ tr2, GlobalStateInv.invariant st tr1

namespace State

public
abbrev TracePart.Proof (StateT: Type) := TracePart.Exec StateT

public
instance (StateT: Type): ProofTrace.Part (TracePart.Exec StateT) (TracePart.Proof StateT) := ProofTrace.Part.default (TracePart.Exec StateT)

public
instance (StateT: Type): ExecEntryAssociatedWithProofEntry (TracePart.Exec StateT) (TracePart.Proof StateT) where

public
instance TracePart.invariant
  [ExecTrace.Def] [ProofTrace.Def]
  (StateT: Type)
  [GlobalStateInv StateT]
  : Trace.Invariant.Part (TracePart.Proof StateT)
where
  invariant tr entry :=
    GlobalStateInv.invariant entry.st tr

public
instance
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def] [Bytes.Def] [Bytes.Invariants.Def]
  (StateT: Type)
  [ExecTrace has% State StateT]
  [ProofTrace has% State StateT]
  [GlobalStateInv StateT]
  [Trace.Invariant has% State StateT]
  : Trace.BaseAttackerKnows_implies_Publishable.Part (TracePart.Proof StateT) (TracePart.baseAttackerKnows StateT)
where
  pf trBefore entry b := by
    simp [TracePart.baseAttackerKnows]

end State

@[instance]
public
theorem storeGlobalState.proof
  {StateT: Type}
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [GlobalStateInv StateT]
  [ExecTrace has% State StateT] [ProofTrace has% State StateT] [Trace.Invariant has% State StateT]
  (st: StateT)
  : HoareTriple
    (storeGlobalState st)
    (fun tr => GlobalStateInv.invariant st tr)
    (fun _ _ => True)
:= by
  unfold storeGlobalState
  dsimp only
  step with ⟨ fun _ => State.TracePart.Exec.mk st ⟩ by simp_all [ProofTrace.Part.erase, Trace.Invariant.Part.invariant]
  grind

@[instance]
public
theorem getGlobalState.proof
  {StateT: Type}
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [GlobalStateInv StateT]
  [ExecTrace has% State StateT] [ProofTrace has% State StateT] [Trace.Invariant has% State StateT]
  (handle: Nat)
  : HoareTriple
    (getGlobalState handle: Traceful StateT)
    (fun _ => True)
    (fun st tr => GlobalStateInv.invariant st tr)
:= by
  unfold getGlobalState
  step
  have: GlobalStateInv.invariant e.st tr := by simp_all [ProofTrace.Part.erase, Trace.Invariant.Part.invariant]; grind
  rename_i h; clear h
  step
  grind

end Proof

end State

section Compromise

section Execution

namespace Compromise

public
structure CompromiseEvent (StateT: Type) where
  state: StateT

#combine (StateT: Type) into ExecTrace, Trace.BaseAttackerKnows from ProtocolEvent (CompromiseEvent StateT)

end Compromise

public
def compromise
  (StateT: Type)
  [Bytes.Def] [Bytes.length.Def]
  [Bytes has% Literal] [Bytes.length has% Literal]
  [Bytes has% Concat] [Bytes.length has% Concat]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace.Def]
  [ExecTrace has% Network]
  [ExecTrace has% State StateT]
  [ExecTrace has% Compromise StateT]
  (handle: Nat)
  : Traceful Nat
:= do
  let state: StateT ← getGlobalState handle
  ProtocolEvent.logEvent ({ state }: Compromise.CompromiseEvent StateT)
  Network.sendMessage (Comparse.serialize state)

public
def GlobalStateCompromised
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace has% Compromise StateT]
  (state: StateT)
  (tr: ExecTrace)
  : Prop
:=
  tr.EventLogged ({ state }: Compromise.CompromiseEvent StateT)

public
theorem GlobalStateCompromised_le
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace has% Compromise StateT]
  (state: StateT)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    GlobalStateCompromised state tr1 →
    GlobalStateCompromised state tr2
:= by
  simp [GlobalStateCompromised]
  grind

grind_pattern GlobalStateCompromised_le => tr1 ≤ tr2, GlobalStateCompromised state tr1
grind_pattern [grind_later] GlobalStateCompromised_le => tr1 ≤ tr2, GlobalStateCompromised state tr1

end Execution

section Proof

namespace Compromise

public
instance
  {StateT: Type}
  [ExecTrace.Def] [ProofTrace.Def]
  : ProtocolEvent.EventInv (CompromiseEvent StateT)
where
  invariant _ _ := True

#combine (StateT: Type) into
  ProofTrace,
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from
  ProtocolEvent (Compromise.CompromiseEvent StateT)

end Compromise

public
def label
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace has% Compromise StateT]
  (state: StateT)
:=
  ProtocolEvent.label ({ state }: Compromise.CompromiseEvent StateT)

public
theorem label_isCorrupt
  {StateT: Type}
  [ExecTrace.Def] [ExecTrace has% Compromise StateT]
  (state: StateT)
  (tr: ExecTrace)
  : (label state).isCorrupt tr = GlobalStateCompromised state tr
:= by
  grind [label, GlobalStateCompromised]

grind_pattern label_isCorrupt => (label state).isCorrupt tr

public
class CompromisableGlobalStateInv
  (StateT: Type)
  [ExecTrace.Def] [ProofTrace.Def]
  [Bytes.Def] [Bytes.length.Def]
  [Bytes has% Literal] [Bytes.length has% Literal]
  [Bytes has% Concat] [Bytes.length has% Concat]
  [Bytes.Invariants.Def]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace has% Compromise StateT]
extends
  GlobalStateInv StateT
where
  invariant_implies_KnowableBy:
    ∀ (state: StateT) tr,
      GlobalStateInv.invariant state tr →
      Comparse.IsWellFormed (Bytes.KnowableBy (label state)) state tr

@[instance]
public
theorem compromise.proof
  {StateT: Type}
  [Bytes.Def] [Bytes.length.Def]
  [Bytes has% Literal] [Bytes.length has% Literal]
  [Bytes has% Concat] [Bytes.length has% Concat]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [ExecTrace has% Network]
  [ProofTrace has% Network]
  [ExecTrace has% State StateT]
  [ProofTrace has% State StateT]
  [ExecTrace has% Compromise StateT]
  [ProofTrace has% Compromise StateT]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Comparse.ParseableSerializeable StateT]
  [CompromisableGlobalStateInv StateT]
  [Trace.Invariant has% Network]
  [Trace.Invariant has% State StateT]
  [Trace.Invariant has% Compromise StateT]
  (handle: Nat)
  : HoareTriple
    (compromise StateT handle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold compromise
  step
  step by simp [ProtocolEvent.EventInv.invariant]
  step by
    have := CompromisableGlobalStateInv.invariant_implies_KnowableBy state tr
    have : (label state).isCorrupt tr.erase := by simp_all [label, ProtocolEvent.label_isCorrupt]
    grind [Comparse.IsWellFormed, canFlowTrans]
  grind

end Proof

end Compromise

section CompromisableState

namespace CompromisableState

#combine (StateT: Type) into ExecTrace, Trace.BaseAttackerKnows from
  State StateT,
  Compromise StateT

#combine (StateT: Type) into ProofTrace from
  State StateT,
  Compromise StateT,

#combine
  (StateT: Type)
  [Bytes.Def] [Bytes.Invariants.Def] [Bytes.length.Def]
  [Bytes has% Literal] [Bytes.length has% Literal]
  [Bytes has% Concat] [Bytes.length has% Concat]
  [Comparse.ParseableSerializeable StateT]
  [ExecTrace has% CompromisableState StateT]
  [CompromisableGlobalStateInv StateT]
into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable__noExecHas,
from
  State StateT,
  Compromise StateT,

end CompromisableState

end CompromisableState

end DY.PersistentGlobalState
