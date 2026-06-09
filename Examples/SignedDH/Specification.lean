module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.Sign
public import DY.EquationalTheory.DiffieHellman
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Actions.LongTermKeys
public import DY.Comparse

namespace DY.Example.SignedDH

open DY.Comparse

-- TODO: meta-program could divide this section length by 6 (=2*3)
public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has Hash.SubF]
  [bytesFunc4: BytesFunctor.Has Signature.SubF]
  [bytesFunc5: BytesFunctor.Has DiffieHellman.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has Hash.SubF.length]
  [bytesLen4: BytesLength.Has Signature.SubF.length]
  [bytesLen5: BytesLength.Has DiffieHellman.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has Hash.attackerKnowledge]
  [att4: AttackerKnowledge.Has Signature.attackerKnowledge]
  [att5: AttackerKnowledge.Has DiffieHellman.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.bytesFunc3
attribute [reducible, scoped instance] HasExecBytes.bytesFunc4
attribute [reducible, scoped instance] HasExecBytes.bytesFunc5
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [           scoped instance] HasExecBytes.bytesLen3
attribute [           scoped instance] HasExecBytes.bytesLen4
attribute [           scoped instance] HasExecBytes.bytesLen5
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2
attribute [           scoped instance] HasExecBytes.att3
attribute [           scoped instance] HasExecBytes.att4
attribute [           scoped instance] HasExecBytes.att5

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

structure ClientMessage where
  xPk: Bytes

structure ServerMessage where
  yPk: Bytes
  sig: Bytes

structure SigInput where
  xPk: Bytes
  yPk: Bytes

structure ClientInitiateState where
  xPk: Bytes
  xSk: Bytes

structure ClientFinishState where
  xPk: Bytes
  kC: Bytes

structure ServerFinishState where
  yPk: Bytes
  kS: Bytes

inductive SignedDHEvent where
  | ClientInitiateEvent (client: Participant) (xPk: Bytes)
  | ServerFinishEvent (server: Participant) (xPk: Bytes) (yPk: Bytes) (kS: Bytes)
  | ClientFinishEvent (client server: Participant) (xPk: Bytes) (yPk: Bytes) (kC: Bytes)
deriving DecidableEq

end Structures

-- TODO: this section should be meta-programmable
public section Formats

variable [HasExecBytes]

public
instance: ParseableSerializeable ClientMessage := .make <|
  .triviallyIsomorphic
    (.bytes)
    (fun xPk => { xPk })
    (fun { xPk := xPk } => xPk)

public
theorem ClientMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientMessage) (tr: τ):
  IsWellFormed pre x tr = pre x.xPk tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ClientMessage.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ServerMessage := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ yPk, sig ⟩ => { yPk, sig })
  (fun { yPk, sig } => ⟨ yPk, sig ⟩)

public
theorem ServerMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ServerMessage) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.yPk tr ∧
    pre x.sig tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ServerMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ServerMessage.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable SigInput := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ xPk, yPk ⟩ => { xPk, yPk })
  (fun { xPk, yPk } => ⟨ xPk, yPk ⟩)

public
theorem SigInput.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: SigInput) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.yPk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SigInput.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SigInput.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ClientInitiateState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ xPk, xSk ⟩ => { xPk, xSk })
    (fun { xPk, xSk } => ⟨ xPk, xSk ⟩)

public
theorem ClientInitiateState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientInitiateState) (tr: τ):
  IsWellFormed pre x tr = (pre x.xPk tr ∧ pre x.xSk tr)
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientInitiateState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ClientFinishState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ xPk, kC ⟩ => { xPk, kC })
    (fun { xPk, kC } => ⟨ xPk, kC ⟩)

public
theorem ClientFinishState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientFinishState) (tr: τ):
  IsWellFormed pre x tr = (pre x.xPk tr ∧ pre x.kC tr)
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientFinishState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ServerFinishState := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ yPk, kS ⟩ => { yPk, kS })
  (fun { yPk, kS } => ⟨ yPk, kS ⟩)

public
theorem ServerFinishState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ServerFinishState) (tr: τ):
  IsWellFormed pre x tr = (pre x.yPk tr ∧ pre x.kS tr)
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ServerFinishState.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

-- TODO: a meta-program could divide this section length by 2
public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDH.SignedDHEvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientInitiateState)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientFinishState)]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ServerFinishState)]
  [traceExec6: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDH PKI")]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.traceExec4
attribute [reducible, scoped instance] HasExecTrace.traceExec5
attribute [reducible, scoped instance] HasExecTrace.traceExec6
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

instance: LongTermKeys.ExecConfig "SignedDH PKI" Signature.vk where

def Client.initiate (me: Participant): Traceful (Nat × Nat) := do
  let xSk ← Random.genRand 32
  let xPk := DiffieHellman.dh_pk xSk

  ProtocolEvent.logEvent (SignedDHEvent.ClientInitiateEvent me xPk)
  let stHandle ← PersistentLocalState.storeLocalState me ({ xPk, xSk }: ClientInitiateState)
  let msgHandle ← Network.sendMessage (serialize ({ xPk } : ClientMessage))
  return (stHandle, msgHandle)

def Server.receive (me: Participant) (skHandle: Nat) (msgHandle: Nat): Traceful (Nat × Nat) := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: ClientMessage ← parse msgBytes
  let xPk := msg.xPk
  let serverSigKey ← LongTermKeys.getPrivateKey "SignedDH PKI" me skHandle

  let ySk ← Random.genRand 32
  let yPk := DiffieHellman.dh_pk ySk
  let kS := Hash.hash (DiffieHellman.dh xPk ySk)
  let sigNonce ← Random.genRand 32
  let sig := Signature.sign serverSigKey sigNonce (serialize ({xPk, yPk}: SigInput))

  ProtocolEvent.logEvent (SignedDHEvent.ServerFinishEvent me xPk yPk kS)
  let stHandle ← PersistentLocalState.storeLocalState me ({ yPk, kS }: ServerFinishState)
  let msgHandle ← Network.sendMessage (serialize ({ yPk, sig } : ServerMessage))
  return (stHandle, msgHandle)

def Client.finish (me: Participant) (server: Participant) (pkHandle: Nat) (msgHandle: Nat) (stHandle: Nat) : Traceful Nat := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: ServerMessage ← parse msgBytes

  let ({xPk, xSk}: ClientInitiateState) ← PersistentLocalState.getLocalState me stHandle
  let serverVk ← LongTermKeys.getPublicKey "SignedDH PKI" server pkHandle

  guard (Signature.verify serverVk (serialize ({ xPk, yPk := msg.yPk }: SigInput)) msg.sig)
  let kC := Hash.hash (DiffieHellman.dh msg.yPk xSk)

  ProtocolEvent.logEvent (SignedDHEvent.ClientFinishEvent me server xPk msg.yPk kC)
  let finalStHandle ← PersistentLocalState.storeLocalState me ({ xPk, kC }: ClientFinishState)
  return finalStHandle

def ClientInitiateState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ClientInitiateState stHandle

def ClientFinishState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ClientFinishState stHandle

def ServerFinishState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ServerFinishState stHandle

end Specification

public section SecurityPredicates

variable [HasExecTrace]

def ClientEphemeralStateCompromised
  (me: Participant) (xPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ xSk, PersistentLocalState.LocalStateCompromised me ({xPk, xSk}: ClientInitiateState) tr) ∨
  (∃ kC, PersistentLocalState.LocalStateCompromised me ({xPk, kC}: ClientFinishState) tr)

theorem ClientEphemeralStateCompromised_le
  (me: Participant) (xPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ClientEphemeralStateCompromised me xPk tr1 →
    ClientEphemeralStateCompromised me xPk tr2
:= by
  simp only [ClientEphemeralStateCompromised]
  grind

grind_pattern ClientEphemeralStateCompromised_le => tr1 ≤ tr2, ClientEphemeralStateCompromised me xPk tr1

def ServerEphemeralStateCompromised
  (me: Participant) (yPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ kS, PersistentLocalState.LocalStateCompromised me ({yPk, kS}: ServerFinishState) tr)

theorem ServerEphemeralStateCompromised_le
  (me: Participant) (yPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ServerEphemeralStateCompromised me yPk tr1 →
    ServerEphemeralStateCompromised me yPk tr2
:= by
  simp only [ServerEphemeralStateCompromised]
  grind

grind_pattern ServerEphemeralStateCompromised_le => tr1 ≤ tr2, ServerEphemeralStateCompromised me yPk tr1

end SecurityPredicates

public section Reachability

variable [HasExecTrace]

@[expose] public section
def Client.initiate.reachability: ReachabilityConfig := .make (fun me => Client.initiate me)
def Server.receive.reachability: ReachabilityConfig := .make (fun (me, skHandle, msgHandle) => Server.receive me skHandle msgHandle)
def Client.finish.reachability: ReachabilityConfig := .make (fun (me, server, pkHandle, msgHandle, stHandle) => Client.finish me server pkHandle msgHandle stHandle)
def ClientInitiateState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ClientInitiateState.compromise stHandle)
def ServerFinishState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ServerFinishState.compromise stHandle)
def ClientFinishState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ClientFinishState.compromise stHandle)
end

#combine into ReachabilityConfig from
  Network,
  LongTermKeys "SignedDH PKI",
  Client.initiate,
  Server.receive,
  Client.finish,
  ClientInitiateState.compromise,
  ClientFinishState.compromise,
  ServerFinishState.compromise,

end Reachability

end DY.Example.SignedDH
