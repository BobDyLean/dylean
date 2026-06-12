module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Hash
public import Examples.SignedDHKEM.Sign
public import Examples.SignedDHKEM.DiffieHellman
public import Examples.SignedDHKEM.KEM
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Actions.LongTermKeys
public import DY.Comparse

namespace DY.Example.SignedDHKEM

open DY.Comparse

public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has Hash.SubF]
  [bytesFunc4: BytesFunctor.Has Signature'.SubF]
  [bytesFunc5: BytesFunctor.Has DiffieHellman'.SubF]
  [bytesFunc6: BytesFunctor.Has KEM.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has Hash.SubF.length]
  [bytesLen4: BytesLength.Has Signature'.SubF.length]
  [bytesLen5: BytesLength.Has DiffieHellman'.SubF.length]
  [bytesLen6: BytesLength.Has KEM.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has Hash.attackerKnowledge]
  [att4: AttackerKnowledge.Has Signature'.attackerKnowledge]
  [att5: AttackerKnowledge.Has DiffieHellman'.attackerKnowledge]
  [att6: AttackerKnowledge.Has KEM.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.bytesFunc3
attribute [reducible, scoped instance] HasExecBytes.bytesFunc4
attribute [reducible, scoped instance] HasExecBytes.bytesFunc5
attribute [reducible, scoped instance] HasExecBytes.bytesFunc6
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [           scoped instance] HasExecBytes.bytesLen3
attribute [           scoped instance] HasExecBytes.bytesLen4
attribute [           scoped instance] HasExecBytes.bytesLen5
attribute [           scoped instance] HasExecBytes.bytesLen6
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2
attribute [           scoped instance] HasExecBytes.att3
attribute [           scoped instance] HasExecBytes.att4
attribute [           scoped instance] HasExecBytes.att5
attribute [           scoped instance] HasExecBytes.att6

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

structure ClientMessage where
  xPk: Bytes
  zPk: Bytes

structure ServerMessage where
  yPk: Bytes
  ct: Bytes
  sig: Bytes

structure SigInput where
  xPk: Bytes
  yPk: Bytes
  zPk: Bytes
  ct: Bytes

structure ClientInitiateDHState where
  xPk: Bytes -- session identifier
  xSk: Bytes

structure ClientInitiateKEMState where
  zPk: Bytes -- session identifier
  zSk: Bytes

structure ClientFinishState where
  xPk: Bytes -- session identifier
  zPk: Bytes -- session identifier
  kC: Bytes

structure ServerFinishState where
  xPk: Bytes -- session identifier
  yPk: Bytes -- session identifier
  zPk: Bytes -- session identifier
  kS: Bytes

inductive SignedDHKEMEvent where
  | ClientInitiateEvent (client: Participant) (xPk zPk: Bytes)
  | ServerFinishEvent (server: Participant) (xPk yPk zPk: Bytes) (kS: Bytes)
  | ClientFinishEvent (client server: Participant) (xPk: Bytes) (yPk: Bytes) (zPk: Bytes) (kC: Bytes)
deriving DecidableEq

end Structures

public section Formats

variable [HasExecBytes]

public
instance: ParseableSerializeable ClientMessage := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun (xPk, zPk) => { xPk, zPk })
    (fun { xPk, zPk } => (xPk, zPk))

public
theorem ClientMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientMessage) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.zPk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ClientMessage.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ServerMessage := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes (.prod .slowBytes .bytes))
  (fun ⟨ yPk, ct, sig ⟩ => { yPk, ct, sig })
  (fun { yPk, ct, sig } => ⟨ yPk, ct, sig ⟩)

public
theorem ServerMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ServerMessage) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.yPk tr ∧
    pre x.ct tr ∧
    pre x.sig tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ServerMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ServerMessage.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable SigInput := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes (.prod .slowBytes (.prod .slowBytes .bytes)))
  (fun ⟨ xPk, yPk, zPk, ct ⟩ => { xPk, yPk, zPk, ct })
  (fun { xPk, yPk, zPk, ct } => ⟨ xPk, yPk, zPk, ct ⟩)

public
theorem SigInput.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: SigInput) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.yPk tr ∧
    pre x.zPk tr ∧
    pre x.ct tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SigInput.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SigInput.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ClientInitiateDHState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ xPk, xSk ⟩ => { xPk, xSk })
    (fun { xPk, xSk } => ⟨ xPk, xSk ⟩)

public
theorem ClientInitiateDHState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientInitiateDHState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.xSk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientInitiateDHState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ClientInitiateKEMState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ zPk, zSk ⟩ => { zPk, zSk })
    (fun { zPk, zSk } => ⟨ zPk, zSk ⟩)

public
theorem ClientInitiateKEMState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientInitiateKEMState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.zPk tr ∧
    pre x.zSk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientInitiateKEMState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ClientFinishState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes (.prod .slowBytes .bytes))
    (fun ⟨ xPk, zPk, kC ⟩ => { xPk, zPk, kC })
    (fun { xPk, zPk, kC } => ⟨ xPk, zPk, kC ⟩)

public
theorem ClientFinishState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientFinishState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.zPk tr ∧
    pre x.kC tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientFinishState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable ServerFinishState := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes (.prod .slowBytes (.prod .slowBytes .bytes)))
  (fun ⟨ xPk, yPk, zPk, kS ⟩ => { xPk, yPk, zPk, kS })
  (fun { xPk, yPk, zPk, kS } => ⟨ xPk, yPk, zPk, kS ⟩)

public
theorem ServerFinishState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ServerFinishState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.yPk tr ∧
    pre x.zPk tr ∧
    pre x.kS tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ServerFinishState.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHKEMEvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateDHState)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateKEMState)]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
  [traceExec6: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ServerFinishState)]
  [traceExec7: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDHKEM PKI")]
  [traceExec8: ExecTraceTypes.Has (KEM.Broken.ExecEntryT)]
  [traceExec9: ExecTraceTypes.Has (DiffieHellman'.Broken.ExecEntryT)]
  [traceExec10: ExecTraceTypes.Has (Signature'.Broken.ExecEntryT)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.traceExec4
attribute [reducible, scoped instance] HasExecTrace.traceExec5
attribute [reducible, scoped instance] HasExecTrace.traceExec6
attribute [reducible, scoped instance] HasExecTrace.traceExec7
attribute [reducible, scoped instance] HasExecTrace.traceExec8
attribute [reducible, scoped instance] HasExecTrace.traceExec9
attribute [reducible, scoped instance] HasExecTrace.traceExec10
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

instance: LongTermKeys.ExecConfig "SignedDHKEM PKI" Signature'.vk where

def Client.initiate (me: Participant): Traceful (Nat × Nat × Nat) := do
  let xSk ← Random.genRand 32
  let xPk := DiffieHellman'.dh_pk xSk

  let zSk ← Random.genRand 64 -- ML-KEM-512 keypair seed size
  let zPk := KEM.kemPk zSk

  ProtocolEvent.logEvent (SignedDHKEMEvent.ClientInitiateEvent me xPk zPk)
  let dhStHandle ← PersistentLocalState.storeLocalState me ({ xPk, xSk }: ClientInitiateDHState)
  let kemStHandle ← PersistentLocalState.storeLocalState me ({ zPk, zSk }: ClientInitiateKEMState)
  let msgHandle ← Network.sendMessage (serialize ({ xPk, zPk } : ClientMessage))
  return (dhStHandle, kemStHandle, msgHandle)

def Server.receive (me: Participant) (skHandle: Nat) (msgHandle: Nat): Traceful (Nat × Nat) := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: ClientMessage ← parse msgBytes
  let xPk := msg.xPk
  let zPk := msg.zPk
  let sigKey ← LongTermKeys.getPrivateKey "SignedDHKEM PKI" me skHandle

  let ySk ← Random.genRand 32
  let yPk := DiffieHellman'.dh_pk ySk
  let dhss := DiffieHellman'.dh xPk ySk
  let entropy ← Random.genRand 32 -- ML-KEM-512 encapsulation seed size
  let kemResult := KEM.kemEncap zPk entropy
  let (ct, kemss) := kemResult
  let kS := Hash.hash (Concat.concat dhss kemss)

  let sigNonce ← Random.genRand 32
  let sig := Signature'.sign sigKey sigNonce (serialize ({xPk, yPk, zPk, ct}: SigInput))

  ProtocolEvent.logEvent (SignedDHKEMEvent.ServerFinishEvent me xPk yPk zPk kS)
  let stHandle ← PersistentLocalState.storeLocalState me ({ xPk, yPk, zPk, kS }: ServerFinishState)
  let msgHandle ← Network.sendMessage (serialize ({ yPk, ct, sig } : ServerMessage))
  return (stHandle, msgHandle)

def Client.finish (me: Participant) (server: Participant) (pkHandle: Nat) (msgHandle: Nat) (dhStHandle kemStHandle: Nat) : Traceful Nat := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: ServerMessage ← parse msgBytes

  let ({xPk, xSk}: ClientInitiateDHState) ← PersistentLocalState.getLocalState me dhStHandle
  let ({zPk, zSk}: ClientInitiateKEMState) ← PersistentLocalState.getLocalState me kemStHandle

  let serverVk ← LongTermKeys.getPublicKey "SignedDHKEM PKI" server pkHandle

  guard (Signature'.verify serverVk (serialize ({ xPk, yPk := msg.yPk, zPk := zPk, ct := msg.ct}: SigInput)) msg.sig)

  let dhss := DiffieHellman'.dh msg.yPk xSk
  let kemss ← KEM.kemDecap zSk msg.ct
  let kC := Hash.hash (Concat.concat dhss kemss)

  ProtocolEvent.logEvent (SignedDHKEMEvent.ClientFinishEvent me server xPk msg.yPk zPk kC)
  let finalStHandle ← PersistentLocalState.storeLocalState me ({ xPk, zPk, kC }: ClientFinishState)
  return finalStHandle

def ClientInitiateDHState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ClientInitiateDHState stHandle

def ClientInitiateKEMState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ClientInitiateKEMState stHandle

def ClientFinishState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ClientFinishState stHandle

def ServerFinishState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ServerFinishState stHandle

end Specification

public section SecurityPredicates

variable [HasExecTrace]

def ClientEphemeralDHStateCompromised
  (me: Participant) (xPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ xSk, PersistentLocalState.LocalStateCompromised me ({xPk, xSk}: ClientInitiateDHState) tr) ∨
  (∃ kC zPk, PersistentLocalState.LocalStateCompromised me ({xPk, zPk, kC}: ClientFinishState) tr)

theorem ClientEphemeralDHStateCompromised_le
  (me: Participant) (xPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ClientEphemeralDHStateCompromised me xPk tr1 →
    ClientEphemeralDHStateCompromised me xPk tr2
:= by
  simp only [ClientEphemeralDHStateCompromised]
  grind

grind_pattern ClientEphemeralDHStateCompromised_le => tr1 ≤ tr2, ClientEphemeralDHStateCompromised me xPk tr1

def ClientEphemeralKEMStateCompromised
  (me: Participant) (zPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ zSk, PersistentLocalState.LocalStateCompromised me ({zPk, zSk}: ClientInitiateKEMState) tr) ∨
  (∃ kC xPk, PersistentLocalState.LocalStateCompromised me ({xPk, zPk, kC}: ClientFinishState) tr)

theorem ClientEphemeralKEMStateCompromised_le
  (me: Participant) (zPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ClientEphemeralKEMStateCompromised me zPk tr1 →
    ClientEphemeralKEMStateCompromised me zPk tr2
:= by
  simp only [ClientEphemeralKEMStateCompromised]
  grind

grind_pattern ClientEphemeralKEMStateCompromised_le => tr1 ≤ tr2, ClientEphemeralKEMStateCompromised me zPk tr1

def ServerEphemeralStateCompromised
  (me: Participant) (xPk yPk zPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ kS, PersistentLocalState.LocalStateCompromised me ({xPk, yPk, zPk, kS}: ServerFinishState) tr)

theorem ServerEphemeralStateCompromised_le
  (me: Participant) (xPk yPk zPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ServerEphemeralStateCompromised me xPk yPk zPk tr1 →
    ServerEphemeralStateCompromised me xPk yPk zPk tr2
:= by
  simp only [ServerEphemeralStateCompromised]
  grind

grind_pattern ServerEphemeralStateCompromised_le => tr1 ≤ tr2, ServerEphemeralStateCompromised me xPk yPk zPk tr1

end SecurityPredicates

public section Reachability

variable [HasExecTrace]

@[expose] public section
def Client.initiate.reachability: ReachabilityConfig := .make (fun me => Client.initiate me)
def Server.receive.reachability: ReachabilityConfig := .make (fun (me, skHandle, msgHandle) => Server.receive me skHandle msgHandle)
def Client.finish.reachability: ReachabilityConfig := .make (fun (me, server, pkHandle, msgHandle, dhStHandle, kemStHandle) => Client.finish me server pkHandle msgHandle dhStHandle kemStHandle)
def ClientInitiateDHState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ClientInitiateDHState.compromise stHandle)
def ClientInitiateKEMState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ClientInitiateKEMState.compromise stHandle)
def ServerFinishState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ServerFinishState.compromise stHandle)
def ClientFinishState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ClientFinishState.compromise stHandle)
end

#combine into ReachabilityConfig from
  Network,
  LongTermKeys "SignedDHKEM PKI",
  Client.initiate,
  Server.receive,
  Client.finish,
  ClientInitiateDHState.compromise,
  ClientInitiateKEMState.compromise,
  ClientFinishState.compromise,
  ServerFinishState.compromise,
  KEM.Broken.breakKemPk,
  DiffieHellman'.Broken.breakDhPk,
  Signature'.Broken.breakVk,

end Reachability

end DY.Example.SignedDHKEM
