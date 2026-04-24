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
  [bytesFunc0: BytesFunctor.Has Literal.SubF]
  [bytesFunc1: BytesFunctor.Has Concat.SubF]
  [bytesFunc2: BytesFunctor.Has Hash.SubF]
  [bytesFunc3: BytesFunctor.Has Signature.SubF]
  [bytesFunc4: BytesFunctor.Has DiffieHellman.SubF]
  [bytesFunc5: BytesFunctor.Has Random.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Literal.SubF.length]
  [bytesLen1: BytesLength.Has Concat.SubF.length]
  [bytesLen2: BytesLength.Has Hash.SubF.length]
  [bytesLen3: BytesLength.Has Signature.SubF.length]
  [bytesLen4: BytesLength.Has DiffieHellman.SubF.length]
  [bytesLen5: BytesLength.Has Random.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att1: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att2: AttackerKnowledge.Has Hash.attackerKnowledge]
  [att3: AttackerKnowledge.Has Signature.attackerKnowledge]
  [att4: AttackerKnowledge.Has DiffieHellman.attackerKnowledge]
  [att5: AttackerKnowledge.Has Random.attackerKnowledge]

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

instance: ParseableSerializeable ClientMessage := .make <|
  .triviallyIsomorphic
    (.bytes)
    (fun xPk => { xPk })
    (fun { xPk := xPk } => xPk)

theorem ClientMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientMessage) (tr: τ):
  IsWellFormed pre x tr = pre x.xPk tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ClientMessage.IsWellFormed_eq => IsWellFormed pre x tr

instance: ParseableSerializeable ServerMessage := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ yPk, sig ⟩ => { yPk, sig })
  (fun { yPk, sig } => ⟨ yPk, sig ⟩)

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

instance: ParseableSerializeable SigInput := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ xPk, yPk ⟩ => { xPk, yPk })
  (fun { xPk, yPk } => ⟨ xPk, yPk ⟩)

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

instance: ParseableSerializeable ClientInitiateState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ xPk, xSk ⟩ => { xPk, xSk })
    (fun { xPk, xSk } => ⟨ xPk, xSk ⟩)

theorem ClientInitiateState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientInitiateState) (tr: τ):
  IsWellFormed pre x tr = (pre x.xPk tr ∧ pre x.xSk tr)
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientInitiateState.IsWellFormed_eq => IsWellFormed pre x tr

instance: ParseableSerializeable ClientFinishState := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ xPk, kC ⟩ => { xPk, kC })
    (fun { xPk, kC } => ⟨ xPk, kC ⟩)

theorem ClientFinishState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ClientFinishState) (tr: τ):
  IsWellFormed pre x tr = (pre x.xPk tr ∧ pre x.kC tr)
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern ClientFinishState.IsWellFormed_eq => IsWellFormed pre x tr

instance: ParseableSerializeable ServerFinishState := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ yPk, kS ⟩ => { yPk, kS })
  (fun { yPk, kS } => ⟨ yPk, kS ⟩)

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
  [traceExec6: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDH")]
  [attBase: BaseAttackerKnowledge]
  -- no has :thinking_face:

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

instance: LongTermKeys.ExecConfig "SignedDH" Signature.vk where

def client_initiate (me: Participant): Traceful (Nat × Nat) := do
  let xSk ← Random.genRand 32
  let xPk := DiffieHellman.dh_pk xSk

  ProtocolEvent.logEvent (SignedDHEvent.ClientInitiateEvent me xPk)
  let st_ts ← PersistentLocalState.storeLocalState me ({ xPk, xSk }: ClientInitiateState)
  let msg_ts ← Network.sendMessage (serialize ({ xPk } : ClientMessage))
  pure (st_ts, msg_ts)

def server_receive (me: Participant) (sk_ts: Nat) (msg_ts: Nat): Traceful (Nat × Nat) := do
  let msg_bytes ← Network.receiveMessage msg_ts
  let msg: ClientMessage ← parse msg_bytes
  let xPk := msg.xPk
  let my_sig_key ← LongTermKeys.getPrivateKey "SignedDH" me sk_ts

  let ySk ← Random.genRand 32
  let yPk := DiffieHellman.dh_pk ySk
  let kS := Hash.hash (DiffieHellman.dh xPk ySk)
  let sig_nonce ← Random.genRand 32
  let sig := Signature.sign my_sig_key sig_nonce (serialize ({xPk, yPk}: SigInput))

  ProtocolEvent.logEvent (SignedDHEvent.ServerFinishEvent me xPk yPk kS)
  let st_ts ← PersistentLocalState.storeLocalState me ({ yPk, kS }: ServerFinishState)
  let msg_ts ← Network.sendMessage (serialize ({ yPk, sig } : ServerMessage))
  pure (st_ts, msg_ts)

def client_finish (me: Participant) (server: Participant) (pk_ts: Nat) (msg_ts: Nat) (sid: Nat) : Traceful Unit := do
  let msg_bytes ← Network.receiveMessage msg_ts
  let msg: ServerMessage ← parse msg_bytes

  let ({xPk, xSk}: ClientInitiateState) ← PersistentLocalState.getLocalState me sid
  let server_vk ← LongTermKeys.getPublicKey "SignedDH" server pk_ts

  guard (Signature.verify server_vk (serialize ({ xPk, yPk := msg.yPk }: SigInput)) msg.sig)
  let kC := Hash.hash (DiffieHellman.dh msg.yPk xSk)

  ProtocolEvent.logEvent (SignedDHEvent.ClientFinishEvent me server xPk msg.yPk kC)
  let _ ← PersistentLocalState.storeLocalState me ({ xPk, kC }: ClientFinishState)

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

@[expose]
def reachability.internal: Fin 5 → ReachabilityConfig
  | 0 => Network.reachability
  | 1 => LongTermKeys.reachability "SignedDH"
  | 2 => .make (fun me => client_initiate me)
  | 3 => .make (fun (me, sk_ts, msg_ts) => server_receive me sk_ts msg_ts)
  | 4 => .make (fun (me, server, pk_ts, msg_ts, sid) => client_finish me server pk_ts msg_ts sid)

@[expose]
def reachability: ReachabilityConfig := .combine reachability.internal

instance: ReachabilityConfig.HasStep (Network.reachability) reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 0) (.combine reachability.internal)
instance: ReachabilityConfig.HasStep (LongTermKeys.reachability "SignedDH") reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 1) (.combine reachability.internal)
instance: ReachabilityConfig.HasStep (.make (fun me => client_initiate me)) reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 2) (.combine reachability.internal)
instance: ReachabilityConfig.HasStep (.make (fun (me, sk_ts, msg_ts) => server_receive me sk_ts msg_ts)) reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 3) (.combine reachability.internal)
instance: ReachabilityConfig.HasStep (.make (fun (me, server, pk_ts, msg_ts, sid) => client_finish me server pk_ts msg_ts sid)) reachability := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal 4) (.combine reachability.internal)

end Reachability

end DY.Example.SignedDH
