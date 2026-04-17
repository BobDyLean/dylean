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

-- TODO: most of this section should be meta-programmable from the SubF.internal list
public section ExecBytesConfig

abbrev SubF.internal: (id: Fin 6) → (Type → Type)
  | 0 => Literal.SubF
  | 1 => Concat.SubF
  | 2 => Hash.SubF
  | 3 => Signature.SubF
  | 4 => DiffieHellman.SubF
  | 5 => Random.SubF

abbrev SubF := BytesFunctor.combine SubF.internal

instance: ∀ id, SubBytesFunctor (SubF.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 => inferInstance

instance: BytesFunctor.HasStep Literal.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 0) SubF)
instance: BytesFunctor.HasStep Concat.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 1) SubF)
instance: BytesFunctor.HasStep Hash.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 2) SubF)
instance: BytesFunctor.HasStep Signature.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 3) SubF)
instance: BytesFunctor.HasStep DiffieHellman.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 4) SubF)
instance: BytesFunctor.HasStep Random.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 5) SubF)

instance: BytesFunctor where
  BytesF := SubF

instance: BytesFunctor.Has SubF := inferInstanceAs (BytesFunctor.Has BytesF)

example: BytesFunctor.Has Hash.SubF := inferInstance
example: BytesFunctor.Has Signature.SubF := inferInstance
example: BytesFunctor.Has DiffieHellman.SubF := inferInstance
example: BytesFunctor.Has Random.SubF := inferInstance

def SubF.length.internal [BytesFunctor]: ∀ id, Bytes.PartialLength (SubF.internal id)
  | 0 => Literal.SubF.length
  | 1 => Concat.SubF.length
  | 2 => Hash.SubF.length
  | 3 => Signature.SubF.length
  | 4 => DiffieHellman.SubF.length
  | 5 => Random.SubF.length

abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  Bytes.PartialLength.combine SubF.length.internal

instance: BytesLength where
  funs := SubF.length

instance: BytesLength.HasStep Literal.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 0) SubF.length)
instance: BytesLength.HasStep Concat.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 1) SubF.length)
instance: BytesLength.HasStep Hash.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 2) SubF.length)
instance: BytesLength.HasStep Signature.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 3) SubF.length)
instance: BytesLength.HasStep DiffieHellman.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 4) SubF.length)
instance: BytesLength.HasStep Random.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 5) SubF.length)

instance: BytesLength.Has SubF.length := inferInstanceAs (BytesLength.Has SubF.length)

example: BytesLength.Has Literal.SubF.length := inferInstance
example: BytesLength.Has Concat.SubF.length := inferInstance
example: BytesLength.Has Hash.SubF.length := inferInstance
example: BytesLength.Has Signature.SubF.length := inferInstance
example: BytesLength.Has DiffieHellman.SubF.length := inferInstance
example: BytesLength.Has Random.SubF.length := inferInstance

def attackerKnowledge.internal (id: Fin 6): SubAttackerKnowledge (SubF.internal id) :=
  match id with
  | 0 => Literal.attackerKnowledge
  | 1 => Concat.attackerKnowledge
  | 2 => Hash.attackerKnowledge
  | 3 => Signature.attackerKnowledge
  | 4 => DiffieHellman.attackerKnowledge
  | 5 => Random.attackerKnowledge

def attackerKnowledge: SubAttackerKnowledge SubF :=
  SubAttackerKnowledge.combine attackerKnowledge.internal

instance: AttackerKnowledge.HasStep Literal.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Concat.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Hash.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 2) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Signature.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 3) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep DiffieHellman.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 4) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Random.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 5) (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledge where
  attackerKnowledge

instance: AttackerKnowledge.Has attackerKnowledge := inferInstanceAs (AttackerKnowledge.Has AttackerKnowledge.attackerKnowledge)

example: AttackerKnowledge.Has Hash.attackerKnowledge := inferInstance
example: AttackerKnowledge.Has Signature.attackerKnowledge := inferInstance
example: AttackerKnowledge.Has DiffieHellman.attackerKnowledge := inferInstance
example: AttackerKnowledge.Has Random.attackerKnowledge := inferInstance

end ExecBytesConfig

public section Structures

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

-- TODO: most of this section should be meta-programmable from the ExecEntryT.internal list
public section ExecTraceConfig

public
abbrev ExecEntryT.internal: Fin 7 → Type
  | 0 => Network.ExecEntryT
  | 1 => Random.ExecEntryT
  | 2 => ProtocolEvent.ExecEntryT SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ServerFinishState
  | 6 => LongTermKeys.ExecEntryT "SignedDH"

public
abbrev ExecEntryT: Type :=
  ExecTraceTypes.combine ExecEntryT.internal

instance: ExecTraceTypes.HasStep Network.ExecEntryT ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 0) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep Random.ExecEntryT ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 1) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (ProtocolEvent.ExecEntryT SignedDH.SignedDHEvent) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 2) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientInitiateState) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 3) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientFinishState) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 4) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ServerFinishState) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 5) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (LongTermKeys.ExecEntryT "SignedDH") ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 6) (ExecTraceTypes.combine ExecEntryT.internal))

instance: ExecTraceTypes where
  ExecT := ExecEntryT

instance: ExecTraceTypes.Has ExecEntryT := inferInstanceAs (ExecTraceTypes.Has ExecTrace.Entry)

example: ExecTraceTypes.Has Network.ExecEntryT := inferInstance
example: ExecTraceTypes.Has Random.ExecEntryT := inferInstance
example: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDH.SignedDHEvent) := inferInstance
example: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientInitiateState) := inferInstance
example: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientFinishState) := inferInstance
example: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ServerFinishState) := inferInstance
example: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDH") := inferInstance

public
def baseAttackerKnowledge.internal: (id: Fin 7) → SubBaseAttackerKnowledge (ExecEntryT.internal id)
  | 0 => Network.baseAttackerKnowledge
  | 1 => Random.baseAttackerKnowledge
  | 2 => ProtocolEvent.baseAttackerKnowledge SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.baseAttackerKnowledge SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.baseAttackerKnowledge SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.baseAttackerKnowledge SignedDH.ServerFinishState
  | 6 => LongTermKeys.baseAttackerKnowledge "SignedDH"

public
def baseAttackerKnowledge: SubBaseAttackerKnowledge ExecEntryT :=
  SubBaseAttackerKnowledge.combine baseAttackerKnowledge.internal

instance: BaseAttackerKnowledge where
  attackerKnows := baseAttackerKnowledge

end ExecTraceConfig

public section Specification

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
