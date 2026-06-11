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

namespace DY.Example.ACME

open DY.Comparse

public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [canSign: Signature.CanSign Bytes]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.canSign
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

structure LetsEncryptMessage where
  token: Bytes
  sig: Bytes

structure OwnerMessage where
  address: String
  oPk: Bytes

structure OwnerKeyState where
  oSk: Bytes

structure OwnerAddressState where
  address: String
  oSk: Bytes

structure LetsEncryptPendingChallengeState where
  address: String
  token: Bytes

structure DNSEntry where
  address: String
  sig: Bytes

inductive ACMEEvent where
  | OwnerRegisterAddress (address: String) (oPk: Bytes)
  | LetsEncryptAcceptAddress (address: String) (oPk: Bytes)
deriving DecidableEq

end Structures

-- TODO: this section should be meta-programmable
public section Formats

variable [HasExecBytes]

public
instance: ParseableSerializeable LetsEncryptMessage := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .bytes)
  (fun ⟨ token, sig ⟩ => { token, sig })
  (fun { token, sig } => ⟨ token, sig ⟩)

public
theorem LetsEncryptMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: LetsEncryptMessage) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.token tr ∧
    pre x.sig tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern LetsEncryptMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] LetsEncryptMessage.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable OwnerMessage := .make <|
  .triviallyIsomorphic
  (.prod .slowString .bytes)
  (fun ⟨ address, oPk ⟩ => { address, oPk })
  (fun { address, oPk } => ⟨ address, oPk ⟩)

public
theorem OwnerMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: OwnerMessage) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.oPk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern OwnerMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] OwnerMessage.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable OwnerKeyState := .make <|
  .triviallyIsomorphic
  (.bytes)
  (fun oSk => { oSk := oSk })
  (fun { oSk := oSk } => oSk)

public
theorem OwnerKeyState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: OwnerKeyState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.oSk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern OwnerKeyState.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] OwnerKeyState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeableNE OwnerAddressState := .make <|
  .triviallyIsomorphic
  (.prod .slowString .slowBytes)
  (fun ⟨ address, oSk ⟩ => { address, oSk })
  (fun { address, oSk } => ⟨ address, oSk ⟩)

public
theorem OwnerAddressState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: OwnerAddressState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.oSk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeableNE.mf, Comparse.ParseableSerializeable.mf]

grind_pattern OwnerAddressState.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] OwnerAddressState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeableNE LetsEncryptPendingChallengeState := .make <|
  .triviallyIsomorphic
  (.prod .slowString .slowBytes)
  (fun ⟨ address, token ⟩ => { address, token })
  (fun { address, token } => ⟨ address, token ⟩)

public
theorem LetsEncryptPendingChallengeState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: LetsEncryptPendingChallengeState) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.token tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeableNE.mf, Comparse.ParseableSerializeable.mf]

grind_pattern LetsEncryptPendingChallengeState.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] LetsEncryptPendingChallengeState.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable DNSEntry := .make <|
  .triviallyIsomorphic
  (.prod .slowString .bytes)
  (fun ⟨ address, sig ⟩ => { address, sig })
  (fun { address, sig } => ⟨ address, sig ⟩)

public
theorem DNSEntry.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: DNSEntry) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.sig tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern DNSEntry.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] DNSEntry.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT ACMEEvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OwnerKeyState)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OwnerAddressState)]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT LetsEncryptPendingChallengeState)]
  [traceExec6: ExecTraceTypes.Has (PersistentGlobalState.CompromisableState.ExecEntryT DNSEntry)]
  [traceExec7: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "ACME PKI")]
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
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

instance: LongTermKeys.ExecConfig "ACME PKI" Signature.vk where

def Owner.generateKeyPair (owner: Participant): Traceful (Nat × Nat) := do
  let oSk ← Random.genRand 32
  let oPk := Signature.vk oSk

  let msgHandle ← Network.sendMessage oPk
  let stHandle ← PersistentLocalState.storeLocalState owner ({ oSk }: OwnerKeyState)
  return (msgHandle, stHandle)

def Owner.claimAddress (owner: Participant) (address: String) (oSkHandle: Nat): Traceful Nat := do
  let st: OwnerKeyState ← PersistentLocalState.getLocalState owner oSkHandle
  let oPk := Signature.vk st.oSk
  ProtocolEvent.logEvent (ACMEEvent.OwnerRegisterAddress address oPk)
  let stHandle ← PersistentLocalState.storeLocalState owner ({ address, oSk := st.oSk }: OwnerAddressState)
  return stHandle

def LetsEncrypt.initiate (server: Participant) (address: String) (skHandle: Nat): Traceful (Nat × Nat) := do
  let token ← Random.genRand 32

  let leSk ← LongTermKeys.getPrivateKey "ACME PKI" server skHandle
  let sigNonce ← Random.genRand 32
  let sig := Signature.sign leSk sigNonce token

  let msgHandle ← Network.sendMessage (serialize ({ token, sig } : LetsEncryptMessage))
  let pendingStHandle ← PersistentLocalState.storeLocalState server ({address, token}: LetsEncryptPendingChallengeState)
  return (msgHandle, pendingStHandle)

def Owner.respond (owner server: Participant) (msgHandle lePkHandle stHandle: Nat): Traceful (Nat × Nat) := do
  let lePk ← LongTermKeys.getPublicKey "ACME PKI" server lePkHandle
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: LetsEncryptMessage ← parse msgBytes
  guard (Signature.verify lePk msg.token msg.sig)

  let st: OwnerAddressState ← PersistentLocalState.getLocalState owner stHandle
  let oPk := Signature.vk st.oSk
  let sigNonce ← Random.genRand 32
  let sig := Signature.sign st.oSk sigNonce msg.token

  let dnsEntryHandle ← PersistentGlobalState.storeGlobalState ({ address := st.address, sig }: DNSEntry)
  let msgHandle ← Network.sendMessage (serialize ({address := st.address, oPk}: OwnerMessage))
  return (dnsEntryHandle, msgHandle)

def LetsEncrypt.finish (server: Participant) (msgHandle pendingStHandle dnsEntryHandle: Nat): Traceful Unit := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: OwnerMessage ← parse msgBytes

  let pendingSt: LetsEncryptPendingChallengeState ← PersistentLocalState.getLocalState server pendingStHandle
  let dnsEntry: DNSEntry ← PersistentGlobalState.getGlobalState dnsEntryHandle

  guard (pendingSt.address = dnsEntry.address)
  guard (Signature.verify msg.oPk pendingSt.token dnsEntry.sig)
  ProtocolEvent.logEvent (ACMEEvent.LetsEncryptAcceptAddress dnsEntry.address msg.oPk)
  return ()

def OwnerKeyState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise OwnerKeyState stHandle

def OwnerAddressState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise OwnerAddressState stHandle

def LetsEncryptPendingChallengeState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise LetsEncryptPendingChallengeState stHandle

def DNSEntry.compromise (stHandle: Nat): Traceful Nat := do
  PersistentGlobalState.compromise DNSEntry stHandle

end Specification

public section Reachability

variable [HasExecTrace]

@[expose] public section
def Owner.generateKeyPair.reachability: ReachabilityConfig := .make (fun owner => Owner.generateKeyPair owner)
def Owner.claimAddress.reachability: ReachabilityConfig := .make (fun (owner, address, oSkHandle) => Owner.claimAddress owner address oSkHandle)
def LetsEncrypt.initiate.reachability: ReachabilityConfig := .make (fun (server, address, skHandle) => LetsEncrypt.initiate server address skHandle)
def Owner.respond.reachability: ReachabilityConfig := .make (fun (owner, server, msgHandle, lePkHandle, stHandle) => Owner.respond owner server msgHandle lePkHandle stHandle)
def LetsEncrypt.finish.reachability: ReachabilityConfig := .make (fun (server, msgHandle, pendingStHandle, dnsEntryHandle) => LetsEncrypt.finish server msgHandle pendingStHandle dnsEntryHandle)

def OwnerKeyState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => OwnerKeyState.compromise stHandle)
def OwnerAddressState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => OwnerAddressState.compromise stHandle)
def LetsEncryptPendingChallengeState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => LetsEncryptPendingChallengeState.compromise stHandle)
def DNSEntry.compromise.reachability: ReachabilityConfig := .make (fun stHandle => DNSEntry.compromise stHandle)
end

#combine into ReachabilityConfig from
  Network,
  LongTermKeys "ACME PKI",
  Owner.generateKeyPair,
  Owner.claimAddress,
  LetsEncrypt.initiate,
  Owner.respond,
  LetsEncrypt.finish,
  OwnerKeyState.compromise,
  OwnerAddressState.compromise,
  LetsEncryptPendingChallengeState.compromise,
  DNSEntry.compromise,

end Reachability

end DY.Example.ACME
