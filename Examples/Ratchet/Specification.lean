module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.Sign
public import DY.EquationalTheory.DiffieHellman
public import DY.EquationalTheory.KdfExtract
public import DY.EquationalTheory.KdfExpand
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Actions.LongTermKeys
public import DY.Comparse

namespace DY.Example.Ratchet

open DY.Comparse

-- Future work: the following section is boilerplate that could be meta-programmed
public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has Hash.SubF]
  [bytesFunc4: BytesFunctor.Has Signature.SubF]
  [bytesFunc5: BytesFunctor.Has DiffieHellman.SubF]
  [bytesFunc6: BytesFunctor.Has KdfExtract.SubF]
  [bytesFunc7: BytesFunctor.Has KdfExpand.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has Hash.SubF.length]
  [bytesLen4: BytesLength.Has Signature.SubF.length]
  [bytesLen5: BytesLength.Has DiffieHellman.SubF.length]
  [bytesLen6: BytesLength.Has KdfExtract.SubF.length]
  [bytesLen7: BytesLength.Has KdfExpand.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has Hash.attackerKnowledge]
  [att4: AttackerKnowledge.Has Signature.attackerKnowledge]
  [att5: AttackerKnowledge.Has DiffieHellman.attackerKnowledge]
  [att6: AttackerKnowledge.Has KdfExtract.attackerKnowledge]
  [att7: AttackerKnowledge.Has KdfExpand.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.bytesFunc3
attribute [reducible, scoped instance] HasExecBytes.bytesFunc4
attribute [reducible, scoped instance] HasExecBytes.bytesFunc5
attribute [reducible, scoped instance] HasExecBytes.bytesFunc6
attribute [reducible, scoped instance] HasExecBytes.bytesFunc7
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [           scoped instance] HasExecBytes.bytesLen3
attribute [           scoped instance] HasExecBytes.bytesLen4
attribute [           scoped instance] HasExecBytes.bytesLen5
attribute [           scoped instance] HasExecBytes.bytesLen6
attribute [           scoped instance] HasExecBytes.bytesLen7
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2
attribute [           scoped instance] HasExecBytes.att3
attribute [           scoped instance] HasExecBytes.att4
attribute [           scoped instance] HasExecBytes.att5
attribute [           scoped instance] HasExecBytes.att6
attribute [           scoped instance] HasExecBytes.att7

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

structure Message where
  dhPk: Bytes
  sig: Bytes

structure TranscriptElement where
  recipient: Participant
  dhPk: Bytes
deriving DecidableEq

abbrev Transcript := List TranscriptElement

structure TranscriptHashInput where
  elem: TranscriptElement
  previousTranscriptHash: Bytes

structure SigInput where
  transcriptHash: Bytes

structure StateMyTurn where
  transcript: Transcript -- session identifier
  recipient: Participant
  transcriptHash: Bytes
  otherDhPk: Bytes
  k: Bytes

structure StateOtherTurn where
  transcript: Transcript -- session identifier
  recipient: Participant
  transcriptHash: Bytes
  myDhSk: Bytes
  k: Bytes

inductive RatchetEvent where
  | SendUpdate (me other: Participant) (transcript: Transcript) (k: Bytes)
  | ReceiveUpdate (me other: Participant) (transcript: Transcript) (k: Bytes)
deriving DecidableEq

end Structures

-- Future work: the following section is boilerplate that could be meta-programmed
public section Formats

variable [HasExecBytes]

public
instance: ParseableSerializeable Message := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun (dhPk, sig) => { dhPk, sig })
    (fun { dhPk, sig } => (dhPk, sig))

public
theorem Message.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: Message) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.dhPk tr ∧
    pre x.sig tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern Message.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] Message.IsWellFormed_eq => IsWellFormed pre x tr

public
instance TranscriptElement.ps: ParseableSerializeableNE TranscriptElement := .make <|
  .triviallyIsomorphic
  (.prod .slowString .slowBytes)
  (fun ⟨ recipient, dhPk ⟩ => { recipient, dhPk })
  (fun { recipient, dhPk } => ⟨ recipient, dhPk ⟩)

instance: TranscriptElement.ps.mf.ParseConsumes := by
  dsimp only [ParseableSerializeableNE.mf]
  infer_instance

public
theorem TranscriptElement.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: TranscriptElement) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.dhPk tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf]

grind_pattern TranscriptElement.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] TranscriptElement.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable TranscriptHashInput := .make <|
  .triviallyIsomorphic
  (.prod TranscriptElement.ps.mf .bytes)
  (fun ⟨ elem, previousTranscriptHash ⟩ => { elem, previousTranscriptHash })
  (fun { elem, previousTranscriptHash } => ⟨ elem, previousTranscriptHash ⟩)

public
theorem TranscriptHashInput.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: TranscriptHashInput) (tr: τ):
  IsWellFormed pre x tr = (
    IsWellFormed pre x.elem tr ∧
    pre x.previousTranscriptHash tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern TranscriptHashInput.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] TranscriptHashInput.IsWellFormed_eq => IsWellFormed pre x tr


public
instance: ParseableSerializeable SigInput := .make <|
  .triviallyIsomorphic
  (.bytes)
  (fun transcriptHash => { transcriptHash := transcriptHash })
  (fun { transcriptHash := transcriptHash } => transcriptHash)

public
theorem SigInput.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: SigInput) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.transcriptHash tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SigInput.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SigInput.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable StateMyTurn := .make <|
  .triviallyIsomorphic
    (.prod .slowString (.prod .slowBytes (.prod .slowBytes (.prod .slowBytes (.list TranscriptElement.ps.mf)))))
    (fun ⟨ recipient, transcriptHash, otherDhPk, k, transcript ⟩ => { recipient, transcriptHash, otherDhPk, k, transcript })
    (fun { recipient, transcriptHash, otherDhPk, k, transcript } => ⟨ recipient, transcriptHash, otherDhPk, k, transcript ⟩)

public
theorem StateMyTurn.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: StateMyTurn) (tr: τ):
  IsWellFormed pre x tr = (
    (∀ elem ∈ x.transcript, IsWellFormed pre elem tr) ∧
    pre x.transcriptHash tr ∧
    pre x.otherDhPk tr ∧
    pre x.k tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]
  grind

grind_pattern StateMyTurn.IsWellFormed_eq => IsWellFormed pre x tr

public
instance: ParseableSerializeable StateOtherTurn := .make <|
  .triviallyIsomorphic
    (.prod .slowString (.prod .slowBytes (.prod .slowBytes (.prod .slowBytes (.list TranscriptElement.ps.mf)))))
    (fun ⟨ recipient, transcriptHash, myDhSk, k, transcript ⟩ => { recipient, transcriptHash, myDhSk, k, transcript })
    (fun { recipient, transcriptHash, myDhSk, k, transcript } => ⟨ recipient, transcriptHash, myDhSk, k, transcript ⟩)

public
theorem StateOtherTurn.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: StateOtherTurn) (tr: τ):
  IsWellFormed pre x tr = (
    (∀ elem ∈ x.transcript, IsWellFormed pre elem tr) ∧
    pre x.transcriptHash tr ∧
    pre x.myDhSk tr ∧
    pre x.k tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]
  grind

grind_pattern StateOtherTurn.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

-- Future work: the following section is boilerplate that could be meta-programmed
public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT RatchetEvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT StateMyTurn)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT StateOtherTurn)]
  [traceExec5: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "Ratchet PKI")]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.traceExec4
attribute [reducible, scoped instance] HasExecTrace.traceExec5
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

def initialTranscriptHash: Bytes :=
  Comparse.BytesLike.empty

def computeTranscriptHash (previousTranscriptHash: Bytes) (elem: TranscriptElement): Bytes :=
  let input: TranscriptHashInput := { previousTranscriptHash, elem }
  Hash.hash (Comparse.serialize input)

def firstKey: Bytes :=
  Literal.literalToBytes "00000000000000000000000000000000".toByteArray

instance: LongTermKeys.ExecConfig "Ratchet PKI" Signature.vk where

def initiate (me other: Participant) (mySigKeyHandle: Nat): Traceful (Nat × Nat) := do
  let dhSk ← Random.genRand 32
  let dhPk := DiffieHellman.dhPk dhSk

  let transcriptElement: TranscriptElement := { recipient := other, dhPk }
  let transcript := [transcriptElement]
  let transcriptHash := computeTranscriptHash initialTranscriptHash transcriptElement

  let sigKey ← LongTermKeys.getPrivateKey "Ratchet PKI" me mySigKeyHandle
  let sigNonce ← Random.genRand 32
  let sig := Signature.sign sigKey sigNonce (Comparse.serialize ({transcriptHash}: SigInput))
  let k := firstKey
  let st: StateOtherTurn := { transcript, recipient := other, transcriptHash, myDhSk := dhSk, k }

  ProtocolEvent.logEvent (RatchetEvent.SendUpdate me other transcript k)
  let stHandle ← PersistentLocalState.storeLocalState me st
  let msgHandle ← Network.sendMessage (serialize ({ dhPk, sig } : Message))
  return (stHandle, msgHandle)

def processInitiate (me other: Participant) (otherVerifKeyHandle: Nat) (msgHandle: Nat): Traceful Nat := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: Message ← Comparse.parse msgBytes

  let transcriptElement: TranscriptElement := { recipient := me, dhPk := msg.dhPk }
  let transcript := [transcriptElement]
  let transcriptHash := computeTranscriptHash initialTranscriptHash transcriptElement

  let verifKey ← LongTermKeys.getPublicKey "Ratchet PKI" other otherVerifKeyHandle
  guard (Signature.verify verifKey (Comparse.serialize ({transcriptHash}: SigInput)) msg.sig)
  let k := firstKey

  ProtocolEvent.logEvent (RatchetEvent.ReceiveUpdate me other transcript k)
  let st: StateMyTurn := { transcript, recipient := other, transcriptHash, otherDhPk := msg.dhPk, k }
  let stHandle ← PersistentLocalState.storeLocalState me st
  return stHandle

def sendUpdate (me: Participant) (mySigKeyHandle: Nat) (stHandle: Nat): Traceful (Nat × Nat) := do
  let st: StateMyTurn ← PersistentLocalState.getLocalState me stHandle
  let dhSk ← Random.genRand 32
  let dhPk := DiffieHellman.dhPk dhSk

  let transcriptElement: TranscriptElement := { recipient := st.recipient, dhPk }
  let transcript := transcriptElement::st.transcript
  let transcriptHash := computeTranscriptHash st.transcriptHash transcriptElement

  let sigKey ← LongTermKeys.getPrivateKey "Ratchet PKI" me mySigKeyHandle
  let sigNonce ← Random.genRand 32
  let sig := Signature.sign sigKey sigNonce (Comparse.serialize ({transcriptHash}: SigInput))

  let dhss := DiffieHellman.dh st.otherDhPk dhSk
  let k := KdfExpand.kdfExpand (KdfExtract.kdfExtract dhss st.k) transcriptHash 32

  ProtocolEvent.logEvent (RatchetEvent.SendUpdate me st.recipient transcript k)
  let st: StateOtherTurn := { transcript, recipient := st.recipient, transcriptHash, myDhSk := dhSk, k }
  let stHandle ← PersistentLocalState.storeLocalState me st
  let msgHandle ← Network.sendMessage (serialize ({ dhPk, sig } : Message))
  return (stHandle, msgHandle)

def processUpdate (me: Participant) (otherVerifKeyHandle: Nat) (stHandle msgHandle: Nat): Traceful Nat := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: Message ← Comparse.parse msgBytes
  let st: StateOtherTurn ← PersistentLocalState.getLocalState me stHandle

  let transcriptElement: TranscriptElement := { recipient := me, dhPk := msg.dhPk }
  let transcript := transcriptElement::st.transcript
  let transcriptHash := computeTranscriptHash st.transcriptHash transcriptElement

  let verifKey ← LongTermKeys.getPublicKey "Ratchet PKI" st.recipient otherVerifKeyHandle
  guard (Signature.verify verifKey (Comparse.serialize ({transcriptHash}: SigInput)) msg.sig)

  let dhss := DiffieHellman.dh msg.dhPk st.myDhSk
  let k := KdfExpand.kdfExpand (KdfExtract.kdfExtract dhss st.k) transcriptHash 32

  ProtocolEvent.logEvent (RatchetEvent.ReceiveUpdate me st.recipient transcript k)
  let st: StateMyTurn := { transcript, recipient := st.recipient, transcriptHash, otherDhPk := msg.dhPk, k }
  let stHandle ← PersistentLocalState.storeLocalState me st
  return stHandle

def StateMyTurn.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise StateMyTurn stHandle

def StateOtherTurn.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise StateOtherTurn stHandle

end Specification

public section SecurityPredicates

variable [HasExecTrace]

def StateCompromised
  (me: Participant) (transcript: Transcript)
  (tr: ExecTrace)
  : Prop
:=
  (∃ recipient transcriptHash otherDhPk k, PersistentLocalState.LocalStateCompromised me ({transcript, recipient, transcriptHash, otherDhPk, k}: StateMyTurn) tr) ∨
  (∃ recipient transcriptHash myDhSk k, PersistentLocalState.LocalStateCompromised me ({transcript, recipient, transcriptHash, myDhSk, k}: StateOtherTurn) tr)

theorem StateCompromised_le
  (me: Participant) (transcript: Transcript)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    StateCompromised me transcript tr1 →
    StateCompromised me transcript tr2
:= by
  simp only [StateCompromised]
  grind

grind_pattern StateCompromised_le => tr1 ≤ tr2, StateCompromised me transcript tr1

end SecurityPredicates

public section Reachability

variable [HasExecTrace]

-- Future work: the following section is boilerplate that could be meta-programmed
@[expose] public section
def initiate.reachability: ReachabilityConfig := .make (fun (me, other, mySigKeyHandle) => initiate me other mySigKeyHandle)
def processInitiate.reachability: ReachabilityConfig := .make (fun (me, other, otherVerifyKeyHandle, msgHandle) => processInitiate me other otherVerifyKeyHandle msgHandle)
def sendUpdate.reachability: ReachabilityConfig := .make (fun (me, mySigKeyHandle, stHandle) => sendUpdate me mySigKeyHandle stHandle)
def processUpdate.reachability: ReachabilityConfig := .make (fun (me, otherVerifyKeyHandle, stHandle, msgHandle) => processUpdate me otherVerifyKeyHandle stHandle msgHandle)
def StateMyTurn.compromise.reachability: ReachabilityConfig := .make (fun stHandle => StateMyTurn.compromise stHandle)
def StateOtherTurn.compromise.reachability: ReachabilityConfig := .make (fun stHandle => StateOtherTurn.compromise stHandle)
end

#combine into ReachabilityConfig from
  Network,
  LongTermKeys "Ratchet PKI",
  initiate,
  processInitiate,
  sendUpdate,
  processUpdate,
  StateMyTurn.compromise,
  StateOtherTurn.compromise,

end Reachability

end DY.Example.Ratchet
