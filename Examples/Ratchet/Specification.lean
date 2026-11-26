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
  [bytesFunc: Bytes.Def]
  [bytesFunc0: Bytes.Has Random.BytesPart.Functor]
  [bytesFunc1: Bytes.Has Literal.BytesPart.Functor]
  [bytesFunc2: Bytes.Has Concat.BytesPart.Functor]
  [bytesFunc3: Bytes.Has Hash.BytesPart.Functor]
  [bytesFunc4: Bytes.Has Signature.BytesPart.Functor]
  [bytesFunc5: Bytes.Has DiffieHellman.BytesPart.Functor]
  [bytesFunc6: Bytes.Has KdfExtract.BytesPart.Functor]
  [bytesFunc7: Bytes.Has KdfExpand.BytesPart.Functor]
  [bytesLen: Bytes.length.Def]
  [bytesLen0: Bytes.length.Has Random.BytesPart.length]
  [bytesLen1: Bytes.length.Has Literal.BytesPart.length]
  [bytesLen2: Bytes.length.Has Concat.BytesPart.length]
  [bytesLen3: Bytes.length.Has Hash.BytesPart.length]
  [bytesLen4: Bytes.length.Has Signature.BytesPart.length]
  [bytesLen5: Bytes.length.Has DiffieHellman.BytesPart.length]
  [bytesLen6: Bytes.length.Has KdfExtract.BytesPart.length]
  [bytesLen7: Bytes.length.Has KdfExpand.BytesPart.length]
  [att: Bytes.AttackerKnows.Def]
  [att0: Bytes.AttackerKnows.Has Random.attackerKnows]
  [att1: Bytes.AttackerKnows.Has Literal.attackerKnows]
  [att2: Bytes.AttackerKnows.Has Concat.attackerKnows]
  [att3: Bytes.AttackerKnows.Has Hash.attackerKnows]
  [att4: Bytes.AttackerKnows.Has Signature.attackerKnows]
  [att5: Bytes.AttackerKnows.Has DiffieHellman.attackerKnows]
  [att6: Bytes.AttackerKnows.Has KdfExtract.attackerKnows]
  [att7: Bytes.AttackerKnows.Has KdfExpand.attackerKnows]

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
    (.prod .unboundedBytes .bytes)
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
  (.prod .unboundedString .unboundedBytes)
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
    (.prod .unboundedString (.prod .unboundedBytes (.prod .unboundedBytes (.prod .unboundedBytes (.list TranscriptElement.ps.mf)))))
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
    (.prod .unboundedString (.prod .unboundedBytes (.prod .unboundedBytes (.prod .unboundedBytes (.list TranscriptElement.ps.mf)))))
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
  [traceExec: ExecTrace.Def]
  [traceExec0: ExecTrace.Has Network.TracePart.Exec]
  [traceExec1: ExecTrace.Has Random.TracePart.Exec]
  [traceExec2: ExecTrace.Has (ProtocolEvent.TracePart.Exec RatchetEvent)]
  [traceExec3: ExecTrace.Has (PersistentLocalState.CompromisableState.TracePart.Exec StateMyTurn)]
  [traceExec4: ExecTrace.Has (PersistentLocalState.CompromisableState.TracePart.Exec StateOtherTurn)]
  [traceExec5: ExecTrace.Has (LongTermKeys.TracePart.Exec "Ratchet PKI")]
  [attBase: Trace.BaseAttackerKnows.Def]

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
def initiate.transition: TransitionSystem := .make (fun (me, other, mySigKeyHandle) => initiate me other mySigKeyHandle)
def processInitiate.transition: TransitionSystem := .make (fun (me, other, otherVerifyKeyHandle, msgHandle) => processInitiate me other otherVerifyKeyHandle msgHandle)
def sendUpdate.transition: TransitionSystem := .make (fun (me, mySigKeyHandle, stHandle) => sendUpdate me mySigKeyHandle stHandle)
def processUpdate.transition: TransitionSystem := .make (fun (me, otherVerifyKeyHandle, stHandle, msgHandle) => processUpdate me otherVerifyKeyHandle stHandle msgHandle)
def StateMyTurn.compromise.transition: TransitionSystem := .make (fun stHandle => StateMyTurn.compromise stHandle)
def StateOtherTurn.compromise.transition: TransitionSystem := .make (fun stHandle => StateOtherTurn.compromise stHandle)
end

#combine into TransitionSystem from
  Network,
  Random,
  LongTermKeys "Ratchet PKI",
  initiate,
  processInitiate,
  sendUpdate,
  processUpdate,
  StateMyTurn.compromise,
  StateOtherTurn.compromise,

end Reachability

end DY.Example.Ratchet
