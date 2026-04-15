module

public import DY.Trace
public import DY.Step
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
import DY.Step.Utils

open DY
open DY.Comparse -- TODO?

@[expose] public section

namespace SignedDH

section StructuresAndFormats

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

structure ClientInitiateState where
  xPk: Bytes
  xSk: Bytes

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

structure ClientFinishState where
  xPk: Bytes
  kC: Bytes

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

structure ServerFinishState where
  yPk: Bytes
  kS: Bytes

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

structure ClientMessage where
  xPk: Bytes

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

structure ServerMessage where
  yPk: Bytes
  sig: Bytes

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

structure SigInput where
  xPk: Bytes
  yPk: Bytes

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

inductive SignedDHEvent where
  | ClientInitiateEvent (client: Participant) (xPk: Bytes)
  | ServerFinishEvent (server: Participant) (xPk: Bytes) (yPk: Bytes) (kS: Bytes)
  | ClientFinishEvent (client server: Participant) (xPk: Bytes) (yPk: Bytes) (kC: Bytes)

end StructuresAndFormats

section Specification

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has Random.SubF]
variable [BytesFunctor.Has Hash.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]
variable [BytesFunctor.Has Signature.SubF]

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDH")]

variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ServerFinishState)]

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

section ForSecurityTheorem

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

def ClientEphemeralStateCompromised
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientFinishState)]
  (me: Participant) (xPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ xSk, PersistentLocalState.LocalStateCompromised me ({xPk, xSk}: ClientInitiateState) tr) ∨
  (∃ kC, PersistentLocalState.LocalStateCompromised me ({xPk, kC}: ClientFinishState) tr)

theorem ClientEphemeralStateCompromised_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientFinishState)]
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
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ServerFinishState)]
  (me: Participant) (yPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ kS, PersistentLocalState.LocalStateCompromised me ({yPk, kS}: ServerFinishState) tr)

theorem ServerEphemeralStateCompromised_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ServerFinishState)]
  (me: Participant) (yPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ServerEphemeralStateCompromised me yPk tr1 →
    ServerEphemeralStateCompromised me yPk tr2
:= by
  simp only [ServerEphemeralStateCompromised]
  grind

grind_pattern ServerEphemeralStateCompromised_le => tr1 ≤ tr2, ServerEphemeralStateCompromised me yPk tr1

end ForSecurityTheorem

section Invariants

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

def client_label
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientFinishState)]
  (me: Participant) (xPk: Bytes)
  : Label
where
  isCorrupt tr := ClientEphemeralStateCompromised me xPk tr


def server_label
  [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ServerFinishState)]
  (me: Participant) (yPk: Bytes)
  : Label
where
  isCorrupt tr := ServerEphemeralStateCompromised me yPk tr

structure LongTermKeyUsage where
  principal: Participant

instance : ParseableSerializeable LongTermKeyUsage := .make <|
  .triviallyIsomorphic
    (.string)
    (fun principal => { principal })
    (fun { principal := principal } => principal)


@[grind]
def mk_long_term_usage (me: Participant): Usage := {
  type := "SigKey",
  tag := "SignedDH",
  data := serialize ({ principal := me }: LongTermKeyUsage)
}

@[grind inj]
theorem mk_long_term_usage_inj:
  Function.Injective mk_long_term_usage
  := by
    simp [Function.Injective, mk_long_term_usage]
    grind


instance SignedDHSignPred
  [BytesFunctor.Has DiffieHellman.SubF]
  [BytesFunctor.Has Hash.SubF]
  [ExecTraceTypes] [ProofTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ServerFinishState)]
  : Signature.SignPred
where
  pred skUsg vk msg tr :=
    ∃ server, skUsg = mk_long_term_usage server ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) => (
        ∃ ySk,
          msg.yPk = DiffieHellman.dh_pk ySk ∧
          ySk.label tr = server_label server msg.yPk ∧
          tr.erase.EventLogged (SignedDHEvent.ServerFinishEvent server msg.xPk msg.yPk (Hash.hash (DiffieHellman.dh msg.xPk ySk)))
      )
    )

instance
  [BytesFunctor.Has DiffieHellman.SubF]
  [BytesFunctor.Has Hash.SubF]
  [ExecTraceTypes] [ProofTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ServerFinishState)]
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman.DhPk.invariants]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  : Signature.SignPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman.dh_pk.WellFormed]


variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

instance ClientInitiateStateInv
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  : PersistentLocalState.CompromisableLocalStateInv ClientInitiateState
where
  invariant me st tr :=
    let { xPk, xSk } := st
    xPk = DiffieHellman.dh_pk xSk ∧
    xPk.Publishable tr ∧
    xSk.Invariant tr ∧
    xSk.label tr = client_label me xPk
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (client_label participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, client_label, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

-- for monotonicity
theorem ClientInitiateStateInv_imp_Invariant
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  (participant: Participant) (st: ClientInitiateState)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.xSk.Invariant tr ∧
      st.xPk.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] ClientInitiateStateInv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr

instance ClientFinishStateInv
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  : PersistentLocalState.CompromisableLocalStateInv ClientFinishState
where
  invariant me st tr :=
    let { xPk, kC } := st
    xPk.Publishable tr ∧
    kC.Invariant tr ∧
    (kC.label tr).canFlow (client_label me xPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (client_label participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, client_label, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

instance ServerFinishStateInv
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ServerFinishState)]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  : PersistentLocalState.CompromisableLocalStateInv ServerFinishState
where
  invariant me st tr :=
    let { yPk, kS } := st
    yPk.Publishable tr ∧
    kS.Invariant tr ∧
    (kS.label tr).canFlow (server_label me yPk) tr.erase
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    have: (server_label participant state.yPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, server_label, ServerEphemeralStateCompromised]
      grind
    grind [canFlowTrans]


instance [BytesFunctor.Has Signature.SubF]: LongTermKeys.ExecConfig "SignedDH" Signature.vk where

@[grind]
instance
  [BytesFunctor.Has Signature.SubF] [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
  [ExecTraceTypes.Has <| LongTermKeys.ExecEntryT "SignedDH"]
  : LongTermKeys.ProofConfig "SignedDH" mk_long_term_usage
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "SignedDH" who vk ∧
    vk.SignkeyHasUsage (mk_long_term_usage who) tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

instance SignedDHEventInv
  [BytesFunctor.Has Signature.SubF]
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes] [ProofTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientInitiateState)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ClientFinishState)]
  [ExecTraceTypes.Has (PersistentLocalState.Compromise.ExecEntryT ServerFinishState)]
  [ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDH")]
  [BytesInvariants]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
  : ProtocolEvent.EventInv (SignedDHEvent)
where
  invariant tr ev :=
    match ev with
    | SignedDHEvent.ClientInitiateEvent client xPk => (
      xPk.Invariant tr ∧
      xPk.dhSkLabel tr = client_label client xPk
    )
    | SignedDHEvent.ServerFinishEvent server xPk yPk kS => (
      kS.Invariant tr ∧
      xPk.Invariant tr ∧
      kS.label tr = (server_label server yPk).join (xPk.dhSkLabel tr)
    )
    | SignedDHEvent.ClientFinishEvent client server xPk yPk kC => (
      (
        tr.erase.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk kC) ∧
        kC.Invariant tr ∧
        kC.label tr = (client_label client xPk).join (server_label server yPk)
      ) ∨ (∃ spk, (LongTermKeys.label "SignedDH" server spk).isCorrupt tr.erase)
    )

end Invariants

section SecurityTheorems

variable [BytesFunctor] [BytesLength]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants] [BytesInvariantsProofs]
variable [BaseAttackerKnowledge] [AttackerKnowledge] [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]

variable [BytesInvariants.Has Literal.invariants]
variable [BytesInvariants.Has Concat.invariants]

variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SignedDHEvent)]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT "SignedDH")]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT "SignedDH")]

variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateState)]
variable [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
variable [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientFinishState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ServerFinishState)]
variable [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerFinishState)]

variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT SignedDHEvent)]


theorem client_auth
  (client server: Participant)
  (xPk yPk k: Bytes)
  (time: Nat)
  (tr: ProofTrace):
  tr.erase.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
  tr.Invariant → -- reachable
  (
    let tr_before := tr.prefix time
    tr_before.erase.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk k) ∨
    (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH" server spk tr_before.erase)
  )
:= by
  intro h_ev h_trinv
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant, LongTermKeys.label] at this
  grind

theorem client_secrecy
  (client server: Participant)
  (xPk yPk k: Bytes)
  (tr: ProofTrace):
  k.AttackerKnows tr.erase →
  tr.erase.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
  tr.Invariant → -- reachable
  (
    let tr_before := tr.prefix time
    (∃ spk, LongTermKeys.LongTermKeyCompromised "SignedDH" server spk tr_before.erase) ∨
    ClientEphemeralStateCompromised client xPk tr.erase ∨
    ServerEphemeralStateCompromised server yPk tr.erase
  )
  := by
    intro h_pub h_ev h_trinv
    have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
    simp [ProtocolEvent.EventInv.invariant] at this
    simp_all [client_label, server_label, LongTermKeys.label]
    grind

end SecurityTheorems

section Proofs

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has Random.SubF]
variable [BytesFunctor.Has Hash.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]
variable [BytesFunctor.Has Signature.SubF]

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants] [BytesInvariantsProofs]

variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ProofTraceTypes.Has Network.ProofEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ProofTraceTypes.Has Random.ProofEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SignedDHEvent)]
variable [ExecTraceTypes.Has <| LongTermKeys.ExecEntryT "SignedDH"]
variable [ProofTraceTypes.Has <| LongTermKeys.ProofEntryT "SignedDH"]

variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientInitiateState)]
variable [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ClientFinishState)]
variable [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientFinishState)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ServerFinishState)]
variable [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerFinishState)]

variable [BytesInvariants.Has Literal.invariants]
variable [BytesInvariants.Has Concat.invariants]
variable [BytesInvariants.Has DiffieHellman.invariants]
variable [BytesInvariants.Has Hash.invariants]
variable [BytesInvariants.Has Signature.invariants]
variable [BytesInvariants.Has Random.invariants]

variable [TraceInvariant.Has Network.ProofEntryT]
variable [TraceInvariant.Has Random.ProofEntryT]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT SignedDHEvent)]
variable [TraceInvariant.Has <| LongTermKeys.ProofEntryT "SignedDH"]

variable [TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientInitiateState)]
variable [TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ClientFinishState)]
variable [TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerFinishState)]

-- Test for a more automatic feeling
attribute [grind] ProtocolEvent.EventInv.invariant
attribute [grind] SignedDHEventInv
attribute [grind] ClientInitiateStateInv
attribute [grind] ClientFinishStateInv
attribute [grind] ServerFinishStateInv
attribute [grind] Signature.SignPred.pred
attribute [grind] SignedDHSignPred
attribute [grind] PersistentLocalState.LocalStateInv.invariant
attribute [grind] PersistentLocalState.CompromisableLocalStateInv.toLocalStateInv
attribute [grind] LongTermKeys.IsLongTermPublicKey
attribute [grind] LongTermKeys.IsLongTermSecretKey

@[instance]
theorem client_initiate.spec:
  HoareTriple
    (client_initiate me)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold client_initiate
  step with ⟨ fun xSk => client_label me (DiffieHellman.dh_pk xSk), Usage.nothing ⟩
  step
  step
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  step
  grind

@[instance]
theorem server_receive.spec:
  HoareTriple
    (server_receive me sk_ts msg_ts)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold server_receive
  step
  step
  step_intro
  step
  step with ⟨ fun ySk => server_label me (DiffieHellman.dh_pk ySk), Usage.nothing ⟩
  step
  hoist
  step
  step
  step with ⟨ fun _ => Label.secret, Usage.nothing ⟩
  hoist
  step_intro
  step_intro -- interesting stuff: we will prove things on `sig` later on, because we need to log the event before
  step
  step_let sig with ⟨ mk_long_term_usage me ⟩
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    have: sig_msg.Publishable tr := by grind -- TODO how to infer this automatically?
    grind
  step
  grind

@[instance]
theorem client_finish.spec:
  HoareTriple
    (client_finish me server pk_ts msg_ts sid)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold client_finish
  step
  step
  step
  split
  step
  step with ⟨ mk_long_term_usage server ⟩ by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  hoist
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step_intro
  step
  grind

end Proofs

end SignedDH

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

@[expose]
public
def ExecEntryT.internal: Fin 7 → Type
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

-- Has trace attacker knowledge?

@[expose]
public
def ProofEntryT.internal: Fin 7 → Type
  | 0 => Network.ProofEntryT
  | 1 => Random.ProofEntryT
  | 2 => ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState
  | 6 => LongTermKeys.ProofEntryT "SignedDH"

public
abbrev ProofEntryT: Type :=
  ProofTraceTypes.combine ProofEntryT.internal

public
instance: ∀ id, ErasableProofEntry (ExecEntryT.internal id) (ProofEntryT.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => by dsimp only [ExecEntryT.internal, ProofEntryT.internal]; infer_instance

public
instance: ErasableProofEntry ExecEntryT ProofEntryT :=
  (inferInstance: ErasableProofEntry (ExecTraceTypes.combine ExecEntryT.internal) (ProofTraceTypes.combine ProofEntryT.internal))

instance: ProofTraceTypes.HasStep Network.ProofEntryT ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 0) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep Random.ProofEntryT ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 1) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 2) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 3) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 4) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 5) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (LongTermKeys.ProofEntryT "SignedDH") ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 6) (ProofTraceTypes.combine ProofEntryT.internal))

instance: ProofTraceTypes where
  ProofT := ProofEntryT
  tc := inferInstance

instance: ProofTraceTypes.Has ProofEntryT := inferInstanceAs (ProofTraceTypes.Has ProofTrace.Entry)

example: ProofTraceTypes.Has Network.ProofEntryT := inferInstance
example: ProofTraceTypes.Has Random.ProofEntryT := inferInstance
example: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) := inferInstance
example: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) := inferInstance
example: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) := inferInstance
example: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) := inferInstance
example: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "SignedDH") := inferInstance

def invariants.internal: (id: Fin 6) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => Literal.invariants
  | 1 => Concat.invariants
  | 2 => Hash.invariants
  | 3 => Signature.invariants
  | 4 => DiffieHellman.invariants
  | 5 => Random.invariants

abbrev invariants: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

instance [BytesInvariants]: BytesInvariants.HasStep Literal.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Concat.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Hash.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 2) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Signature.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 3) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep DiffieHellman.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 4) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Random.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 5) invariants)

instance: BytesInvariants where
  invs := invariants

instance: BytesInvariants.Has invariants := inferInstance

example: BytesInvariants.Has Hash.invariants := inferInstance
example: BytesInvariants.Has Signature.invariants := inferInstance
example: BytesInvariants.Has DiffieHellman.invariants := inferInstance
example: BytesInvariants.Has Random.invariants := inferInstance

def invariantsProofs.internal: (id: Fin 6) → Bytes.PartialInvariantsProofs (invariants.internal id)
  | 0 => Literal.invariantsProofs
  | 1 => Concat.invariantsProofs
  | 2 => Hash.invariantsProofs
  | 3 => Signature.invariantsProofs
  | 4 => DiffieHellman.invariantsProofs
  | 5 => Random.invariantsProofs

abbrev invariantsProofs: Bytes.PartialInvariantsProofs invariants :=
  Bytes.PartialInvariantsProofs.combine invariantsProofs.internal

instance: BytesInvariantsProofs where
  pfs := invariantsProofs

public
instance: ∀ id, SubTraceInvariant (ProofEntryT.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance: SubTraceInvariant ProofEntryT :=
  (inferInstance: SubTraceInvariant (ProofTraceTypes.combine ProofEntryT.internal))

instance : TraceInvariant where
  tc_inv := by dsimp only [ProofTrace.Entry, ProofTraceTypes.ProofT]; infer_instance

instance: TraceInvariant.Has ProofEntryT := inferInstanceAs (TraceInvariant.Has ProofTrace.Entry)

instance: TraceInvariant.HasStep Network.ProofEntryT ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 0) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep Random.ProofEntryT ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 1) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 2) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 3) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 4) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 5) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (LongTermKeys.ProofEntryT "SignedDH") ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 6) (ProofTraceTypes.combine ProofEntryT.internal))

example: TraceInvariant.Has Network.ProofEntryT := inferInstance
example: TraceInvariant.Has Random.ProofEntryT := inferInstance
example: TraceInvariant.Has (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) := inferInstance
example: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) := inferInstance
example: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) := inferInstance
example: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) := inferInstance
example: TraceInvariant.Has (LongTermKeys.ProofEntryT "SignedDH") := inferInstance

instance : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal id) (baseAttackerKnowledge.internal id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Network.baseAttackerKnowledgeTheorem
  | 1 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Random.baseAttackerKnowledgeTheorem
  | 2 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply ProtocolEvent.baseAttackerKnowledgeTheorem
  | 3 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 4 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 5 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 6 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply LongTermKeys.baseAttackerKnowledgeTheorem "SignedDH"

instance: SubBaseAttackerKnowledgeTheorem (ProofEntryT) (baseAttackerKnowledge) := by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  infer_instance

instance: BaseAttackerKnowledgeTheorem where
  pf := by
    dsimp only [ProofTrace.Entry, ProofTraceTypes.ProofT, BaseAttackerKnowledge.attackerKnows]
    -- TODO infer_instance
    exact instSubBaseAttackerKnowledgeTheoremExecEntryTProofEntryTBaseAttackerKnowledge

instance: (id: Fin 6) → SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem Literal.attackerKnowledge)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem Concat.attackerKnowledge)
  | 2 => inferInstanceAs (SubAttackerKnowledgeTheorem Hash.attackerKnowledge)
  | 3 => inferInstanceAs (SubAttackerKnowledgeTheorem Signature.attackerKnowledge)
  | 4 => inferInstanceAs (SubAttackerKnowledgeTheorem DiffieHellman.attackerKnowledge)
  | 5 => inferInstanceAs (SubAttackerKnowledgeTheorem Random.attackerKnowledge)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledgeTheorem where
  inst := inferInstanceAs (SubAttackerKnowledgeTheorem attackerKnowledge)

theorem test (b: Bytes) (tr: ProofTrace) :
    tr.Invariant →
    Bytes.AttackerKnows b tr.erase →
    b.Publishable tr
  := by
    apply Bytes.AttackerKnows_implies_Publishable
