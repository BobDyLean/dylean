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
public import DY.Comparse

open DY
open DY.Comparse -- TODO?

@[expose] public section

namespace Test

variable [BytesFunctor]

def Principal := String

structure ClientInitiateState where
  xPk: Bytes
  xSk: Bytes

noncomputable
instance: ParseableSerializeable ClientInitiateState := comparseMetaProgramExists

axiom ClientInitiateState.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ClientInitiateState) (tr: τ):
  isWellFormed pre x tr = (pre x.xPk tr ∧ pre x.xSk tr)

grind_pattern ClientInitiateState.isWellFormedLemma => isWellFormed pre x tr

structure ClientFinishState where
  xPk: Bytes
  kC: Bytes

noncomputable
instance: ParseableSerializeable ClientFinishState := comparseMetaProgramExists

axiom ClientFinishState.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ClientFinishState) (tr: τ):
  isWellFormed pre x tr = (pre x.xPk tr ∧ pre x.kC tr)

grind_pattern ClientFinishState.isWellFormedLemma => isWellFormed pre x tr

structure ServerFinishState where
  yPk: Bytes
  kS: Bytes

noncomputable
instance: ParseableSerializeable ServerFinishState := comparseMetaProgramExists

axiom ServerFinishState.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ServerFinishState) (tr: τ):
  isWellFormed pre x tr = (pre x.yPk tr ∧ pre x.kS tr)

grind_pattern ServerFinishState.isWellFormedLemma => isWellFormed pre x tr

-- TODO move
grind_pattern [grind_later] serialize_formatRel => serialize x
grind_pattern [grind_later] isWellFormedFormatRelBytesInvariant => formatRel buf x, buf.Invariant tr

structure ClientMessage where
  xPk: Bytes

noncomputable
instance: ParseableSerializeable ClientMessage := comparseMetaProgramExists

axiom ClientMessage.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ClientMessage) (tr: τ):
  isWellFormed pre x tr = pre x.xPk tr

grind_pattern ClientMessage.isWellFormedLemma => isWellFormed pre x tr
grind_pattern [grind_later] ClientMessage.isWellFormedLemma => isWellFormed pre x tr

structure ServerMessage where
  yPk: Bytes
  sig: Bytes

noncomputable
instance: ParseableSerializeable ServerMessage := comparseMetaProgramExists

axiom ServerMessage.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ServerMessage) (tr: τ):
  isWellFormed pre x tr = (
    pre x.yPk tr ∧
    pre x.sig tr
  )

grind_pattern ServerMessage.isWellFormedLemma => isWellFormed pre x tr
grind_pattern [grind_later] ServerMessage.isWellFormedLemma => isWellFormed pre x tr

structure SigInput where
  xPk: Bytes
  yPk: Bytes

noncomputable
instance: ParseableSerializeable SigInput := comparseMetaProgramExists

axiom SigInput.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: SigInput) (tr: τ):
  isWellFormed pre x tr = (
    pre x.xPk tr ∧
    pre x.yPk tr
  )

grind_pattern SigInput.isWellFormedLemma => isWellFormed pre x tr
grind_pattern [grind_later] SigInput.isWellFormedLemma => isWellFormed pre x tr

inductive SignedDHEvent where
  | ClientInitiateEvent (client: Principal) (xPk: Bytes)
  | ServerFinishEvent (server: Principal) (xPk: Bytes) (yPk: Bytes) (kS: Bytes)
  | ClientFinishEvent (client server: Principal) (xPk: Bytes) (yPk: Bytes) (kC: Bytes)

section

variable [ExecTraceTypes]

def get_public_key (who: Principal): Traceful Bytes := sorry
def get_private_key (who: Principal): Traceful Bytes := sorry

end

def ClientEphemeralStateCompromised
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  (me: Principal) (xPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ xSk, PersistentLocalState.LocalStateCompromised me ({xPk, xSk}: ClientInitiateState) tr) ∨
  (∃ kC, PersistentLocalState.LocalStateCompromised me ({xPk, kC}: ClientFinishState) tr)

theorem ClientEphemeralStateCompromised_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  (me: Principal) (xPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ClientEphemeralStateCompromised me xPk tr1 →
    ClientEphemeralStateCompromised me xPk tr2
:= by
  simp only [ClientEphemeralStateCompromised]
  grind

grind_pattern ClientEphemeralStateCompromised_le => tr1 ≤ tr2, ClientEphemeralStateCompromised me xPk tr1

def client_label
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  (me: Principal) (xPk: Bytes)
  : Label
where
  isCorrupt tr := ClientEphemeralStateCompromised me xPk tr

def ServerEphemeralStateCompromised
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  (me: Principal) (yPk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  (∃ kS, PersistentLocalState.LocalStateCompromised me ({yPk, kS}: ServerFinishState) tr)

theorem ServerEphemeralStateCompromised_le
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  (me: Principal) (yPk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ServerEphemeralStateCompromised me yPk tr1 →
    ServerEphemeralStateCompromised me yPk tr2
:= by
  simp only [ServerEphemeralStateCompromised]
  grind

grind_pattern ServerEphemeralStateCompromised_le => tr1 ≤ tr2, ServerEphemeralStateCompromised me yPk tr1

def server_label
  [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  (me: Principal) (yPk: Bytes)
  : Label
where
  isCorrupt tr := ServerEphemeralStateCompromised me yPk tr

instance [ExecTraceTypes]: Inhabited Label where
  default := Label.secret

opaque long_term_label [ExecTraceTypes] (me: Principal): Label


structure LongTermKeyUsage where
  principal: Principal

noncomputable
instance : ParseableSerializeable LongTermKeyUsage := comparseMetaProgramExists

@[grind]
noncomputable
def mk_long_term_usage (me: Principal): Usage := {
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
  [TraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
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
  [TraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman.DhPk.invariants]
  : Signature.SignPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman.dh_pk.WellFormed]

section

variable [TraceTypes]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

instance ClientInitiateStateInv
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  : PersistentLocalState.LocalStateInv ClientInitiateState
where
  invariant me st tr :=
    let { xPk, xSk } := st
    xPk = DiffieHellman.dh_pk xSk ∧
    xPk.Publishable tr ∧
    xSk.Invariant tr ∧
    xSk.label tr = client_label me xPk ∧
    True -- usage
  invariant_later := by grind

instance
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  : PersistentLocalState.CompromisableStateInv ClientInitiateState
where
  invariant_implies_KnowableBy participant state tr := by
    simp [PersistentLocalState.LocalStateInv.invariant]
    have: (client_label participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, client_label, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

instance ClientFinishStateInv
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  : PersistentLocalState.LocalStateInv ClientFinishState
where
  invariant me st tr :=
    let { xPk, kC } := st
    xPk.Publishable tr ∧
    kC.Invariant tr ∧
    (kC.label tr).canFlow (client_label me xPk) tr.erase
  invariant_later := by grind

instance
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  : PersistentLocalState.CompromisableStateInv ClientFinishState
where
  invariant_implies_KnowableBy participant state tr := by
    simp [PersistentLocalState.LocalStateInv.invariant]
    have: (client_label participant state.xPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, client_label, ClientEphemeralStateCompromised]
      grind
    grind [canFlowTrans]

instance ServerFinishStateInv
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  : PersistentLocalState.LocalStateInv ServerFinishState
where
  invariant me st tr :=
    let { yPk, kS } := st
    yPk.Publishable tr ∧
    kS.Invariant tr ∧
    (kS.label tr).canFlow (server_label me yPk) tr.erase
  invariant_later := by grind

instance
  [BytesFunctor.Has DiffieHellman.SubF]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  : PersistentLocalState.CompromisableStateInv ServerFinishState
where
  invariant_implies_KnowableBy participant state tr := by
    simp [PersistentLocalState.LocalStateInv.invariant]
    have: (server_label participant state.yPk).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, server_label, ServerEphemeralStateCompromised]
      grind
    grind [canFlowTrans]
end

instance
  [TraceTypes]
  [BytesInvariants]
  [BytesFunctor.Has DiffieHellman.SubF]
  [BytesInvariants.Has DiffieHellman.invariants]
  (sk: Bytes)
  : HoareTriplePure
    (DiffieHellman.dh_pk sk)
    (fun tr => sk.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
  where
    pf := by
      grind [DiffieHellman.dh_pk.Invariant, DiffieHellman.dh_pk.label]

instance
  [TraceTypes]
  [BytesInvariants]
  [BytesFunctor.Has DiffieHellman.SubF]
  [BytesInvariants.Has DiffieHellman.invariants]
  (pk sk: Bytes)
  : HoareTriplePure
    (DiffieHellman.dh pk sk)
    (fun tr =>
      sk.Invariant tr ∧
      pk.Publishable tr
      -- and usage
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.join (sk.label tr) (pk.dhSkLabel tr)
      -- and usage
    )
  where
    pf := by
      grind [DiffieHellman.dh.Invariant, DiffieHellman.dh.label]

instance
  [TraceTypes]
  [BytesInvariants]
  [BytesFunctor.Has Signature.SubF]
  [Signature.SignPred]
  [BytesInvariants.Has Signature.invariants]
  (sk: Bytes)
  : HoareTriplePure
    (Signature.vk sk)
    (fun tr =>
      sk.Invariant tr
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
  where
    pf := by
      grind [Signature.vk.Invariant, Signature.vk.label]

instance
  [BytesFunctor.Has Signature.SubF]
  (sk nonce msg: Bytes)
  : HasGhostArgumentType (Signature.sign sk nonce msg) Usage
where
  dummy := ()

def signMetaprog: GhostParameterFinder where
  findGhost mvar e :=
  Lean.withTraceNode `Step (fun _ => pure m!"signMetaprog") do
    let sk_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let nonce_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let msg_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let signToUnify ← Lean.Meta.mkAppM ``Signature.sign #[sk_mvar, nonce_mvar, msg_mvar]
    trace[Step] "gonna unify {e} and {signToUnify}"
    unless ← Lean.Meta.isDefEq e signToUnify do
      throwError "signMetaprog: cannot unify {e} and {signToUnify}"
    trace[Step] "got {signToUnify}"

    let usg_mvar: Lean.Expr := .mvar mvar
    let tr_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``ProofTrace #[none]))
    let hasUsageToUnify ← Lean.Meta.mkAppOptM ``Bytes.HasUsage #[none, none, none, none, sk_mvar, usg_mvar, tr_mvar]
    trace[Step] "gonna find {hasUsageToUnify} in assumptions"
    let .mvar hasUsageMvar ← Lean.Meta.mkFreshExprMVar hasUsageToUnify
      | throwError ""
    hasUsageMvar.assumption

instance
  [BytesFunctor.Has Signature.SubF]
  (sk nonce msg: Bytes)
  : HasGhostMetaprogram (Signature.sign sk nonce msg) signMetaprog
where
  dummy := ()

instance
  [TraceTypes]
  [BytesInvariants]
  [BytesFunctor.Has Signature.SubF]
  [Signature.SignPred]
  [BytesInvariants.Has Signature.invariants]
  (sk nonce msg: Bytes) (skUsg: Usage)
  : HoareTriplePureGhost
    (Signature.sign sk nonce msg)
    (skUsg)
    (fun tr =>
      sk.Invariant tr ∧
      nonce.Invariant tr ∧
      msg.Invariant tr ∧
      sk.HasUsage skUsg tr ∧
      --nonce `has_usage tr` SigNonce /\
      (sk.label tr).canFlow (nonce.label tr) tr.erase ∧
      (
        (
          skUsg.type = "SigKey" ∧
          Signature.SignPred.pred skUsg (Signature.vk sk) msg tr
        ) ∨ (
          (sk.label tr).canFlow Label.pub tr.erase
        )
      )
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = msg.label tr
    )
  where
    pf := by
      simp only [Signature.sign.label, and_true, and_imp]
      intros
      apply Signature.sign.Invariant sk nonce msg skUsg
      grind

instance
  [BytesFunctor.Has Signature.SubF]
  (vkey msg sig: Bytes): HasGhostArgumentType (Signature.verify vkey msg sig) Usage
where
  dummy := ()

def verifyMetaprog: GhostParameterFinder where
  findGhost mvar e :=
  Lean.withTraceNode `Step (fun _ => pure m!"verifyMetaprog") do
    let vkey_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let msg_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let sig_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``Bytes #[none]))
    let verifyToUnify ← Lean.Meta.mkAppM ``Signature.verify #[vkey_mvar, msg_mvar, sig_mvar]
    trace[Step] "gonna unify {e} and {verifyToUnify}"
    unless ← Lean.Meta.isDefEq e verifyToUnify do
      throwError "verifyMetaprog: cannot unify {e} and {verifyToUnify}"
    trace[Step] "got {verifyToUnify}"

    let usg_mvar: Lean.Expr := .mvar mvar
    let tr_mvar ← Lean.Meta.mkFreshExprMVar (some (← Lean.Meta.mkAppOptM ``ProofTrace #[none]))
    let hasUsageToUnify ← Lean.Meta.mkAppOptM ``Bytes.SignkeyHasUsage #[none, none, none, none, vkey_mvar, usg_mvar, tr_mvar]
    trace[Step] "gonna find {hasUsageToUnify} in assumptions"
    let .mvar hasUsageMvar ← Lean.Meta.mkFreshExprMVar hasUsageToUnify
      | throwError ""
    hasUsageMvar.assumption

instance
  [BytesFunctor.Has Signature.SubF]
  (vkey msg sig: Bytes): HasGhostMetaprogram (Signature.verify vkey msg sig) verifyMetaprog
where
  dummy := ()

instance
  [TraceTypes]
  [BytesInvariants]
  [BytesFunctor.Has Signature.SubF]
  [Signature.SignPred]
  [BytesInvariants.Has Signature.invariants]
  (vkey msg sig: Bytes) (skUsg: Usage)
  : HoareTriplePureGhost
    (Signature.verify vkey msg sig)
    (skUsg: Usage)
    (fun tr =>
      vkey.Invariant tr ∧
      msg.Invariant tr ∧
      sig.Invariant tr ∧
      vkey.SignkeyHasUsage skUsg tr
    )
    (fun res tr =>
      res → (
        (
          skUsg.type = "SigKey" →
          Signature.SignPred.pred skUsg vkey msg tr
        ) ∨ (
          (vkey.signkeyLabel tr).canFlow Label.pub tr.erase
        )
      )
    )
  where
    pf := by
      simp
      intros
      apply Signature.verify.Invariant vkey msg sig skUsg <;>
      grind

instance
  [TraceTypes]
  [BytesInvariants]
  [BytesFunctor.Has Hash.SubF]
  [BytesInvariants.Has Hash.invariants]
  (b: Bytes)
  : HoareTriplePure
    (Hash.hash b)
    (fun tr => b.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = b.label tr
    )
  where
    pf := by
      simp

section

variable [TraceInvariant]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

instance
  [BytesFunctor.Has Signature.SubF]
  : HoareTriple
    (get_public_key who)
    (fun _ => True)
    (fun vk tr =>
      vk.Invariant tr ∧
      vk.signkeyLabel tr = long_term_label who ∧
      vk.SignkeyHasUsage (mk_long_term_usage who) tr
    )
  where
    pf := sorry

instance:
  HoareTriple
    (get_private_key who)
    (fun _ => True)
    (fun sk tr =>
      sk.Invariant tr ∧
      sk.label tr = long_term_label who ∧
      sk.HasUsage (mk_long_term_usage who) tr
    )
  where
    pf := sorry
end

instance SignedDHEventInv
  [BytesFunctor]
  [BytesFunctor.Has Signature.SubF]
  [BytesFunctor.Has DiffieHellman.SubF]
  [TraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh
  [BytesInvariants]
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
      ) ∨ (long_term_label server).isCorrupt tr.erase
    )

namespace SignedDH

section Specification

variable [BytesFunctor.Has Random.SubF]
variable [BytesFunctor.Has Hash.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]
variable [BytesFunctor.Has Signature.SubF]

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT SignedDHEvent)]

variable [ExecTraceTypes.Has (PersistentLocalState.ExecEntryT ClientInitiateState)]
variable [ExecTraceTypes.Has (PersistentLocalState.ExecEntryT ClientFinishState)]
variable [ExecTraceTypes.Has (PersistentLocalState.ExecEntryT ServerFinishState)]

variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh

noncomputable
def client_initiate (me: Principal): Traceful (Nat × Nat) := do
  let xSk ← Random.genRand 32
  let xPk := DiffieHellman.dh_pk xSk

  ProtocolEvent.logEvent (SignedDHEvent.ClientInitiateEvent me xPk)
  let st_ts ← PersistentLocalState.storeLocalState me ({ xPk, xSk }: ClientInitiateState)
  let msg_ts ← Network.sendMessage (serialize ({ xPk } : ClientMessage))
  pure (st_ts, msg_ts)

noncomputable
def server_receive (me: Principal) (msg_ts: Nat) : Traceful (Nat × Nat) := do
  let msg_bytes ← Network.receiveMessage msg_ts
  let msg: ClientMessage ← parse msg_bytes
  let xPk := msg.xPk
  let my_sig_key ← get_private_key me

  let ySk ← Random.genRand 32
  let yPk := DiffieHellman.dh_pk ySk
  let kS := Hash.hash (DiffieHellman.dh xPk ySk)
  let sig_nonce ← Random.genRand 32
  let sig := Signature.sign my_sig_key sig_nonce (serialize ({xPk, yPk}: SigInput))

  ProtocolEvent.logEvent (SignedDHEvent.ServerFinishEvent me xPk yPk kS)
  let st_ts ← PersistentLocalState.storeLocalState me ({ yPk, kS }: ServerFinishState)
  let msg_ts ← Network.sendMessage (serialize ({ yPk, sig } : ServerMessage))
  pure (st_ts, msg_ts)

noncomputable
def client_finish (me: Principal) (server: Principal) (msg_ts: Nat) (sid: Nat) : Traceful Unit := do
  let msg_bytes ← Network.receiveMessage msg_ts
  let msg: ServerMessage ← parse msg_bytes

  let ({xPk, xSk}: ClientInitiateState) ← PersistentLocalState.getLocalState me sid
  let server_vk ← get_public_key server

  guard (Signature.verify server_vk (serialize ({ xPk, yPk := msg.yPk }: SigInput)) msg.sig)
  let kC := Hash.hash (DiffieHellman.dh msg.yPk xSk)

  ProtocolEvent.logEvent (SignedDHEvent.ClientFinishEvent me server xPk msg.yPk kC)
  let _ ← PersistentLocalState.storeLocalState me ({ xPk, kC }: ClientFinishState)

end Specification

section SecurityTheorems

variable [TraceInvariant] [BytesInvariants] [BytesInvariantsProofs]
variable [BaseAttackerKnowledge] [AttackerKnowledge] [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc SignedDHEvent)]

variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh

variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]

variable [TraceInvariant.Has (ProtocolEvent.Invariant SignedDHEvent)]


theorem client_auth
  (client server: Principal)
  (xPk yPk k: Bytes)
  (time: Nat)
  (tr: ProofTrace):
  tr.erase.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
  tr.Invariant → -- reachable
  (
    let tr_before := tr.prefix time
    tr_before.erase.EventLogged (SignedDHEvent.ServerFinishEvent server xPk yPk k) ∨
    (long_term_label server).isCorrupt tr_before.erase
  )
:= by
  intro h_ev h_trinv
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant] at this
  grind

theorem client_secrecy
  (client server: Principal)
  (xPk yPk k: Bytes)
  (tr: ProofTrace):
  k.AttackerKnows tr.erase →
  tr.erase.EventLoggedAt (SignedDHEvent.ClientFinishEvent client server xPk yPk k) time →
  tr.Invariant → -- reachable
  (
    let tr_before := tr.prefix time
    (long_term_label server).isCorrupt tr_before.erase ∨
    ClientEphemeralStateCompromised client xPk tr.erase ∨
    ServerEphemeralStateCompromised server yPk tr.erase
  )
  := by
    intro h_pub h_ev h_trinv
    have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
    simp [ProtocolEvent.EventInv.invariant] at this
    simp_all [client_label, server_label]
    grind

end SecurityTheorems

namespace TestGrindAnnot

variable [BytesFunctor.Has Random.SubF]
variable [BytesFunctor.Has Hash.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]
variable [BytesFunctor.Has Signature.SubF]

variable [TraceInvariant]
variable [BytesInvariants] [BytesInvariantsProofs]

variable [TraceTypes.Has Network.ProofEntryFunc]
variable [TraceTypes.Has Random.ProofEntryFunc]
variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc SignedDHEvent)]

variable [TraceTypes.Has (PersistentLocalState.ProofEntryFunc ClientInitiateState)]
variable [TraceTypes.Has (PersistentLocalState.ProofEntryFunc ClientFinishState)]
variable [TraceTypes.Has (PersistentLocalState.ProofEntryFunc ServerFinishState)]

variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientInitiateState)))] -- ugh
variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState ClientFinishState)))] -- ugh
variable [TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState ServerFinishState)))] -- ugh

variable [BytesInvariants.Has DiffieHellman.invariants]
variable [BytesInvariants.Has Hash.invariants]
variable [BytesInvariants.Has Signature.invariants]
variable [BytesInvariants.Has Random.invariants]

variable [TraceInvariant.Has Network.Invariant]
variable [TraceInvariant.Has Random.Invariant]
variable [TraceInvariant.Has (ProtocolEvent.Invariant SignedDHEvent)]

variable [TraceInvariant.Has (PersistentLocalState.Invariant ClientInitiateState)]
variable [TraceInvariant.Has (PersistentLocalState.Invariant ClientFinishState)]
variable [TraceInvariant.Has (PersistentLocalState.Invariant ServerFinishState)]

-- Test for a more automatic feeling
attribute [grind] ProtocolEvent.EventInv.invariant
attribute [grind] SignedDHEventInv
attribute [grind] ClientInitiateStateInv
attribute [grind] ClientFinishStateInv
attribute [grind] ServerFinishStateInv
attribute [grind] Signature.SignPred.pred
attribute [grind] SignedDHSignPred
attribute [grind] PersistentLocalState.LocalStateInv.invariant

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
  step
  step
  step
  grind

@[instance]
theorem server_receive.spec:
  HoareTriple
    (server_receive me msg_ts)
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
  step with ⟨ fun _: Bytes => Label.secret, Usage.nothing ⟩
  hoist
  step_intro
  -- for monotonicity TODO: how to infer Publishable automatically?
  have h_sig_msg: sig_msg.Publishable tr := by grind
  -- interesting stuff: we will prove things on `sig` later on,
  -- because we need to log the event before
  step_intro
  step
  step_let sig
  step
  step
  step
  grind

@[instance]
theorem client_finish.spec:
  HoareTriple
    (client_finish me server msg_ts sid)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold client_finish
  step
  step
  step
  split
  case h_1 xPk xSk h_xSk =>
    have: xPk.Invariant tr := by grind -- for monotonicity
    have: xSk.Invariant tr := by grind -- for monotonicity
    step
    step
    hoist
    step
    step
    step
    step
    step_intro
    step
    grind

end TestGrindAnnot

end SignedDH

end Test

abbrev SubF.internal: (id: Fin 4) → (Type → Type)
  | 0 => Hash.SubF
  | 1 => Signature.SubF
  | 2 => DiffieHellman.SubF
  | 3 => Random.SubF

abbrev SubF := BytesFunctor.combine SubF.internal

instance: ∀ id, SubBytesFunctor (SubF.internal id)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance

instance: BytesFunctor.HasStep Hash.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 0) SubF)
instance: BytesFunctor.HasStep Signature.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 1) SubF)
instance: BytesFunctor.HasStep DiffieHellman.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 2) SubF)
instance: BytesFunctor.HasStep Random.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 3) SubF)

instance: BytesFunctor where
  BytesF := SubF

instance: BytesFunctor.Has SubF := inferInstanceAs (BytesFunctor.Has BytesF)

example: BytesFunctor.Has Hash.SubF := inferInstance
example: BytesFunctor.Has Signature.SubF := inferInstance
example: BytesFunctor.Has DiffieHellman.SubF := inferInstance
example: BytesFunctor.Has Random.SubF := inferInstance

def SubF.length.internal [BytesFunctor]: ∀ id, Bytes.PartialLength (SubF.internal id)
  | 0 => Hash.SubF.length
  | 1 => Signature.SubF.length
  | 2 => DiffieHellman.SubF.length
  | 3 => Random.SubF.length

abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  Bytes.PartialLength.combine SubF.length.internal

instance: BytesLength where
  funs := SubF.length

instance: BytesLength.HasStep Hash.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 0) SubF.length)
instance: BytesLength.HasStep Signature.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 1) SubF.length)
instance: BytesLength.HasStep DiffieHellman.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 2) SubF.length)
instance: BytesLength.HasStep Random.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 3) SubF.length)

instance: BytesLength.Has SubF.length := inferInstanceAs (BytesLength.Has SubF.length)

example: BytesLength.Has Hash.SubF.length := inferInstance
example: BytesLength.Has Signature.SubF.length := inferInstance
example: BytesLength.Has DiffieHellman.SubF.length := inferInstance
example: BytesLength.Has Random.SubF.length := inferInstance

def attackerKnowledge.internal (id: Fin 4): SubAttackerKnowledge (SubF.internal id) :=
  match id with
  | 0 => Hash.attackerKnowledge
  | 1 => Signature.attackerKnowledge
  | 2 => DiffieHellman.attackerKnowledge
  | 3 => Random.attackerKnowledge

def attackerKnowledge: SubAttackerKnowledge SubF :=
  SubAttackerKnowledge.combine attackerKnowledge.internal

instance: AttackerKnowledge.HasStep Hash.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Signature.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep DiffieHellman.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 2) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Random.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 3) (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledge where
  attackerKnowledge

instance: AttackerKnowledge.Has attackerKnowledge := inferInstanceAs (AttackerKnowledge.Has AttackerKnowledge.attackerKnowledge)

example: AttackerKnowledge.Has Hash.attackerKnowledge := inferInstance
example: AttackerKnowledge.Has Signature.attackerKnowledge := inferInstance
example: AttackerKnowledge.Has DiffieHellman.attackerKnowledge := inferInstance
example: AttackerKnowledge.Has Random.attackerKnowledge := inferInstance

instance: ExecTraceTypes where
  n := 9
  entries
  | 0 => Network.ExecEntryT
  | 1 => Random.ExecEntryT
  | 2 => ProtocolEvent.ExecEntryT Test.SignedDHEvent
  | 3 => PersistentLocalState.ExecEntryT Test.ClientInitiateState
  | 4 => PersistentLocalState.ExecEntryT Test.ClientFinishState
  | 5 => PersistentLocalState.ExecEntryT Test.ServerFinishState
  | 6 => ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState)) -- ugh
  | 7 => ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState)) -- ugh
  | 8 => ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState)) -- ugh

instance: ExecTraceTypes.Has Network.ExecEntryT := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 0))
instance: ExecTraceTypes.Has Random.ExecEntryT := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 1))
instance: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Test.SignedDHEvent) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 2))
instance: ExecTraceTypes.Has (PersistentLocalState.ExecEntryT Test.ClientInitiateState) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 3))
instance: ExecTraceTypes.Has (PersistentLocalState.ExecEntryT Test.ClientFinishState) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 4))
instance: ExecTraceTypes.Has (PersistentLocalState.ExecEntryT Test.ServerFinishState) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 5))
instance: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState))) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 6))
instance: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState))) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 7))
instance: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState))) := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 8))

instance: BaseAttackerKnowledge where
  attackerKnows
  | 0 => Network.baseAttackerKnowledge
  | 1 => Random.baseAttackerKnowledge
  | 2 => ProtocolEvent.baseAttackerKnowledge Test.SignedDHEvent
  | 3 => PersistentLocalState.baseAttackerKnowledge Test.ClientInitiateState
  | 4 => PersistentLocalState.baseAttackerKnowledge Test.ClientFinishState
  | 5 => PersistentLocalState.baseAttackerKnowledge Test.ServerFinishState
  | 6 => ProtocolEvent.baseAttackerKnowledge (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState)) -- ugh
  | 7 => ProtocolEvent.baseAttackerKnowledge (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState)) -- ugh
  | 8 => ProtocolEvent.baseAttackerKnowledge (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState)) -- ugh

-- Has trace attacker knowledge?

instance: TraceTypes where
  proofEntries
  | 0 => Network.ProofEntryT
  | 1 => Random.ProofEntryT
  | 2 => ProtocolEvent.ProofEntryT Test.SignedDHEvent
  | 3 => PersistentLocalState.ProofEntryT Test.ClientInitiateState
  | 4 => PersistentLocalState.ProofEntryT Test.ClientFinishState
  | 5 => PersistentLocalState.ProofEntryT Test.ServerFinishState
  | 6 => ProtocolEvent.ProofEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState)) -- ugh
  | 7 => ProtocolEvent.ProofEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState)) -- ugh
  | 8 => ProtocolEvent.ProofEntryT (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState)) -- ugh
  funs
  | 0 => Network.ProofEntryFunc
  | 1 => Random.ProofEntryFunc
  | 2 => ProtocolEvent.ProofEntryFunc Test.SignedDHEvent
  | 3 => PersistentLocalState.ProofEntryFunc Test.ClientInitiateState
  | 4 => PersistentLocalState.ProofEntryFunc Test.ClientFinishState
  | 5 => PersistentLocalState.ProofEntryFunc Test.ServerFinishState
  | 6 => ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState)) -- ugh
  | 7 => ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState)) -- ugh
  | 8 => ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState)) -- ugh

instance: TraceTypes.Has Network.ProofEntryFunc := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 0))
instance: TraceTypes.Has Random.ProofEntryFunc := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 1))
instance: TraceTypes.Has (ProtocolEvent.ProofEntryFunc Test.SignedDHEvent) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 2))
instance: TraceTypes.Has (PersistentLocalState.ProofEntryFunc Test.ClientInitiateState) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 3))
instance: TraceTypes.Has (PersistentLocalState.ProofEntryFunc Test.ClientFinishState) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 4))
instance: TraceTypes.Has (PersistentLocalState.ProofEntryFunc Test.ServerFinishState) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 5))
instance: TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState))) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 6))
instance: TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState))) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 7))
instance: TraceTypes.Has (ProtocolEvent.ProofEntryFunc (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState))) := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 8))

def invariants.internal: (id: Fin 4) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => Hash.invariants
  | 1 => Signature.invariants
  | 2 => DiffieHellman.invariants
  | 3 => Random.invariants

abbrev invariants: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

instance [BytesInvariants]: BytesInvariants.HasStep Hash.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Signature.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep DiffieHellman.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 2) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Random.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 3) invariants)

instance: BytesInvariants where
  invs := invariants

instance: BytesInvariants.Has invariants := inferInstance

example: BytesInvariants.Has Hash.invariants := inferInstance
example: BytesInvariants.Has Signature.invariants := inferInstance
example: BytesInvariants.Has DiffieHellman.invariants := inferInstance
example: BytesInvariants.Has Random.invariants := inferInstance

def invariantsProofs.internal: (id: Fin 4) → Bytes.PartialInvariantsProofs (invariants.internal id)
  | 0 => Hash.invariantsProofs
  | 1 => Signature.invariantsProofs
  | 2 => DiffieHellman.invariantsProofs
  | 3 => Random.invariantsProofs

abbrev invariantsProofs: Bytes.PartialInvariantsProofs invariants :=
  Bytes.PartialInvariantsProofs.combine invariantsProofs.internal

instance: BytesInvariantsProofs where
  pfs := invariantsProofs

instance: TraceInvariant where
  invs
  | 0 => Network.Invariant
  | 1 => Random.Invariant
  | 2 => ProtocolEvent.Invariant (Test.SignedDHEvent)
  | 3 => PersistentLocalState.Invariant Test.ClientInitiateState
  | 4 => PersistentLocalState.Invariant Test.ClientFinishState
  | 5 => PersistentLocalState.Invariant Test.ServerFinishState
  | 6 => ProtocolEvent.Invariant (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState)) -- ugh
  | 7 => ProtocolEvent.Invariant (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState)) -- ugh
  | 8 => ProtocolEvent.Invariant (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState)) -- ugh

instance: TraceInvariant.Has Network.Invariant := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 0))
instance: TraceInvariant.Has Random.Invariant := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 1))
instance: TraceInvariant.Has (ProtocolEvent.Invariant Test.SignedDHEvent) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 2))
instance: TraceInvariant.Has (PersistentLocalState.Invariant Test.ClientInitiateState) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 3))
instance: TraceInvariant.Has (PersistentLocalState.Invariant Test.ClientFinishState) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 4))
instance: TraceInvariant.Has (PersistentLocalState.Invariant Test.ServerFinishState) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 5))
instance: TraceInvariant.Has (ProtocolEvent.Invariant (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState))) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 6))
instance: TraceInvariant.Has (ProtocolEvent.Invariant (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState))) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 7))
instance: TraceInvariant.Has (ProtocolEvent.Invariant (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState))) := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 8))

instance: BaseAttackerKnowledgeTheorem where
  pfs
  | 0 => Network.baseAttackerKnowledgeTheorem
  | 1 => Random.baseAttackerKnowledgeTheorem
  | 2 => ProtocolEvent.baseAttackerKnowledgeTheorem Test.SignedDHEvent
  | 3 => PersistentLocalState.baseAttackerKnowledgeTheorem Test.ClientInitiateState
  | 4 => PersistentLocalState.baseAttackerKnowledgeTheorem Test.ClientFinishState
  | 5 => PersistentLocalState.baseAttackerKnowledgeTheorem Test.ServerFinishState
  | 6 => ProtocolEvent.baseAttackerKnowledgeTheorem (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientInitiateState)) -- ugh
  | 7 => ProtocolEvent.baseAttackerKnowledgeTheorem (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ClientFinishState)) -- ugh
  | 8 => ProtocolEvent.baseAttackerKnowledgeTheorem (Compromise.CompromiseEvent (PersistentLocalState.LocalState Test.ServerFinishState)) -- ugh

instance: (id: Fin 4) → SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem Hash.attackerKnowledge)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem Signature.attackerKnowledge)
  | 2 => inferInstanceAs (SubAttackerKnowledgeTheorem DiffieHellman.attackerKnowledge)
  | 3 => inferInstanceAs (SubAttackerKnowledgeTheorem Random.attackerKnowledge)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledgeTheorem where
  inst := inferInstanceAs (SubAttackerKnowledgeTheorem attackerKnowledge)

theorem test (b: Bytes) (tr: ProofTrace) :
    tr.Invariant →
    Bytes.AttackerKnows b tr.erase →
    b.Publishable tr
  := by
    apply Bytes.AttackerKnows_implies_Publishable

end
