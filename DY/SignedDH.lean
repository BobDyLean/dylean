import DY.Trace
import DY.Step
import DY.Bytes
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.Hash
import DY.EquationalTheory.Sign
import DY.EquationalTheory.DiffieHellman
import DY.Actions.Network
import DY.Actions.Random

open DY

namespace Test

variable [BytesFunctor]
variable [BytesFunctor.Has Random.SubF]
variable [BytesFunctor.Has Hash.SubF]
variable [BytesFunctor.Has DiffieHellman.SubF]
variable [BytesFunctor.Has Signature.SubF]

def Principal := String

class ParseableSerializeable (a: Type) where
  parse: Bytes -> Err a
  serialize: a -> Bytes

  parse_serialize_inv:
    ∀ x: a,
      parse (serialize x) = some x

  serialize_parse_inv:
    ∀ buf: Bytes, ∀ x: a,
      parse buf = some x →
      buf = serialize x

open ParseableSerializeable

axiom comparseExists {a: Type}: ParseableSerializeable a

@[simp]
theorem parse_serialize_inv_grind [ParseableSerializeable a] (x: a):
  ParseableSerializeable.parse (serialize x) = some x
  := by
  exact (parse_serialize_inv x)

grind_pattern parse_serialize_inv_grind => serialize x

def formatRel [ParseableSerializeable a] (buf: Bytes) (x: a) :=
  buf = serialize x

instance [TraceInvariant] [ParseableSerializeable a]:
  HoareTriple
    (parse buf: Err a)
    (fun _ => True)
    (fun res _ => formatRel buf res)
where
  pf := by
    simp only [hoareTriple, wp, formatRel, OptionT.run]
    grind [serialize_parse_inv]

theorem serialize_formatRel [ParseableSerializeable a] (x: a):
  (formatRel (serialize x) x)
  := by
    simp [formatRel]

grind_pattern serialize_formatRel => serialize x

@[grind! .]
theorem parse_formatRel [ParseableSerializeable a] (b: Bytes):
  match (parse b: Err a) with
  | none => True
  | some x => formatRel b x
  := by
    grind [formatRel, serialize_parse_inv]

def isWellFormed [ParseableSerializeable a] (pre: Bytes → τ → Prop) (x: a) (tr: τ): Prop :=
  pre (serialize x) tr

theorem isWellFormedFormatRel [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  formatRel buf x →
  (pre buf tr = isWellFormed pre x tr)
  := by
    grind [isWellFormed, formatRel]

theorem isWellFormedFormatRelBytesWellFormed [TraceTypes] [BytesWellFormed] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.WellFormed tr = isWellFormed Bytes.WellFormed x tr)
  := isWellFormedFormatRel Bytes.WellFormed

grind_pattern isWellFormedFormatRelBytesWellFormed => formatRel buf x, buf.WellFormed tr

theorem isWellFormedFormatRelBytesInvariant [TraceTypes] [BytesInvariant] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Invariant tr = isWellFormed Bytes.Invariant x tr)
  := isWellFormedFormatRel Bytes.Invariant

grind_pattern isWellFormedFormatRelBytesInvariant => formatRel buf x, buf.Invariant tr

theorem isWellFormedFormatRelIsPublishable [TraceTypes] [BytesInvariants] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Publishable tr = isWellFormed Bytes.Publishable x tr)
  := isWellFormedFormatRel Bytes.Publishable

grind_pattern isWellFormedFormatRelIsPublishable => formatRel buf x, Bytes.Publishable buf tr

theorem isWellFormedParse [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  parse buf = some x →
  pre buf tr →
  isWellFormed pre x tr
  := by
    grind [isWellFormed, serialize_parse_inv]

class BytesCompatible (pre: Bytes → τ → Prop) where
  dummy: Unit

instance [TraceTypes] [BytesWellFormed]: BytesCompatible Bytes.WellFormed where
  dummy := ()

instance [TraceTypes] [BytesInvariant]: BytesCompatible Bytes.Invariant where
  dummy := ()

instance [TraceTypes] [BytesInvariants]: BytesCompatible Bytes.Publishable where
  dummy := ()

inductive ClientState where
  | ClientInitiateState (x_sk: Bytes)
  | ClientFinishState (k_c: Bytes)

instance : ParseableSerializeable ClientState := sorry

inductive ServerState where
  | ServerFinishState (k_s: Bytes)

instance : ParseableSerializeable ServerState := sorry

structure ClientMessage where
  x_pk: Bytes

instance : ParseableSerializeable ClientMessage := sorry

@[grind]
axiom ClientMessage.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ClientMessage) (tr: τ):
  isWellFormed pre x tr = pre x.x_pk tr

structure ServerMessage where
  y_pk: Bytes
  sig: Bytes

instance : ParseableSerializeable ServerMessage := sorry

@[grind]
axiom ServerMessage.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: ServerMessage) (tr: τ):
  isWellFormed pre x tr = (
    pre x.y_pk tr ∧
    pre x.sig tr
  )

structure SigInput where
  x_pk: Bytes
  y_pk: Bytes

noncomputable
instance: ParseableSerializeable SigInput := comparseExists

@[grind]
axiom SigInput.isWellFormedLemma
  (pre: Bytes → τ → Prop) [BytesCompatible pre] (x: SigInput) (tr: τ):
  isWellFormed pre x tr = (
    pre x.x_pk tr ∧
    pre x.y_pk tr
  )

inductive SignedDHEvent where
  | ClientInitiateEvent (x_pk: Bytes)
  | ServerFinishEvent (x_pk: Bytes) (y_pk: Bytes) (k_s: Bytes)
  | ClientFinishEvent (server: Principal) (x_pk: Bytes) (y_pk: Bytes) (k_c: Bytes)

instance : ParseableSerializeable SignedDHEvent := sorry

-- setup

axiom event_logged_at [TraceTypes] (who: Principal) (ev: SignedDHEvent) (i: Nat) (tr: ProofTrace): Prop
abbrev event_logged [TraceTypes] (who: Principal) (ev: SignedDHEvent) (tr: ProofTrace) :=
  ∃ i, event_logged_at who ev i tr

namespace DY -- ???
@[grind→]
axiom _root_.DY.Trace.MonotoneLemmas.event_logged_at_later [TraceTypes] (who: Principal) (ev: SignedDHEvent) (i: Nat) (tr1 tr2: ProofTrace): tr1 ≤ tr2 → event_logged_at who ev i tr1 → event_logged_at who ev i tr2
end DY

section

variable [ExecTraceTypes]

def new_sid (me: Principal): Traceful Nat := sorry
def set_client_state (me: Principal) (sid: Nat) (st: ClientState): Traceful Unit := sorry
def get_client_state (me: Principal) (sid: Nat): Traceful ClientState  := sorry
def set_server_state (me: Principal) (sid: Nat) (st: ServerState): Traceful Unit := sorry
def get_server_state (me: Principal) (sid: Nat): Traceful ServerState  := sorry
def get_public_key (who: Principal): Traceful Bytes := sorry
def get_private_key (who: Principal): Traceful Bytes := sorry
def log_event (who: Principal) (ev: SignedDHEvent): Traceful Unit := sorry

end

-- invariants

instance [ExecTraceTypes]: Inhabited Label where
  default := Label.secret

opaque client_label [ExecTraceTypes] (me: Principal): Label
opaque server_label [ExecTraceTypes] (me: Principal): Label
opaque long_term_label [ExecTraceTypes] (me: Principal): Label


structure LongTermKeyUsage where
  principal: Principal

noncomputable
instance : ParseableSerializeable LongTermKeyUsage := comparseExists

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

instance [TraceTypes]: Signature.SignPred where
  pred skUsg vk msg tr :=
    ∃ server, skUsg = mk_long_term_usage server ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) => (
        ∃ y_sk,
          msg.y_pk = DiffieHellman.dh_pk y_sk ∧
          y_sk.label tr = server_label server ∧
          event_logged server (.ServerFinishEvent msg.x_pk msg.y_pk (Hash.hash (DiffieHellman.dh msg.x_pk y_sk))) tr
      )
    )

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has DiffieHellman.DhPk.invariants]: Signature.SignPredProof where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman.dh_pk.WellFormed]

section

variable [TraceTypes]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

def client_state_inv (me: Principal) (sid: Nat) (st: ClientState) (tr: ProofTrace) :=
  match st with
  | .ClientInitiateState x_sk =>
    x_sk.Invariant tr ∧
    x_sk.label tr = client_label me ∧
    True -- usage
  | .ClientFinishState k_c =>
    k_c.Invariant tr ∧
    (k_c.label tr).canFlow (client_label me) tr.erase

namespace DY -- ???
-- scoped ??
@[grind→]
theorem _root_.DY.Trace.MonotoneLemmas.client_state_inv_later
  (me: Principal) (sid: Nat) (st: ClientState) (tr1 tr2: ProofTrace):
  tr1 ≤ tr2 → client_state_inv me sid st tr1 → client_state_inv me sid st tr2
  := by
    unfold client_state_inv
    grind
end DY


def server_state_inv (me: Principal) (sid: Nat)(st: ServerState) (tr: ProofTrace) :=
  match st with
  | .ServerFinishState k_s =>
    k_s.Invariant tr ∧
    (k_s.label tr).canFlow (server_label me) tr.erase

end

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has DiffieHellman.invariants] (sk: Bytes):
  HoareTriplePure
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

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has DiffieHellman.invariants] (pk sk: Bytes):
  HoareTriplePure
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

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has Signature.invariants] (sk: Bytes):
  HoareTriplePure
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

instance (sk nonce msg: Bytes): HasGhostArgumentType (Signature.sign sk nonce msg) Usage
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

instance (sk nonce msg: Bytes): HasGhostMetaprogram (Signature.sign sk nonce msg) signMetaprog
where
  dummy := ()

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has Signature.invariants] (sk nonce msg: Bytes) (skUsg: Usage):
  HoareTriplePureGhost
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

instance (vkey msg sig: Bytes): HasGhostArgumentType (Signature.verify vkey msg sig) Usage
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

instance (vkey msg sig: Bytes): HasGhostMetaprogram (Signature.verify vkey msg sig) verifyMetaprog
where
  dummy := ()

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has Signature.invariants] (vkey msg sig: Bytes) (skUsg: Usage):
  HoareTriplePureGhost
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

instance [TraceTypes] [BytesInvariants] [BytesInvariants.Has Hash.invariants] (b: Bytes):
  HoareTriplePure
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

instance:
  HoareTriple
    (new_sid me)
    (fun _ => True)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (set_client_state me sid st)
    (fun tr => client_state_inv me sid st tr)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (get_client_state me sid)
    (fun _ => True)
    (fun st tr => client_state_inv me sid st tr)
  where
    pf := sorry

instance:
  HoareTriple
    (set_server_state me sid st)
    (fun tr => server_state_inv me sid st tr)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (get_server_state me sid)
    (fun _ => True)
    (fun st tr => server_state_inv me sid st tr)
  where
    pf := sorry

instance:
  HoareTriple
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

def event_pred (me: Principal) (ev: SignedDHEvent) (tr: ProofTrace) :=
  match ev with
  | .ClientInitiateEvent x_pk => (
    x_pk.Invariant tr ∧
    x_pk.dhSkLabel tr = client_label me
  )
  | .ServerFinishEvent x_pk _y_pk k_s => (
    k_s.Invariant tr ∧
    x_pk.Invariant tr ∧
    k_s.label tr = (server_label me).join (x_pk.dhSkLabel tr)
  )
  | .ClientFinishEvent server x_pk y_pk k_c => (
    (
      event_logged server (.ServerFinishEvent x_pk y_pk k_c) tr ∧
      k_c.Invariant tr ∧
      k_c.label tr = (client_label me).join (server_label server)
    ) ∨ (long_term_label server).isCorrupt tr.erase
  )

instance:
  HoareTriple
    (log_event who ev)
    (fun tr => event_pred who ev tr)
    (fun () tr => event_logged who ev tr)
  where
    pf := sorry

@[grind→]
axiom event_logged_at_implies_event_pred
  (who: Principal) (ev: SignedDHEvent) (i: Nat) (tr: ProofTrace):
    event_logged_at who ev i tr →
    tr.Invariant →
    event_pred who ev (tr.prefix i)

end

namespace SignedDH

section Specification

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]

def client_initiate (me: Principal): Traceful (Nat × Nat) := do
  let x_sk ← Random.genRand 32
  let x_pk := DiffieHellman.dh_pk x_sk

  log_event me (.ClientInitiateEvent x_pk)
  let sid ← new_sid me
  set_client_state me sid (.ClientInitiateState x_sk)
  let msg_ts ← Network.sendMessage (serialize ({ x_pk } : ClientMessage))
  pure (sid, msg_ts)

noncomputable
def server_receive (me: Principal) (msg_ts: Nat) : Traceful (Nat × Nat) := do
  let msg_bytes ← Network.receiveMessage msg_ts
  let msg: ClientMessage ← parse msg_bytes
  let x_pk := msg.x_pk
  let my_sig_key ← get_private_key me

  let y_sk ← Random.genRand 32
  let y_pk := DiffieHellman.dh_pk y_sk
  let k_s := Hash.hash (DiffieHellman.dh x_pk y_sk)
  let sig_nonce ← Random.genRand 32
  let sig := Signature.sign my_sig_key sig_nonce (serialize ({x_pk, y_pk}: SigInput))

  log_event me (.ServerFinishEvent x_pk y_pk k_s)
  let sid ← new_sid me
  set_server_state me sid (.ServerFinishState k_s)
  let msg_ts ← Network.sendMessage (serialize ({ y_pk, sig } : ServerMessage))
  pure (sid, msg_ts)

noncomputable
def client_finish (me: Principal) (server: Principal) (msg_ts: Nat) (sid: Nat) : Traceful Unit := do
  let msg_bytes ← Network.receiveMessage msg_ts
  let msg: ServerMessage ← parse msg_bytes

  let my_state ← get_client_state me sid
  let .ClientInitiateState x_sk := my_state
    | OptionT.fail

  let server_vk ← get_public_key server

  let x_pk := DiffieHellman.dh_pk x_sk
  guard (Signature.verify server_vk (serialize ({ x_pk, y_pk := msg.y_pk }: SigInput)) msg.sig)
  let k_c := Hash.hash (DiffieHellman.dh msg.y_pk x_sk)

  log_event me (.ClientFinishEvent server x_pk msg.y_pk k_c)
  set_client_state me sid (.ClientFinishState k_c)

end Specification

section SecurityTheorems

variable [TraceInvariant] [BytesInvariants] [BytesInvariantsProofs]
variable [BaseAttackerKnowledge] [AttackerKnowledge] [BaseAttackerKnowledgeTheorem] [AttackerKnowledgeTheorem]

theorem client_auth:
  event_logged_at client (.ClientFinishEvent server x_pk y_pk k) time tr →
  tr.Invariant → -- reachable
  (
    let tr_before := tr.prefix time
    event_logged server (.ServerFinishEvent x_pk y_pk k) tr_before  ∨
    (long_term_label server).isCorrupt tr_before.erase
  )
  := by
    intro h_ev h_trinv
    have := event_logged_at_implies_event_pred _ _ _ _ h_ev h_trinv
    simp [event_pred] at this
    grind

theorem client_secrecy:
  k.AttackerKnows tr.erase →
  event_logged_at client (.ClientFinishEvent server x_pk y_pk k) time tr →
  tr.Invariant → -- reachable
  (
    let tr_before := tr.prefix time
    (long_term_label server).isCorrupt tr_before.erase ∨
    (client_label client).isCorrupt tr.erase ∨
    (server_label server).isCorrupt tr.erase
  )
  := by
    intro h_pub h_ev h_trinv
    have h_ev := event_logged_at_implies_event_pred _ _ _ _ h_ev h_trinv
    simp [event_pred] at h_ev
    grind

end SecurityTheorems

namespace TestGrindAnnot

variable [TraceInvariant]
variable [BytesInvariants] [BytesInvariantsProofs]

variable [TraceInvariant.Has Network.Invariant]
variable [TraceInvariant.Has Random.Invariant]
variable [BytesInvariants.Has DiffieHellman.invariants]
variable [BytesInvariants.Has Hash.invariants]
variable [BytesInvariants.Has Signature.invariants]
variable [BytesInvariants.Has Random.invariants]

-- Test for a more automatic feeling
attribute [grind] event_pred
attribute [grind] client_state_inv
attribute [grind] server_state_inv
attribute [grind] Signature.SignPred.pred
attribute [grind] instSignPred

@[instance]
theorem client_initiate.spec:
  HoareTriple
    (client_initiate me)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold client_initiate
  step with ⟨ client_label me, Usage.nothing ⟩
  step
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
  step with ⟨ server_label me, Usage.nothing ⟩
  step
  hoist
  step
  step
  step with ⟨ Label.secret, Usage.nothing ⟩
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
  case h_1 x_sk h_x_sk =>
    step
    step
    step
    hoist
    step
    step
    step
    step
    grind
  · step
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
  n := 2
  entries
  | 0 => Network.ExecEntryT
  | 1 => Random.ExecEntryT

instance: ExecTraceTypes.Has Network.ExecEntryT := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 0))
instance: ExecTraceTypes.Has Random.ExecEntryT := inferInstanceAs (ExecTraceTypes.Has (ExecTraceTypes.entries 1))

instance: TraceTypes where
  proofEntries
  | 0 => Network.ProofEntryT
  | 1 => Random.ProofEntryT
  funs
  | 0 => Network.ProofEntryFunc
  | 1 => Random.ProofEntryFunc

instance: TraceTypes.Has Network.ProofEntryFunc := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 0))
instance: TraceTypes.Has Random.ProofEntryFunc := inferInstanceAs (TraceTypes.Has (TraceTypes.funs 1))

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

instance: TraceInvariant.Has Network.Invariant := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 0))
instance: TraceInvariant.Has Random.Invariant := inferInstanceAs (TraceInvariant.Has (TraceInvariant.invs 1))

instance: BaseAttackerKnowledge where
  attackerKnows
  | 0 => Network.baseAttackerKnowledge
  | 1 => Random.baseAttackerKnowledge

-- Has trace attacker knowledge?

instance: BaseAttackerKnowledgeTheorem where
  pfs
  | 0 => Network.baseAttackerKnowledgeTheorem
  | 1 => Random.baseAttackerKnowledgeTheorem

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

/--
info: 'test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Test.comparseExists,
 Test.event_logged_at,
 Test.SigInput.isWellFormedLemma,
 DY.Trace.MonotoneLemmas.event_logged_at_later]
-/
#guard_msgs in
#print axioms test
