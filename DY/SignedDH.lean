import DY.Trace
import DY.Step
import DY.Bytes.Type
import DY.Bytes.Invariants
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.Hash
import DY.EquationalTheory.Sign

open DY

namespace Test

variable [BytesFunctor]
variable [BytesInvariants]

variable [BytesFunctor.Has Hash.Hash]
variable [BytesInvariants.Has Hash.Hash.invariants]

variable [BytesFunctor.Has Signature.SubF]

instance:
  HoareTriple
    (pure x: Traceful a)
    (fun _ => True)
    (fun res _ => res = x)
  where
    pf := sorry

instance:
  HoareTriple
    (OptionT.fail: Traceful a)
    (fun _ => True)
    (fun _ _ => True)
  where
    pf := sorry

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

@[simp]
theorem parse_serialize_inv_grind [ParseableSerializeable a] (x: a):
  ParseableSerializeable.parse (serialize x) = some x
  := by
  exact (parse_serialize_inv x)

grind_pattern parse_serialize_inv_grind => serialize x

def formatRel [ParseableSerializeable a] (buf: Bytes) (x: a) :=
  buf = serialize x

instance [ParseableSerializeable a]:
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

def isWellFormed [ParseableSerializeable a] (pre: Bytes → τ → Prop) (x: a) (tr: τ): Prop :=
  pre (serialize x) tr

theorem isWellFormedFormatRel [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  formatRel buf x →
  (pre buf tr = isWellFormed pre x tr)
  := by
    grind [isWellFormed, formatRel]

theorem isWellFormedFormatRelBytesInvariant [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Invariant tr = isWellFormed Bytes.Invariant x tr)
  := isWellFormedFormatRel Bytes.Invariant

grind_pattern isWellFormedFormatRelBytesInvariant => formatRel buf x, buf.Invariant tr

theorem isWellFormedFormatRelIsPublishable [ParseableSerializeable a]:
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

instance: BytesCompatible Bytes.Invariant where
  dummy := ()

instance: BytesCompatible Publishable where
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

instance : ParseableSerializeable SigInput := sorry

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

def _root_.DY.Trace.prefix (tr: Trace α) (i: Nat): Trace α := sorry
axiom prefix_le (tr: Trace α) (i: Nat): (tr.prefix i) ≤ tr
grind_pattern prefix_le => tr.prefix i

axiom event_logged_at (who: Principal) (ev: SignedDHEvent) (i: Nat) (tr: ProofTrace): Prop
abbrev event_logged (who: Principal) (ev: SignedDHEvent) (tr: ProofTrace) :=
  ∃ i, event_logged_at who ev i tr

namespace DY -- ???
@[grind→]
axiom _root_.DY.Trace.MonotoneLemmas.event_logged_at_later (who: Principal) (ev: SignedDHEvent) (i: Nat) (tr1 tr2: ProofTrace): tr1 ≤ tr2 → event_logged_at who ev i tr1 → event_logged_at who ev i tr2
end DY

def dh_pk (sk: Bytes): Bytes := sorry
def dh (sk: Bytes) (pk: Bytes): Bytes := sorry
-- def vk (sk: Bytes): Bytes := sorry
-- def sign (sk: Bytes) (nonce: Bytes) (msg: Bytes): Bytes := sorry
-- def verify (vk: Bytes) (msg: Bytes) (sig: Bytes): Bool := sorry

-- invariants

def client_label (me: Principal): Label := sorry
def server_label (me: Principal): Label := sorry
def long_term_label (me: Principal): Label := sorry


structure LongTermKeyUsage where
  principal: Principal

instance : ParseableSerializeable LongTermKeyUsage := sorry

@[grind]
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

instance: Signature.SignPred where
  pred skUsg vk msg tr :=
    ∃ server, skUsg = mk_long_term_usage server ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) => (
        ∃ y_sk,
          msg.y_pk = dh_pk y_sk ∧
          y_sk.label tr = server_label server ∧
          event_logged server (.ServerFinishEvent msg.x_pk msg.y_pk (Hash.hash (dh y_sk msg.x_pk))) tr
      )
    )
  pred_later := sorry

variable [BytesInvariants.Has Signature.invariants]

def client_state_inv (me: Principal) (sid: Nat) (st: ClientState) (tr: ProofTrace) :=
  match st with
  | .ClientInitiateState x_sk =>
    x_sk.Invariant tr ∧
    x_sk.label tr = client_label me ∧
    True -- usage
  | .ClientFinishState k_c =>
    k_c.Invariant tr ∧
    (k_c.label tr).canFlow (client_label me) tr

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
    (k_s.label tr).canFlow (server_label me) tr

instance:
  HoareTriplePure
    (dh_pk sk)
    (fun tr => sk.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
  where
    pf := sorry

def get_dh_label (pk: Bytes) (tr: ProofTrace): Label := sorry

@[grind =]
theorem get_dh_label_lemma (sk: Bytes) (tr: ProofTrace):
  get_dh_label (dh_pk sk) tr = sk.label tr
  := by sorry

axiom _root_.DY.Trace.MonotoneLemmas.get_dh_label_later (b:Bytes) (tr1 tr2: ProofTrace): b.Invariant tr1 → tr1 ≤ tr2 → get_dh_label b tr1 = get_dh_label b tr2

axiom dh_eq (sk1 sk2: Bytes): dh sk1 (dh_pk sk2) = dh sk2 (dh_pk sk1)
grind_pattern dh_eq => dh sk1 (dh_pk sk2), dh sk2 (dh_pk sk1)

-- TODO scoped
grind_pattern _root_.DY.Trace.MonotoneLemmas.get_dh_label_later =>
  b.Invariant tr1, tr1 ≤ tr2, get_dh_label b tr1

instance:
  HoareTriplePure
    (dh sk pk)
    (fun tr =>
      sk.Invariant tr ∧
      pk.Publishable tr
      -- and usage
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.join (sk.label tr) (get_dh_label pk tr)
      -- and usage
    )
  where
    pf := sorry

instance (sk: Bytes):
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
    pf := sorry

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
    let hasUsageToUnify ← Lean.Meta.mkAppOptM ``Bytes.HasUsage #[none, none, none, sk_mvar, usg_mvar, tr_mvar]
    trace[Step] "gonna find {hasUsageToUnify} in assumptions"
    let .mvar hasUsageMvar ← Lean.Meta.mkFreshExprMVar hasUsageToUnify
      | throwError ""
    hasUsageMvar.assumption

instance (sk nonce msg: Bytes): HasGhostMetaprogram (Signature.sign sk nonce msg) signMetaprog
where
  dummy := ()

instance (sk nonce msg: Bytes) (skUsg: Usage):
  HoareTriplePureGhost
    (Signature.sign sk nonce msg)
    (skUsg)
    (fun tr =>
      sk.Invariant tr ∧
      nonce.Invariant tr ∧
      msg.Invariant tr ∧
      sk.HasUsage skUsg tr ∧
      --nonce `has_usage tr` SigNonce /\
      (sk.label tr).canFlow (nonce.label tr) tr ∧
      (
        (
          skUsg.type = "SigKey" ∧
          Signature.SignPred.pred skUsg (Signature.vk sk) msg tr
        ) ∨ (
          (sk.label tr).canFlow Label.pub tr
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
    let hasUsageToUnify ← Lean.Meta.mkAppOptM ``Bytes.SignkeyHasUsage #[none, none, none, vkey_mvar, usg_mvar, tr_mvar]
    trace[Step] "gonna find {hasUsageToUnify} in assumptions"
    let .mvar hasUsageMvar ← Lean.Meta.mkFreshExprMVar hasUsageToUnify
      | throwError ""
    hasUsageMvar.assumption

instance (vkey msg sig: Bytes): HasGhostMetaprogram (Signature.verify vkey msg sig) verifyMetaprog
where
  dummy := ()

instance (vkey msg sig: Bytes) (skUsg: Usage):
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
          (vkey.signkeyLabel tr).canFlow Label.pub tr
        )
      )
    )
  where
    pf := by
      simp
      intros
      apply Signature.verify.Invariant vkey msg sig skUsg <;>
      grind

instance (b: Bytes):
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

def gen_rand (len: Nat) : Traceful Bytes := sorry
def send_message (b:Bytes) : Traceful Nat := sorry
def receive_message (ts: Nat): Traceful Bytes := sorry
def new_sid (me: Principal): Traceful Nat := sorry
def set_client_state (me: Principal) (sid: Nat) (st: ClientState): Traceful Unit := sorry
def get_client_state (me: Principal) (sid: Nat): Traceful ClientState  := sorry
def set_server_state (me: Principal) (sid: Nat) (st: ServerState): Traceful Unit := sorry
def get_server_state (me: Principal) (sid: Nat): Traceful ServerState  := sorry
def get_public_key (who: Principal): Traceful Bytes := sorry
def get_private_key (who: Principal): Traceful Bytes := sorry
def log_event (who: Principal) (ev: SignedDHEvent): Traceful Unit := sorry

instance: HasGhostArgumentType (gen_rand len) Label
where
  dummy := ()

instance:
  HoareTripleGhost
    (gen_rand len)
    lab
    (fun _ => True)
    (fun b tr =>
      b.Invariant tr ∧
      b.label tr = lab
      -- usage, length
    )
  where
    pf := sorry

instance:
  HoareTriple
    (send_message b)
    (fun tr => b.Publishable tr)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (receive_message ts)
    (fun _ => True)
    (fun b tr => b.Publishable tr)
  where
    pf := sorry

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
    get_dh_label x_pk tr = client_label me
  )
  | .ServerFinishEvent x_pk _y_pk k_s => (
    k_s.Invariant tr ∧
    x_pk.Invariant tr ∧
    k_s.label tr = (server_label me).join (get_dh_label x_pk tr)
  )
  | .ClientFinishEvent server x_pk y_pk k_c => (
    (
      event_logged server (.ServerFinishEvent x_pk y_pk k_c) tr ∧
      k_c.Invariant tr ∧
      k_c.label tr = (client_label me).join (server_label server)
    ) ∨ (long_term_label server).isCorrupt tr
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
    tr.invariant →
    event_pred who ev (tr.prefix i)

-- signed dh

namespace SignedDH

def client_initiate (me: Principal): Traceful (Nat × Nat) := do
  let x_sk ← gen_rand 32
  let x_pk := dh_pk x_sk

  log_event me (.ClientInitiateEvent x_pk)
  let sid ← new_sid me
  set_client_state me sid (.ClientInitiateState x_sk)
  let msg_ts ← send_message (serialize ({ x_pk } : ClientMessage))
  pure (sid, msg_ts)

def server_receive (me: Principal) (msg_ts: Nat) : Traceful (Nat × Nat) := do
  let msg_bytes ← receive_message msg_ts
  let msg: ClientMessage ← parse msg_bytes
  let x_pk := msg.x_pk
  let my_sig_key ← get_private_key me

  let y_sk ← gen_rand 32
  let y_pk := dh_pk y_sk
  let k_s := Hash.hash (dh y_sk x_pk)
  let sig_nonce ← gen_rand 32
  let sig := Signature.sign my_sig_key sig_nonce (serialize ({x_pk, y_pk}: SigInput))

  log_event me (.ServerFinishEvent x_pk y_pk k_s)
  let sid ← new_sid me
  set_server_state me sid (.ServerFinishState k_s)
  let msg_ts ← send_message (serialize ({ y_pk, sig } : ServerMessage))
  pure (sid, msg_ts)

def client_finish (me: Principal) (server: Principal) (msg_ts: Nat) (sid: Nat) : Traceful Unit := do
  let msg_bytes ← receive_message msg_ts
  let msg: ServerMessage ← parse msg_bytes

  let my_state ← get_client_state me sid
  let .ClientInitiateState x_sk := my_state
    | OptionT.fail

  let server_vk ← get_public_key server

  let x_pk := dh_pk x_sk
  guard (Signature.verify server_vk (serialize ({ x_pk, y_pk := msg.y_pk }: SigInput)) msg.sig)
  let k_c := Hash.hash (dh x_sk msg.y_pk)

  log_event me (.ClientFinishEvent server x_pk msg.y_pk k_c)
  set_client_state me sid (.ClientFinishState k_c)

instance:
  HoareTriple
    (client_initiate me)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    unfold client_initiate
    step with ⟨ client_label me ⟩
    step
    step by grind [event_pred]
    step
    step by grind [client_state_inv]
    step
    step
    grind

instance:
  HoareTriple
    (server_receive me msg_ts)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    unfold server_receive
    step
    step
    step_intro
    step
    step with ⟨ server_label me ⟩
    step
    hoist
    step
    step
    step with ⟨ Label.secret ⟩
    hoist
    step_intro
    -- for monotonicity TODO: how to infer Publishable automatically?
    have h_sig_msg: sig_msg.Publishable tr := by grind
    -- interesting stuff: we will prove things on `sig` later on,
    -- because we need to log the event before
    step_intro
    step by grind [event_pred]
    step_let sig with ⟨ mk_long_term_usage me ⟩ by
      simp only [Signature.SignPred.pred]
      grind
    step
    step by grind [server_state_inv]
    step
    step
    grind

instance:
  HoareTriple
    (client_finish me server msg_ts sid)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    unfold client_finish
    step
    step
    step
    split
    case h_1 x_sk h_x_sk =>
      -- this is useful to monotonize hypothesis
      -- (probably best as a grind pattern on client_state_inv but well)
      have h_x_sk': x_sk.Invariant tr := by grind [client_state_inv]
      step
      step
      step with ⟨ mk_long_term_usage server ⟩
      hoist
      step
      step
      step by
        simp_all [event_pred, Signature.SignPred.pred]
        grind [event_pred, client_state_inv]
      step by grind [client_state_inv]
      grind
    · step
      grind

theorem client_auth:
  event_logged_at client (.ClientFinishEvent server x_pk y_pk k) time tr →
  tr.invariant → (
    let tr_before := tr.prefix time
    event_logged server (.ServerFinishEvent x_pk y_pk k) tr_before  ∨
    (long_term_label server).isCorrupt tr_before
  )
  := by
    intro h_ev h_trinv
    have := event_logged_at_implies_event_pred _ _ _ _ h_ev h_trinv
    simp [event_pred] at this
    grind

theorem client_secrecy:
  k.Publishable tr → -- attacker_knows
  event_logged_at client (.ClientFinishEvent server x_pk y_pk k) time tr →
  tr.invariant → (
    let tr_before := tr.prefix time
    (long_term_label server).isCorrupt tr_before ∨
    (client_label client).isCorrupt tr ∨
    (server_label server).isCorrupt tr
  )
  := by
    intro h_pub h_ev h_trinv
    have h_ev := event_logged_at_implies_event_pred _ _ _ _ h_ev h_trinv
    simp [event_pred] at h_ev
    grind


namespace TestGrindAnnot

-- Test for a more automatic feeling
attribute [grind] event_pred
attribute [grind] client_state_inv
attribute [grind] server_state_inv
attribute [grind] Signature.SignPred.pred
attribute [grind] instSignPred

instance:
  HoareTriple
    (client_initiate me)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    unfold client_initiate
    step with ⟨ client_label me ⟩
    step
    step
    step
    step
    step
    step
    grind

instance:
  HoareTriple
    (server_receive me msg_ts)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    unfold server_receive
    step
    step
    step_intro
    step
    step with ⟨ server_label me ⟩
    step
    hoist
    step
    step
    step with ⟨ Label.secret ⟩
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

instance:
  HoareTriple
    (client_finish me server msg_ts sid)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
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

abbrev SubF.internal: (id: Fin 2) → (Type → Type)
  | 0 => Hash.Hash
  | 1 => Signature.SubF

abbrev SubF := BytesFunctor.combine SubF.internal

instance: ∀ id, SubBytesFunctor (SubF.internal id)
  | 0 => inferInstance
  | 1 => inferInstance

instance: BytesFunctor.HasStep Hash.Hash SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 0) SubF)
instance: BytesFunctor.HasStep Signature.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 1) SubF)

instance: BytesFunctor where
  BytesF := SubF

instance: BytesFunctor.Has SubF := inferInstanceAs (BytesFunctor.Has BytesF)

example: BytesFunctor.Has Hash.Hash := inferInstance
example: BytesFunctor.Has Signature.SubF := inferInstance

def attackerKnowledge.internal (id: Fin 2): SubAttackerKnowledge (SubF.internal id) :=
  match id with
  | 0 => Hash.attKnowsHash
  | 1 => Signature.attackerKnowledge

def attackerKnowledge: SubAttackerKnowledge SubF :=
  SubAttackerKnowledge.combine attackerKnowledge.internal

instance: AttackerKnowledge.HasStep Hash.attKnowsHash attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Signature.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledge where
  attackerKnowledge

instance: AttackerKnowledge.Has attackerKnowledge := inferInstanceAs (AttackerKnowledge.Has AttackerKnowledge.attackerKnowledge)

example: AttackerKnowledge.Has Hash.attKnowsHash := inferInstance
example: AttackerKnowledge.Has Signature.attackerKnowledge := inferInstance

def invariants.internal: (id: Fin 2) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => Hash.Hash.invariants
  | 1 => Signature.invariants

abbrev invariants: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

instance [BytesInvariants]: BytesInvariants.HasStep Hash.Hash.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Signature.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)

instance: BytesInvariants where
  invs := invariants

instance: BytesInvariants.Has invariants := inferInstance

example: BytesInvariants.Has Hash.Hash.invariants := inferInstance
example: BytesInvariants.Has Signature.invariants := inferInstance

instance: (id: Fin 2) → SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem Hash.attKnowsHash)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem Signature.attackerKnowledge)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledgeTheorem where
  inst := inferInstanceAs (SubAttackerKnowledgeTheorem attackerKnowledge)

example (b: Bytes) (tr: ProofTrace) :
    tr.invariant →
    Bytes.AttackerKnows b tr →
    b.Publishable tr
  := by
    apply Bytes.AttackerKnows_implies_Publishable
