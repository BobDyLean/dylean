import Init.Control.Lawful.Basic

namespace Chamelean.Trace

axiom Bytes: Type 0

inductive TraceEntry (a:Type) where
  | rand_gen: a -> TraceEntry a
  | send_msg: Bytes -> TraceEntry a
  | log_event: TraceEntry a
  -- TODO

inductive Trace (a:Type) where
  | nil: Trace a
  | snoc: Trace a -> TraceEntry a -> Trace a

def map_trace_entry
  (f: a -> b) (e: TraceEntry a)
  : TraceEntry b
  :=
  match e with
  | .rand_gen pf => .rand_gen (f pf)
  | .send_msg msg => .send_msg msg
  | .log_event => .log_event

def map_trace
  (f: a -> b) (tr: Trace a)
  : Trace b
  :=
  match tr with
  | .nil => .nil
  | .snoc tr_before e => .snoc (map_trace f tr_before) (map_trace_entry f e)

instance : Functor Trace where
  map := map_trace

instance : LawfulFunctor Trace where
  map_const := by
    intros
    simp [Functor.mapConst, Functor.map]
  id_map := by
    intros α tr
    simp [Functor.map]
    induction tr with
    | nil =>
      simp [map_trace]
    | snoc tr_before e =>
      simp [map_trace, map_trace_entry]
      grind
  comp_map := by
    intros α β γ g h tr
    simp [Functor.map]
    induction tr with
    | nil =>
      simp [map_trace]
    | snoc tr_before e =>
      simp [map_trace, map_trace_entry]
      grind

inductive LETrace : Trace a -> Trace a -> Prop where
  | equal: (tr1 = tr2) -> LETrace tr1 tr2
  | extend: (e: TraceEntry a) -> LETrace tr1 tr2 -> LETrace tr1 (.snoc tr2 e)

instance : LE (Trace a) where
  le := LETrace

theorem trace_le_trans
  (tr1: Trace a) (tr2: Trace a) (tr3: Trace a)
  : tr1 ≤ tr2 → tr2 ≤ tr3 → tr1 ≤ tr3
  := by
    intros hxy hyz
    induction hyz with
    | equal => simp_all
    | extend e _ ih =>
      exact (LETrace.extend e ih)

-- grind_pattern trace_le_trans => tr1 ≤ tr2, tr1 ≤ tr3

instance : Trans (· ≤ · : Trace a → Trace a → Prop) (· ≤ ·) (· ≤ ·) where
  trans := by
    intros x y z
    exact trace_le_trans x y z
  /-by
    intros x y z hxy hyz
    induction hyz with
    | equal => simp_all
    | extend e _ ih =>
      exact (LETrace.extend e ih)
      -/

abbrev ExecutionTrace := Trace Unit

def Label := ExecutionTrace -> Prop

abbrev ProofTrace := Trace Label -- TODO and usage

def trace_rel (tr_exec: ExecutionTrace) (tr_proof: ProofTrace) :=
  tr_exec = Functor.mapConst () tr_proof

abbrev Traceful := StateT ExecutionTrace Id
abbrev TracefulErr := OptionT Traceful
abbrev Err := OptionT Id

axiom trace_invariant: ProofTrace -> Prop

def preserves_invariant_on
  (f: Traceful a)
  (post: a -> ProofTrace -> Prop)
  (tr_exec: ExecutionTrace) (tr_proof: ProofTrace)
  : Prop
  :=
  let (x, tr_exec') := (f.run tr_exec).run
  ∃ tr_proof',
    post x tr_proof' ∧
    trace_invariant tr_proof' ∧
    trace_rel tr_exec' tr_proof' ∧
    tr_proof ≤ tr_proof'

def preserves_invariant
  (f: Traceful a)
  (pre: ProofTrace -> Prop) (post: a -> ProofTrace -> Prop)
  : Prop
  :=
  ∀ tr_exec tr_proof,
  pre tr_proof →
  trace_invariant tr_proof →
  trace_rel tr_exec tr_proof →
  preserves_invariant_on f post tr_exec tr_proof

theorem bind_preserves_invariant_on
  {a b}
  (x: Traceful a) (f: a -> Traceful b)
  (post_f: b -> ProofTrace -> Prop)
  (tr_exec: ExecutionTrace) (tr_proof: ProofTrace)
  {pre_x post_x}
  (pf_x: preserves_invariant x pre_x post_x)
  (pf_tr_inv: trace_invariant tr_proof)
  (pf_tr_rel: trace_rel tr_exec tr_proof)
  (pf_pre_x: pre_x tr_proof)
  (pf_next: ∀ tr_exec_mid tr_proof_mid x',
    post_x x' tr_proof_mid →
    trace_invariant tr_proof_mid →
    trace_rel tr_exec_mid tr_proof_mid →
    tr_proof ≤ tr_proof_mid → (
      preserves_invariant_on (f x') (post_f) tr_exec_mid tr_proof_mid
    )
  )
  : preserves_invariant_on (x >>= f) (post_f) tr_exec tr_proof
  := by
    simp only [preserves_invariant_on, StateT.run_bind, Id.run_bind]
    grind [trace_le_trans, preserves_invariant_on, preserves_invariant]

theorem finish_preserves_invariant_on
  {a}
  (x: Traceful a)
  (post: a -> ProofTrace -> Prop)
  (tr_exec: ExecutionTrace) (tr_proof: ProofTrace)
  {pre_x post_x}
  (pf_x: preserves_invariant x pre_x post_x)
  (pf_tr_inv: trace_invariant tr_proof)
  (pf_tr_rel: trace_rel tr_exec tr_proof)
  (pf_pre_x: pre_x tr_proof)
  (pf_next: ∀ tr_exec_mid tr_proof_mid x',
    post_x x' tr_proof_mid →
    trace_invariant tr_proof_mid →
    trace_rel tr_exec_mid tr_proof_mid →
    tr_proof ≤ tr_proof_mid → (
      post x' tr_proof_mid
    )
  )
  : preserves_invariant_on x post tr_exec tr_proof
  := by
    grind [preserves_invariant_on, preserves_invariant]

def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message: Traceful Bytes := sorry

axiom bytes_invariant (b:Bytes) (tr: ProofTrace): Prop
axiom is_publishable (b:Bytes) (tr: ProofTrace): Prop

axiom is_publishable_implies_bytes_invariant:
  is_publishable b tr → bytes_invariant b tr

axiom send_message_spec:
  preserves_invariant (send_message b)
    (fun tr => bytes_invariant b tr)
    (fun _ _ => True)

axiom receive_message_spec:
  preserves_invariant (receive_message)
    (fun _ => True)
    (fun b tr => is_publishable b tr)

def test: Traceful Unit := do
  let msg ← receive_message
  send_message msg

theorem test_spec:
  preserves_invariant (test)
    (fun _ => True)
    (fun _ _ => True)
  := by
    rw [test, preserves_invariant]
    intros tr_exec tr_proof _ h_tr_inv h_tr_rel
    apply bind_preserves_invariant_on
    · exact receive_message_spec
    · assumption
    · assumption
    · grind
    -- clear h_tr_rel h_tr_inv
    intros tr_exec tr_proof msg
    intros
    apply finish_preserves_invariant_on
    · exact send_message_spec
    · assumption
    · assumption
    · grind [is_publishable_implies_bytes_invariant]
    intros tr_exec tr_proof x
    intros
    trivial

def later_lemmas_enabled (_: Unit): Prop := True
theorem enable_later_lemmas: later_lemmas_enabled () := by simp [later_lemmas_enabled]

axiom is_publishable_later (b:Bytes) (tr1 tr2: ProofTrace) (dummy: Unit): is_publishable b tr1 → tr1 ≤ tr2 → is_publishable b tr2
grind_pattern is_publishable_later => is_publishable b tr1, tr1 ≤ tr2, later_lemmas_enabled dummy

axiom bytes_invariant_later (b:Bytes) (tr1 tr2: ProofTrace) (dummy: Unit): bytes_invariant b tr1 → tr1 ≤ tr2 → bytes_invariant b tr2
grind_pattern bytes_invariant_later => bytes_invariant b tr1, tr1 ≤ tr2, later_lemmas_enabled dummy

def is_monotone (p: ProofTrace → Prop): Prop :=
  ∀ tr1 tr2,
    p tr1 → tr1 ≤ tr2 → p tr2

example: is_monotone (fun tr =>
  is_publishable b1 tr ∨ (
    bytes_invariant b2 tr ∧ (
      match x with
      | none => is_publishable b3 tr
      | some true => bytes_invariant b4 tr
      | some false => bytes_invariant b5 tr
    )
  )) := by
  have := enable_later_lemmas
  grind [is_monotone]

example: is_publishable b tr1 ∧ tr1 ≤ tr2 → is_publishable b tr2 := by
  have := enable_later_lemmas
  grind

end Chamelean.Trace
