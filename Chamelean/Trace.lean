import Init.Control.Lawful.Basic
import Chamelean.Trace.Type
import Chamelean.Label.Type
import Chamelean.Label

namespace Chamelean

abbrev ExecutionTrace := Trace Unit

abbrev ProofTrace := Trace Label -- TODO and usage

def Trace.erase (tr_proof: ProofTrace): ExecutionTrace :=
  Functor.mapConst () tr_proof

abbrev Traceful := OptionT (StateT ExecutionTrace Id)
abbrev Err := OptionT Id

instance : MonadLift Err Traceful := {
  monadLift := fun x => StateT.pure x.run
}

def Traceful.run (x: Traceful a) (tr: ExecutionTrace): (Option a × ExecutionTrace) :=
  Id.run (StateT.run (OptionT.run x) tr)

-- This is missing from Lean's standard library??
theorem OptionT.run_pure {m : Type u → Type v} [Monad m] {α : Type u} (x : α) :
  OptionT.run (pure x) = some (pure x)
  := rfl

-- This is missing from Lean's standard library??
theorem OptionT.run_bind {m : Type u → Type v} [Monad m] {α β : Type u} (x : OptionT m α) (f : α → OptionT m β) :
  (x >>= f).run = (do
    match (← x.run) with
    | some a => (f a).run
    | none   => pure none
  )
  := rfl


theorem Traceful.run_pure
  (x: a) (tr: ExecutionTrace)
  : Traceful.run (pure x) tr = (some x, tr)
  := by
    rfl

theorem Traceful.run_bind
  (x: Traceful a) (f: a → Traceful b) (tr: ExecutionTrace)
  : Traceful.run (x >>= f) tr = (
    let (opt_x, tr) := x.run tr
    match opt_x with
    | some x => (f x).run tr
    | none => (none, tr)
  )
  := by
    simp only [Traceful.run, OptionT.run_bind, StateT.run_bind, Id.run_bind]
    split
    · simp_all
    · simp_all

axiom Trace.invariant: ProofTrace -> Prop

-- Weakest precondition for Traceful functions
-- (+ relation (≤) between old and new proof trace)
def preserves_invariant_on
  (f: Traceful a)
  (post: a -> ProofTrace -> Prop)
  (tr_proof: ProofTrace)
  : Prop
  :=
  let (opt_x, tr_exec') := f.run tr_proof.erase
  ∃ tr_proof',
    (
      match opt_x with
      | .none => True
      | .some x => post x tr_proof'
    ) ∧
    Trace.invariant tr_proof' ∧
    tr_exec' = tr_proof'.erase ∧
    tr_proof ≤ tr_proof'

-- Hoare triple for Traceful functions
def preserves_invariant
  (f: Traceful a)
  (pre: ProofTrace -> Prop) (post: a -> ProofTrace -> Prop)
  : Prop
  :=
  ∀ tr,
  pre tr →
  Trace.invariant tr →
  preserves_invariant_on f post tr

theorem bind_preserves_invariant_on
  {a b}
  (x: Traceful a) (f: a -> Traceful b)
  (post_f: b -> ProofTrace -> Prop)
  (tr: ProofTrace)
  {pre_x post_x}
  (pf_x: preserves_invariant x pre_x post_x)
  (pf_tr_inv: Trace.invariant tr)
  (pf_pre_x: pre_x tr)
  (pf_next: ∀ tr_mid x',
    post_x x' tr_mid →
    Trace.invariant tr_mid →
    tr ≤ tr_mid → (
      preserves_invariant_on (f x') (post_f) tr_mid
    )
  )
  : preserves_invariant_on (x >>= f) (post_f) tr
  := by
    simp only [preserves_invariant_on, Traceful.run_bind]
    split
    · grind [Trace.trace_le_trans, preserves_invariant_on, preserves_invariant]
    · grind [preserves_invariant_on, preserves_invariant]

theorem finish_preserves_invariant_on
  {a}
  (x: Traceful a)
  (post: a -> ProofTrace -> Prop)
  (tr: ProofTrace)
  {pre_x post_x}
  (pf_x: preserves_invariant x pre_x post_x)
  (pf_tr_inv: Trace.invariant tr)
  (pf_pre_x: pre_x tr)
  (pf_next: ∀ tr_mid x',
    post_x x' tr_mid →
    Trace.invariant tr_mid →
    tr ≤ tr_mid → (
      post x' tr_mid
    )
  )
  : preserves_invariant_on x post tr
  := by
    grind [preserves_invariant_on, preserves_invariant]

def send_message (b:Bytes) : Traceful Nat := sorry
def receive_message (ts: Nat): Traceful Bytes := sorry

axiom bytes_invariant (b:Bytes) (tr: ProofTrace): Prop
axiom get_label (b:Bytes) (tr: ProofTrace): Label

@[scoped grind→]
axiom _root_.Chamelean.Trace.MonotoneLemmas.bytes_invariant_later (b:Bytes) (tr1 tr2: ProofTrace): tr1 ≤ tr2 → bytes_invariant b tr1 → bytes_invariant b tr2

axiom _root_.Chamelean.Trace.MonotoneLemmas.get_label_later (b:Bytes) (tr1 tr2: ProofTrace): bytes_invariant b tr1 → tr1 ≤ tr2 → get_label b tr1 = get_label b tr2

-- TODO scoped
grind_pattern _root_.Chamelean.Trace.MonotoneLemmas.get_label_later =>
  bytes_invariant b tr1, tr1 ≤ tr2, get_label b tr1

abbrev is_publishable (b:Bytes) (tr: ProofTrace): Prop :=
  bytes_invariant b tr ∧
  (get_label b tr).canFlow Label.pub tr

axiom is_publishable_implies_bytes_invariant:
  is_publishable b tr → bytes_invariant b tr

axiom send_message_spec:
  preserves_invariant (send_message b)
    (fun tr => bytes_invariant b tr)
    (fun _ _ => True)

axiom receive_message_spec:
  preserves_invariant (receive_message ts)
    (fun _ => True)
    (fun b tr => is_publishable b tr)

def test: Traceful Nat := do
  let msg ← receive_message 0
  send_message msg

theorem test_spec:
  preserves_invariant (test)
    (fun _ => True)
    (fun _ _ => True)
  := by
    rw [test, preserves_invariant]
    intros tr _ h_tr_inv
    apply bind_preserves_invariant_on
    · exact receive_message_spec
    · assumption
    · grind
    -- clear h_tr_rel h_tr_inv
    intros tr_exec tr msg
    intros
    apply finish_preserves_invariant_on
    · exact send_message_spec
    · assumption
    · grind [is_publishable_implies_bytes_invariant]
    intros tr_exec tr x
    intros
    trivial

def is_monotone (p: ProofTrace → Prop): Prop :=
  ∀ tr1 tr2,
    tr1 ≤ tr2 → p tr1 → p tr2

example: is_monotone (fun tr =>
  is_publishable b1 tr ∨ (
    bytes_invariant b2 tr ∧ (
      match x with
      | none => is_publishable b3 tr
      | some true => bytes_invariant b4 tr
      | some false => bytes_invariant b5 tr
    )
  )) := by
  open Chamelean.Trace.MonotoneLemmas in
  grind [is_monotone]

example: is_monotone (fun tr => is_publishable b tr) := by
  open Chamelean.Trace.MonotoneLemmas in
  unfold is_monotone
  grind [is_monotone]

example: tr1 ≤ tr2 → is_publishable b tr1 → is_publishable b tr2 := by
  open Chamelean.Trace.MonotoneLemmas in
  grind

end Chamelean
