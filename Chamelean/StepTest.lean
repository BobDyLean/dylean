import Chamelean.Trace
import Chamelean.Step

namespace Test

open Chamelean.Trace

def mk_rand (len:Nat) : Traceful Bytes := sorry
def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message (n:Nat) : Traceful Bytes := sorry

axiom is_knowable_by (b:Bytes) (l:Label) (tr: ProofTrace): Prop
axiom is_knowable_by_later (b:Bytes) (l:Label) (tr1 tr2: ProofTrace) (dummy: Unit): is_knowable_by b l tr1 → tr1 ≤ tr2 → is_knowable_by b l tr2
grind_pattern is_knowable_by_later => is_knowable_by b l tr1, tr1 ≤ tr2, later_lemmas_enabled dummy

axiom is_publishable_implies_bytes_invariant:
  is_publishable b tr → bytes_invariant b tr
grind_pattern is_publishable_implies_bytes_invariant => is_publishable b tr

axiom is_knowable_by_implies_bytes_invariant:
  is_knowable_by b l tr → bytes_invariant b tr
grind_pattern is_knowable_by_implies_bytes_invariant => is_knowable_by b l tr

axiom pub: Label
axiom secret: Label

set_option trace.Step true

@[step]
axiom pure_spec:
  preserves_invariant (pure x)
    (fun _ => True)
    (fun res _ => res = x)

@[step]
axiom mk_rand_spec (len: Nat) (lab: Label):
  preserves_invariant (mk_rand len)
    (fun _ => True)
    (fun b tr => is_knowable_by b lab tr)

@[step]
axiom send_message_spec:
  preserves_invariant (send_message b)
    (fun tr => bytes_invariant b tr)
    (fun _ _ => True)

@[step]
axiom receive_message_spec:
  preserves_invariant (receive_message n)
    (fun _ => True)
    (fun b tr => is_publishable b tr)

def test (b:Bytes) : Traceful Bytes := do
  let msg1 ← receive_message 0
  let r ← mk_rand 32
  send_message r
  send_message b
  send_message msg1
  pure msg1

theorem test_spec (b:Bytes) :
  preserves_invariant (test b)
    (fun tr => is_publishable b tr)
    (fun res tr => is_publishable res tr)
  := by
    unfold test preserves_invariant
    intros tr_exec tr_proof _ h_tr_inv h_tr_rel
    step
    · trivial
    step with ⟨ pub ⟩
    · grind
    step
    · grind
    step
    · grind
    step
    · grind
    step
    · trivial
    grind

end Test
