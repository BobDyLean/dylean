import Chamelean.Trace
import Chamelean.Step

open Chamelean.Trace

namespace Test

def mk_rand (len:Nat) : Traceful Bytes := sorry
def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message (n:Nat) : Traceful Bytes := sorry

axiom is_knowable_by (b:Bytes) (l:Label) (tr: ProofTrace): Prop

@[scoped grind→]
axiom _root_.Chamelean.Trace.Monotone.is_knowable_by_later (b:Bytes) (l:Label) (tr1 tr2: ProofTrace): Test.is_knowable_by b l tr1 → tr1 ≤ tr2 → Test.is_knowable_by b l tr2

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
    unfold test
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
