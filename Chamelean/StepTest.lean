import Chamelean.Trace
import Chamelean.Step

open Chamelean

namespace Test

def mk_rand (len:Nat) : Traceful Bytes := sorry
def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message (n:Nat) : Traceful Bytes := sorry

abbrev is_knowable_by (b: Bytes) (l: Label) (tr: ProofTrace): Prop :=
  bytes_invariant b tr ∧
  (get_label b tr).canFlow l tr

set_option trace.Step true

instance:
  HoareTriple
    (pure x)
    (fun _ => True)
    (fun res _ => res = x)
  where
    pf := sorry

instance:
  HoareTripleGhost
    (mk_rand len)
    lab
    (fun _ => True)
    (fun b tr => is_knowable_by b lab tr)
  where
    pf := sorry

instance:
  HoareTriple
    (send_message b)
    (fun tr => bytes_invariant b tr)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (receive_message n)
    (fun _ => True) (fun b tr => is_publishable b tr)
  where
    pf := sorry

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
    step with ⟨ Label.pub ⟩
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
