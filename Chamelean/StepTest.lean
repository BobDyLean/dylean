import Chamelean.Trace
import Chamelean.Step

open Chamelean

namespace Test

def hash (b: Bytes): Bytes := sorry
def test_publishable (b: Bytes): Bool := sorry

instance:
  HoareTriplePure
    (hash b)
    (fun tr => bytes_invariant b tr)
    (fun res tr =>
      bytes_invariant res tr ∧
      get_label res tr = get_label b tr
    )
  where
    pf := sorry

def mk_rand (len:Nat) : Traceful Bytes := sorry
def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message (n:Nat) : Traceful Bytes := sorry

abbrev is_knowable_by (b: Bytes) (l: Label) (tr: ProofTrace): Prop :=
  bytes_invariant b tr ∧
  (get_label b tr).canFlow l tr

set_option trace.Step true

instance:
  HoareTriple
    (pure x: Traceful a)
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

instance:
  HoareTriplePureBool
    (test_publishable b)
    (fun _ => True) (fun tr => is_publishable b tr)
  where
    pf := sorry


def test (b:Bytes) (b2: Bytes): Traceful Bytes := do
  let msg1 ← receive_message 0
  let r ← mk_rand 32
  let hb := hash b
  send_message (hash r)
  send_message hb
  send_message msg1
  guard (test_publishable b2)
  send_message b2
  pure msg1

instance:
  HoareTriple
    (test b b2)
    (fun tr => is_publishable b tr)
    (fun res tr => is_publishable res tr)
where
  pf := by
    unfold test
    step
    step with ⟨ Label.pub ⟩
    step_intro -- will do proofs on hb later
    hoist
    step
    step
    step_let hb
    step
    step
    step
    step
    step
    grind

end Test
