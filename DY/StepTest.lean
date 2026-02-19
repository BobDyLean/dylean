import DY.Trace
import DY.Bytes
import DY.Step

open DY

namespace StepTest

variable [TraceInvariant]
variable [BytesFunctor]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

def hash (b: Bytes): Bytes := sorry
def test_publishable (b: Bytes): Bool := sorry

instance:
  HoareTriplePure
    (hash b)
    (fun tr => b.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = b.label tr
    )
  where
    pf := sorry

def mk_rand (len:Nat) : Traceful Bytes := sorry
def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message (n:Nat) : Traceful Bytes := sorry

abbrev is_knowable_by (b: Bytes) (l: Label) (tr: ProofTrace): Prop :=
  b.Invariant tr ∧
  (b.label tr).canFlow l tr.erase

set_option trace.Step true

instance:
  HoareTriple
    (pure x: Traceful a)
    (fun _ => True)
    (fun res _ => res = x)
  where
    pf := sorry

instance: HasGhostArgumentType (mk_rand len) Label where
  dummy := ()

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
    (fun tr => b.Invariant tr)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (receive_message n)
    (fun _ => True) (fun b tr => b.Publishable tr)
  where
    pf := sorry

instance:
  HoareTriplePure
    (test_publishable b)
    (fun _ => True) (fun res tr => res → b.Publishable tr)
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
    (fun tr => b.Publishable tr)
    (fun res tr => res.Publishable tr)
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

end StepTest
