import DY.Trace
import DY.Bytes
import DY.Meta

open DY

namespace StepTest

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
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

example:
  HoareTriple
    (test b b2)
    (fun tr => b.Publishable tr)
    (fun res tr => res.Publishable tr)
:= by
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

set_option trace.Step false

-- Test mark_non_monotone (hypothesis h_msg1 must be dropped)

section NonMonotoneHypothesis

def testNonMonoPre: Traceful Unit := sorry

def testNonMono: Traceful Unit := do
  testNonMonoPre
  let msg ← receive_message 0
  send_message msg

opaque nonMonotoneProperty (tr: ProofTrace): Prop

instance:
  HoareTriple
    (testNonMonoPre)
    (fun tr => nonMonotoneProperty tr)
    (fun _ _ => True)
  where
    pf := sorry

/--
trace: inst✝⁵ : ExecTraceTypes
inst✝⁴ : ProofTraceTypes
inst✝³ : TraceInvariant
inst✝² : BytesFunctor
inst✝¹ : BytesInvariants
inst✝ : BytesInvariantsProofs
tr : ProofTrace
h_inv : Trace.Invariant tr
pre : Step.nonMono (nonMonotoneProperty tr)
⊢ wp
    (do
      testNonMonoPre
      let msg ← receive_message 0
      send_message msg)
    (fun x x_1 => True) tr
---
trace: case pf_next
inst : ExecTraceTypes
inst_1 : ProofTraceTypes
inst_2 : TraceInvariant
inst_3 : BytesFunctor
inst_4 : BytesInvariants
inst_5 : BytesInvariantsProofs
tr : Trace ProofTrace.Entry
h_inv : tr.Invariant
⊢ wp
    (do
      let msg ← receive_message 0
      send_message msg)
    (fun x x_1 => True) tr
-/
#guard_msgs in
example:
HoareTriple
  (testNonMono)
  (fun tr => nonMonotoneProperty tr)
  (fun _ _ => True)
:= by
  unfold testNonMono
  fail_if_success step
  apply HoareTriple.mk; intro tr pre h_inv
  fail_if_success step
  mark_non_monotone pre
  trace_state
  step
  trace_state
  step
  step
  trivial

end NonMonotoneHypothesis


section AdmitMono

-- TODO: no warning about using `sorry`?
/--  -/
#guard_msgs in
example:
HoareTriple
  (testNonMono)
  (fun tr => nonMonotoneProperty tr)
  (fun _ _ => True)
:= by
  set_option step.admitMono true in
  unfold testNonMono
  step
  step
  step
  trivial

end AdmitMono

section UnprovedPrecondition

def testUnprovenPrecondition: Traceful Unit := do
  let msg ← receive_message 0
  send_message msg
  send_message msg

/-- error: unsolved goal in precondition proof -/
#guard_msgs in
example:
HoareTriple
  (testUnprovenPrecondition)
  (fun _ => True)
  (fun _ _ => True)
:= by
  unfold testUnprovenPrecondition
  step
  step
  step by
    exfalso
    simp_all [Bytes.Publishable]
    -- proof is not finished
  trivial

end UnprovedPrecondition

section UnifyGhostArgumentType

def mk_rand_bis (len:Nat) : Traceful Bytes := sorry

instance: HasGhostArgumentType (mk_rand_bis len) ((Bytes → Label) × String) where
  dummy := ()

instance (len: Nat) (lab: Bytes → Label) (usg: String):
  HoareTripleGhost
    (mk_rand_bis len)
    (lab, usg)
    (fun _ => True)
    (fun b tr => is_knowable_by b (lab b) tr)
  where
    pf := sorry

def testUnifyGhostType: Traceful Unit := do
  let b ← mk_rand_bis 32
  send_message b

example:
HoareTriple
  (testUnifyGhostType)
  (fun _ => True)
  (fun _ _ => True)
:= by
  unfold testUnifyGhostType
  step with ⟨ fun _ => Label.pub, "" ⟩
  step
  trivial

end UnifyGhostArgumentType

section IncrementalCleanup
-- Test that we do not introduce useless hypotheses such as:
-- - x: Unit
-- - h: True

def weirdUnitFunction: Traceful Unit := sorry

instance:
  HoareTriple
    (weirdUnitFunction)
    (fun _ => True)
    (fun () _ => True)
  where
    pf := sorry

def testIncrementalCleanup: Traceful Unit := do
  let b ← receive_message 0
  send_message b
  send_message b
  weirdUnitFunction
  send_message b
  send_message b

/--
trace: case pf_next
inst : ExecTraceTypes
inst_1 : ProofTraceTypes
inst_2 : TraceInvariant
inst_3 : BytesFunctor
inst_4 : BytesInvariants
inst_5 : BytesInvariantsProofs
tr : Trace ProofTrace.Entry
h : tr.Invariant
b : Bytes
h_b✝ : b.Publishable tr
⊢ True
-/
#guard_msgs in
example:
HoareTriple
  (testIncrementalCleanup)
  (fun _ => True)
  (fun _ _ => True)
:= by
  unfold testIncrementalCleanup
  step
  step
  step
  step
  step
  step
  trace_state
  trivial

-- Test that we do not support post-conditions that actually reference the Unit value
-- (we could add support, but why?)

def weirderUnitFunction: Traceful Unit := sorry

instance:
  HoareTriple
    (weirderUnitFunction)
    (fun _ => True)
    (fun res _ => res = ())
  where
    pf := sorry

def testIncrementalCleanup': Traceful Unit := do
  let b ← receive_message 0
  send_message b
  send_message b
  weirderUnitFunction
  send_message b
  send_message b

/--
trace: case pf_next
inst : ExecTraceTypes
inst_1 : ProofTraceTypes
inst_2 : TraceInvariant
inst_3 : BytesFunctor
inst_4 : BytesInvariants
inst_5 : BytesInvariantsProofs
tr : Trace ProofTrace.Entry
h : tr.Invariant
b : Bytes
h_b✝ : b.Publishable tr
x✝ : PUnit
h_x✝ : x✝ = PUnit.unit
⊢ wp
    (do
      send_message b
      send_message b)
    (fun x x_1 => True) tr
-/
#guard_msgs in
example:
HoareTriple
  (testIncrementalCleanup')
  (fun _ => True)
  (fun _ _ => True)
:= by
  unfold testIncrementalCleanup'
  step
  step
  step
  step
  trace_state -- unit is not cleared because precondition depends on it
  step
  step
  trivial

end IncrementalCleanup

section BrutalCleanup

def testBrutalCleanup (n: Nat): Traceful Unit := do
  let b ← receive_message n
  send_message b
  send_message b

/--
trace: case pf_next
inst : ExecTraceTypes
inst_1 : ProofTraceTypes
inst_2 : TraceInvariant
inst_3 : BytesFunctor
inst_4 : BytesInvariants
inst_5 : BytesInvariantsProofs
n : Nat
tr : Trace ProofTrace.Entry
h : tr.Invariant
a✝ : n + 0 = n
b : Bytes
h_b✝ : b.Publishable tr
⊢ wp (send_message b) (fun x x_1 => True) tr
---
trace: case pf_next
inst : ExecTraceTypes
inst_1 : ProofTraceTypes
inst_2 : TraceInvariant
inst_3 : BytesFunctor
inst_4 : BytesInvariants
inst_5 : BytesInvariantsProofs
tr : Trace ProofTrace.Entry
h : tr.Invariant
b : Bytes
h_b✝ : b.Publishable tr
⊢ wp (send_message b) (fun x x_1 => True) tr
-/
#guard_msgs in
example (n: Nat):
  HoareTriple
  (testBrutalCleanup n)
  (fun _ => n + 0 = n)
  (fun _ _ => True)
:= by
  unfold testBrutalCleanup
  step
  step
  trace_state
  cleanup
  trace_state
  step
  trivial

end BrutalCleanup

end StepTest

