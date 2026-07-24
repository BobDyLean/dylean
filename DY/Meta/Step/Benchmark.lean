module

import DY.Trace
import DY.Bytes
import DY.Meta

open DY

namespace DY.Step.Benchmark

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

section Axiomatization

set_option warn.sorry false

def send_message (b:Bytes) : Traceful Unit := sorry
def receive_message (n:Nat) : Traceful Bytes := sorry

instance:
  HoareTriple
    (send_message b)
    (fun tr => b.Publishable tr)
    (fun _ _ => True)
  where
    pf := sorry

instance:
  HoareTriple
    (receive_message n)
    (fun _ => True) (fun b tr => b.Publishable tr)
  where
    pf := sorry

end Axiomatization

def test: Traceful Unit := do
  let msg0 ← receive_message 0
  let msg1 ← receive_message 1
  let msg2 ← receive_message 2
  let msg3 ← receive_message 3
  let msg4 ← receive_message 4
  let msg5 ← receive_message 5
  let msg6 ← receive_message 6
  let msg7 ← receive_message 7
  let msg8 ← receive_message 8
  let msg9 ← receive_message 9
  let msg10 ← receive_message 10
  let msg11 ← receive_message 11
  let msg12 ← receive_message 12
  let msg13 ← receive_message 13
  let msg14 ← receive_message 14
  let msg15 ← receive_message 15
  let msg16 ← receive_message 16
  let msg17 ← receive_message 17
  let msg18 ← receive_message 18
  let msg19 ← receive_message 19
  let msg20 ← receive_message 20
  let msg21 ← receive_message 21
  let msg22 ← receive_message 22
  let msg23 ← receive_message 23
  let msg24 ← receive_message 24
  let msg25 ← receive_message 25
  let msg26 ← receive_message 26
  let msg27 ← receive_message 27
  let msg28 ← receive_message 28
  let msg29 ← receive_message 29
  let msg30 ← receive_message 30
  let msg31 ← receive_message 31
  let msg32 ← receive_message 32
  let msg33 ← receive_message 33
  let msg34 ← receive_message 34
  let msg35 ← receive_message 35
  let msg36 ← receive_message 36
  let msg37 ← receive_message 37
  let msg38 ← receive_message 38
  let msg39 ← receive_message 39

  send_message msg0
  send_message msg1
  send_message msg2
  send_message msg3
  send_message msg4
  send_message msg5
  send_message msg6
  send_message msg7
  send_message msg8
  send_message msg9
  send_message msg10
  send_message msg11
  send_message msg12
  send_message msg13
  send_message msg14
  send_message msg15
  send_message msg16
  send_message msg17
  send_message msg18
  send_message msg19
  send_message msg20
  send_message msg21
  send_message msg22
  send_message msg23
  send_message msg24
  send_message msg25
  send_message msg26
  send_message msg27
  send_message msg28
  send_message msg29
  send_message msg30
  send_message msg31
  send_message msg32
  send_message msg33
  send_message msg34
  send_message msg35
  send_message msg36
  send_message msg37
  send_message msg38
  send_message msg39

theorem test.spec:
  HoareTriple
    (test)
    (fun _ => True)
    (fun _ _ => True)
:= by
  -- On TWal's laptop:
  -- - full tactic executes in ~8s
  -- - steps at the end take ~0.1s
  -- set_option trace.profiler true in
  apply HoareTriple.mk
  unfold test
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  trivial

end DY.Step.Benchmark
