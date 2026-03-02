import DY.Trace
import DY.Bytes
import DY.Step

open DY

namespace DY.Step.Benchmark

variable [BytesFunctor]
variable [BytesInvariants]
variable [BytesInvariantsProofs]

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


def test: Traceful Unit := do
  let _msg0 ← receive_message 0
  let _msg1 ← receive_message 1
  let _msg2 ← receive_message 2
  let _msg3 ← receive_message 3
  let _msg4 ← receive_message 4
  let _msg5 ← receive_message 5
  let _msg6 ← receive_message 6
  let _msg7 ← receive_message 7
  let _msg8 ← receive_message 8
  let _msg9 ← receive_message 9
  let _msg10 ← receive_message 10
  let _msg11 ← receive_message 11
  let _msg12 ← receive_message 12
  let _msg13 ← receive_message 13
  let _msg14 ← receive_message 14
  let _msg15 ← receive_message 15
  let _msg16 ← receive_message 16
  let _msg17 ← receive_message 17
  let _msg18 ← receive_message 18
  let _msg19 ← receive_message 19
  let _msg20 ← receive_message 20
  let _msg21 ← receive_message 21
  let _msg22 ← receive_message 22
  let _msg23 ← receive_message 23
  let _msg24 ← receive_message 24
  let _msg25 ← receive_message 25
  let _msg26 ← receive_message 26
  let _msg27 ← receive_message 27
  let _msg28 ← receive_message 28
  let _msg29 ← receive_message 29
  let _msg30 ← receive_message 30
  let _msg31 ← receive_message 31
  let _msg32 ← receive_message 32
  let _msg33 ← receive_message 33
  let _msg34 ← receive_message 34
  let _msg35 ← receive_message 35
  let _msg36 ← receive_message 36
  let _msg37 ← receive_message 37
  let _msg38 ← receive_message 38
  let _msg39 ← receive_message 39

  send_message _msg0


set_option maxHeartbeats 10000000


theorem test.spec:
  HoareTriple
    (test)
    (fun _ => True)
    (fun _ _ => True)
:= by
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
  trivial

end DY.Step.Benchmark
