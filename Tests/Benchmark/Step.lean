module

import DY.Trace
import DY.Bytes
import DY.Meta
public import DY.EquationalTheory.Literal
public import DY.Actions.Network

open DY

namespace DY.Step.Benchmark


#combine +toplevel into BytesFunctor from
  Literal

#combine +toplevel into ExecEntryT, ProofEntryT from
  Network

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Literal

#combine +toplevel into SubTraceInvariant from
  Network

/--
`#mk_step_benchmark_program name n` defines
```
def name: Traceful Unit := do
  let msg0 ← Network.receiveMessage 0
  ...
  let msg{n-1} ← Network.receiveMessage {n-1}

  let _ ← Network.sendMessage msg0
  ...
  let _ ← Network.sendMessage msg{n-1}
```
-/
macro "#mk_step_benchmark_program " name:ident n:num : command => do
  let n := n.getNat
  let mkMsgId (i: Nat) := Lean.mkIdent (.mkSimple s!"msg{i}")
  let mut items : Array (Lean.TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
  for i in [0:n] do
    items := items.push (← `(Lean.Parser.Term.doSeqItem| let $(mkMsgId i) ← Network.receiveMessage $(Lean.quote i)))
  for i in [0:n] do
    items := items.push (← `(Lean.Parser.Term.doSeqItem| let _ ← Network.sendMessage $(mkMsgId i)))
  `(def $name : Traceful Unit := do $items*)

#mk_step_benchmark_program test 40

set_option maxHeartbeats 0

theorem test.proof:
  HoareTriple
    (test)
    (fun _ => True)
    (fun _ _ => True)
:= by
  -- set_option trace.profiler true in
  unfold test
  repeat step
  grind

end DY.Step.Benchmark
