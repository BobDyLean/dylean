module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.Actions.Network
public meta import DY.Trace.Monad
public meta import DY.EquationalTheory.Literal
public meta import DY.Actions.Network

namespace DY.Benchmark.TraceRuntime

#combine +toplevel into BytesFunctor, BytesLength from
  Literal

#combine +toplevel into ExecEntryT from
  Network

def run (n: Nat): Traceful Unit := do
  let msgHandle ← Network.sendMessage (Literal.literalToBytes ByteArray.empty)
  for _ in [0:n] do
    let _ ← Network.sendMessage (Literal.literalToBytes ByteArray.empty)
    let msg ← Network.receiveMessage msgHandle
    guard (msg = Literal.literalToBytes ByteArray.empty)

-- calibrated to run in ~1s
#guard ((run 500000).run Trace.empty).fst = some ()

end DY.Benchmark.TraceRuntime
