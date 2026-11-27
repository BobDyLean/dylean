module

public import Examples.MerkleTree.Specification
public import Examples.MerkleTree.Proof

namespace DY.Example.MerkleTree

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into Bytes, Bytes.length, Bytes.AttackerKnows from
  Literal,
  Concat,
  Hash,
  Signature,
  Random,

instance: HasExecBytes where

#combine +toplevel into
  ExecTrace,
  Trace.BaseAttackerKnows,
from
  Network,
  Random,
  ProtocolEvent TheEvent,
  PersistentLocalState.CompromisableState ServerState,
  LongTermKeys "MerkleTree PKI",

instance: HasExecTrace where

#combine +toplevel into
  ProofTrace,
from
  Network,
  Random,
  ProtocolEvent TheEvent,
  PersistentLocalState.CompromisableState ServerState,
  LongTermKeys "MerkleTree PKI",

instance: HasProofTrace where

#combine +toplevel into Bytes.Invariants, Bytes.Invariants.Lawful from
  Literal,
  Concat,
  Hash,
  Signature,
  Random

instance: HasBytesInvariants where

#combine +toplevel into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from
  Network,
  Random,
  ProtocolEvent TheEvent,
  PersistentLocalState.CompromisableState ServerState,
  LongTermKeys "MerkleTree PKI",

#combine +toplevel into Bytes.AttackerKnows_implies_Publishable from
  Literal,
  Concat,
  Hash,
  Signature,
  Random

instance: HasTraceInvariant where

end

end DY.Example.MerkleTree
