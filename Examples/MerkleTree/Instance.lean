module

public import Examples.MerkleTree.Specification
public import Examples.MerkleTree.Proof

namespace DY.Example.MerkleTree

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,
  Signature,
  Random,

instance: HasExecBytes where

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent TheEvent,
  PersistentLocalState.CompromisableState ServerState,
  LongTermKeys "MerkleTree PKI",

instance: HasExecTrace where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Random,
  ProtocolEvent TheEvent,
  PersistentLocalState.CompromisableState ServerState,
  LongTermKeys "MerkleTree PKI",

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Literal,
  Concat,
  Hash,
  Signature,
  Random

instance: HasBytesInvariants where

#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent TheEvent,
  PersistentLocalState.CompromisableState ServerState,
  LongTermKeys "MerkleTree PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,
  Signature,
  Random

instance: HasTraceInvariant where

end

end DY.Example.MerkleTree
