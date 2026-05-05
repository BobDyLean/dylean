module

public import Examples.SignedDH.Specification
public import Examples.SignedDH.Proof

namespace DY.Example.SignedDH

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  Random,

instance: HasExecBytes where

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent SignedDH.SignedDHEvent,
  PersistentLocalState.CompromisableState SignedDH.ClientInitiateState,
  PersistentLocalState.CompromisableState SignedDH.ClientFinishState,
  PersistentLocalState.CompromisableState SignedDH.ServerFinishState,
  LongTermKeys "SignedDH",

instance: HasExecTrace where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Random,
  ProtocolEvent SignedDH.SignedDHEvent,
  PersistentLocalState.CompromisableState SignedDH.ClientInitiateState,
  PersistentLocalState.CompromisableState SignedDH.ClientFinishState,
  PersistentLocalState.CompromisableState SignedDH.ServerFinishState,
  LongTermKeys "SignedDH",

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  Random

instance: HasBytesInvariants where

#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent SignedDH.SignedDHEvent,
  PersistentLocalState.CompromisableState SignedDH.ClientInitiateState,
  PersistentLocalState.CompromisableState SignedDH.ClientFinishState,
  PersistentLocalState.CompromisableState SignedDH.ServerFinishState,
  LongTermKeys "SignedDH",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  Random,

instance: HasTraceInvariant where

end

end DY.Example.SignedDH
