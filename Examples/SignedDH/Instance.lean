module

public import Examples.SignedDH.Specification
public import Examples.SignedDH.Proof

namespace DY.Example.SignedDH

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,

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
  LongTermKeys "SignedDH PKI",

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
  LongTermKeys "SignedDH PKI",

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,

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
  LongTermKeys "SignedDH PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,

instance: HasTraceInvariant where

end

end DY.Example.SignedDH
