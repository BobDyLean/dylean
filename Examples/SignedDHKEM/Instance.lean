module

public import Examples.SignedDHKEM.Specification
public import Examples.SignedDHKEM.Proof

namespace DY.Example.SignedDHKEM

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  Hash,
  Signature',
  DiffieHellman',
  KEM,

instance: HasExecBytes where

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent SignedDHKEMEvent,
  PersistentLocalState.CompromisableState ClientInitiateDHState,
  PersistentLocalState.CompromisableState ClientInitiateKEMState,
  PersistentLocalState.CompromisableState ClientFinishState,
  PersistentLocalState.CompromisableState ServerFinishState,
  LongTermKeys "SignedDHKEM PKI",
  KEM.Broken,
  DiffieHellman'.Broken,
  Signature'.Broken,

instance: HasExecTrace where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Random,
  ProtocolEvent SignedDHKEMEvent,
  PersistentLocalState.CompromisableState ClientInitiateDHState,
  PersistentLocalState.CompromisableState ClientInitiateKEMState,
  PersistentLocalState.CompromisableState ClientFinishState,
  PersistentLocalState.CompromisableState ServerFinishState,
  LongTermKeys "SignedDHKEM PKI",
  KEM.Broken,
  DiffieHellman'.Broken,
  Signature'.Broken,

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  Hash,
  Signature',
  DiffieHellman',
  KEM,

instance: HasBytesInvariants where

#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent SignedDHKEMEvent,
  PersistentLocalState.CompromisableState ClientInitiateDHState,
  PersistentLocalState.CompromisableState ClientInitiateKEMState,
  PersistentLocalState.CompromisableState ClientFinishState,
  PersistentLocalState.CompromisableState ServerFinishState,
  LongTermKeys "SignedDHKEM PKI",
  KEM.Broken,
  DiffieHellman'.Broken,
  Signature'.Broken,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  Hash,
  Signature',
  DiffieHellman',
  KEM,

instance: HasTraceInvariant where

end

end DY.Example.SignedDHKEM
