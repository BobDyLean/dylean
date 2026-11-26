module

public import Examples.SignedDHKEM.Specification
public import Examples.SignedDHKEM.Proof

namespace DY.Example.SignedDHKEM

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into Bytes, Bytes.length, Bytes.AttackerKnows from
  Random,
  Literal,
  Concat,
  Hash,
  Signature',
  DiffieHellman',
  KEM,

instance: HasExecBytes where

#combine +toplevel into
  ExecTrace,
  Trace.BaseAttackerKnows,
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
  ProofTrace,
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

#combine +toplevel into Bytes.Invariants, Bytes.Invariants.Lawful from
  Random,
  Literal,
  Concat,
  Hash,
  Signature',
  DiffieHellman',
  KEM,

instance: HasBytesInvariants where

#combine +toplevel into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
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

#combine +toplevel into Bytes.AttackerKnows_implies_Publishable from
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
