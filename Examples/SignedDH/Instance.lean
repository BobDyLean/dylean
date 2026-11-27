module

public import Examples.SignedDH.Specification
public import Examples.SignedDH.Proof

namespace DY.Example.SignedDH

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into Bytes, Bytes.length, Bytes.AttackerKnows from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,

instance: HasExecBytes where

#combine +toplevel into
  ExecTrace,
  Trace.BaseAttackerKnows,
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
  ProofTrace,
from
  Network,
  Random,
  ProtocolEvent SignedDH.SignedDHEvent,
  PersistentLocalState.CompromisableState SignedDH.ClientInitiateState,
  PersistentLocalState.CompromisableState SignedDH.ClientFinishState,
  PersistentLocalState.CompromisableState SignedDH.ServerFinishState,
  LongTermKeys "SignedDH PKI",

instance: HasProofTrace where

#combine +toplevel into Bytes.Invariants, Bytes.Invariants.Lawful from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,

instance: HasBytesInvariants where

#combine +toplevel into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from
  Network,
  Random,
  ProtocolEvent SignedDH.SignedDHEvent,
  PersistentLocalState.CompromisableState SignedDH.ClientInitiateState,
  PersistentLocalState.CompromisableState SignedDH.ClientFinishState,
  PersistentLocalState.CompromisableState SignedDH.ServerFinishState,
  LongTermKeys "SignedDH PKI",

#combine +toplevel into Bytes.AttackerKnows_implies_Publishable from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,

instance: HasTraceInvariant where

end

end DY.Example.SignedDH
