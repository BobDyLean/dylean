module

public import Examples.ACME.Specification
public import Examples.ACME.WithoutDEO.Proof

namespace DY.Example.ACME.WithoutDEO

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into Bytes, Bytes.length, Bytes.AttackerKnows from
  Random,
  Literal,
  Concat,
  Signature,

instance: HasExecBytesWithoutDEO where

#combine +toplevel into
  ExecTrace,
  Trace.BaseAttackerKnows,
from
  Network,
  Random,
  ProtocolEvent ACMEEvent,
  PersistentLocalState.CompromisableState OwnerKeyState,
  PersistentLocalState.CompromisableState OwnerAddressState,
  PersistentLocalState.CompromisableState LetsEncryptPendingChallengeState,
  PersistentGlobalState.CompromisableState DNSEntry,
  LongTermKeys "ACME PKI",

instance: HasExecTraceWithoutDEO where

#combine +toplevel into
  ProofTrace,
from
  Network,
  Random,
  ProtocolEvent ACMEEvent,
  PersistentLocalState.CompromisableState OwnerKeyState,
  PersistentLocalState.CompromisableState OwnerAddressState,
  PersistentLocalState.CompromisableState LetsEncryptPendingChallengeState,
  PersistentGlobalState.CompromisableState DNSEntry,
  LongTermKeys "ACME PKI",

instance: HasProofTrace where

#combine +toplevel into Bytes.Invariants, Bytes.Invariants.Lawful from
  Random,
  Literal,
  Concat,
  Signature,

instance: HasBytesInvariants where

#combine +toplevel into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from
  Network,
  Random,
  ProtocolEvent ACMEEvent,
  PersistentLocalState.CompromisableState OwnerKeyState,
  PersistentLocalState.CompromisableState OwnerAddressState,
  PersistentLocalState.CompromisableState LetsEncryptPendingChallengeState,
  PersistentGlobalState.CompromisableState DNSEntry,
  LongTermKeys "ACME PKI",

#combine +toplevel into Bytes.AttackerKnows_implies_Publishable from
  Random,
  Literal,
  Concat,
  Signature,

instance: HasTraceInvariant where

end

end DY.Example.ACME.WithoutDEO
