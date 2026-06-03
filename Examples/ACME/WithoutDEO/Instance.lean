module

public import Examples.ACME.Specification
public import Examples.ACME.WithoutDEO.Proof

namespace DY.Example.ACME.WithoutDEO

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  Signature,

instance: HasExecBytesWithoutDEO where

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
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
  ProofEntryT,
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

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  Signature,

instance: HasBytesInvariants where

#combine +toplevel into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent ACMEEvent,
  PersistentLocalState.CompromisableState OwnerKeyState,
  PersistentLocalState.CompromisableState OwnerAddressState,
  PersistentLocalState.CompromisableState LetsEncryptPendingChallengeState,
  PersistentGlobalState.CompromisableState DNSEntry,
  LongTermKeys "ACME PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  Signature,

instance: HasTraceInvariant where

end

end DY.Example.ACME.WithoutDEO
