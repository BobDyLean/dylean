module

public import Examples.ACME.Specification
public import Examples.ACME.WithDEO.SignDEO

namespace DY.Example.ACME.WithDEO

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  SignDEO,

instance: HasExecBytes where

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

instance: HasExecTrace where

end

end DY.Example.ACME.WithDEO
