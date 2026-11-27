module

public import Examples.Ratchet.Specification
public import Examples.Ratchet.Proof

namespace DY.Example.Ratchet

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into Bytes, Bytes.length, Bytes.AttackerKnows from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  KdfExtract,
  KdfExpand,

instance: HasExecBytes where

#combine +toplevel into
  ExecTrace,
  Trace.BaseAttackerKnows,
from
  Network,
  Random,
  ProtocolEvent RatchetEvent,
  PersistentLocalState.CompromisableState StateMyTurn,
  PersistentLocalState.CompromisableState StateOtherTurn,
  LongTermKeys "Ratchet PKI",

instance: HasExecTrace where

#combine +toplevel into
  ProofTrace,
from
  Network,
  Random,
  ProtocolEvent RatchetEvent,
  PersistentLocalState.CompromisableState StateMyTurn,
  PersistentLocalState.CompromisableState StateOtherTurn,
  LongTermKeys "Ratchet PKI",

instance: HasProofTrace where

#combine +toplevel into Bytes.Invariants, Bytes.Invariants.Lawful from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  KdfExtract,
  KdfExpand,

instance: HasBytesInvariants where

#combine +toplevel into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from
  Network,
  Random,
  ProtocolEvent RatchetEvent,
  PersistentLocalState.CompromisableState StateMyTurn,
  PersistentLocalState.CompromisableState StateOtherTurn,
  LongTermKeys "Ratchet PKI",

#combine +toplevel into Bytes.AttackerKnows_implies_Publishable from
  Random,
  Literal,
  Concat,
  Hash,
  Signature,
  DiffieHellman,
  KdfExtract,
  KdfExpand,

instance: HasTraceInvariant where

end

end DY.Example.Ratchet
