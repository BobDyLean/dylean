module

public import Examples.Ratchet.Specification
public import Examples.Ratchet.Proof

namespace DY.Example.Ratchet

-- Future work: the following section could avoid a lot of repetition
public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
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
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent RatchetEvent,
  PersistentLocalState.CompromisableState StateMyTurn,
  PersistentLocalState.CompromisableState StateOtherTurn,
  LongTermKeys "Ratchet PKI",

instance: HasExecTrace where

#combine +toplevel into
  ProofEntryT,
from
  Network,
  Random,
  ProtocolEvent RatchetEvent,
  PersistentLocalState.CompromisableState StateMyTurn,
  PersistentLocalState.CompromisableState StateOtherTurn,
  LongTermKeys "Ratchet PKI",

instance: HasProofTrace where

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
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
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  Network,
  Random,
  ProtocolEvent RatchetEvent,
  PersistentLocalState.CompromisableState StateMyTurn,
  PersistentLocalState.CompromisableState StateOtherTurn,
  LongTermKeys "Ratchet PKI",

#combine +toplevel into SubAttackerKnowledgeTheorem from
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
