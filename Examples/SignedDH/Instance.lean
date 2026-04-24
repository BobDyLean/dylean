module

public import Examples.SignedDH.Specification
public import Examples.SignedDH.Proof

namespace DY.Example.SignedDH

public section

abbrev SubF.internal: (id: Fin 6) → (Type → Type)
  | 0 => Literal.SubF
  | 1 => Concat.SubF
  | 2 => Hash.SubF
  | 3 => Signature.SubF
  | 4 => DiffieHellman.SubF
  | 5 => Random.SubF

abbrev SubF := BytesFunctor.combine SubF.internal

instance: ∀ id, SubBytesFunctor (SubF.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 => inferInstance

instance: BytesFunctor.HasStep Literal.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 0) SubF)
instance: BytesFunctor.HasStep Concat.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 1) SubF)
instance: BytesFunctor.HasStep Hash.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 2) SubF)
instance: BytesFunctor.HasStep Signature.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 3) SubF)
instance: BytesFunctor.HasStep DiffieHellman.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 4) SubF)
instance: BytesFunctor.HasStep Random.SubF SubF := inferInstanceAs (BytesFunctor.HasStep (SubF.internal 5) SubF)

instance: BytesFunctor where
  BytesF := SubF

instance: BytesFunctor.Has SubF := inferInstanceAs (BytesFunctor.Has BytesF)

def SubF.length.internal [BytesFunctor]: ∀ id, Bytes.PartialLength (SubF.internal id)
  | 0 => Literal.SubF.length
  | 1 => Concat.SubF.length
  | 2 => Hash.SubF.length
  | 3 => Signature.SubF.length
  | 4 => DiffieHellman.SubF.length
  | 5 => Random.SubF.length

abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  Bytes.PartialLength.combine SubF.length.internal

instance: BytesLength where
  funs := SubF.length

instance: BytesLength.HasStep Literal.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 0) SubF.length)
instance: BytesLength.HasStep Concat.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 1) SubF.length)
instance: BytesLength.HasStep Hash.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 2) SubF.length)
instance: BytesLength.HasStep Signature.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 3) SubF.length)
instance: BytesLength.HasStep DiffieHellman.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 4) SubF.length)
instance: BytesLength.HasStep Random.SubF.length SubF.length := inferInstanceAs (BytesLength.HasStep (SubF.length.internal 5) SubF.length)

instance: BytesLength.Has SubF.length := inferInstanceAs (BytesLength.Has SubF.length)

def attackerKnowledge.internal (id: Fin 6): SubAttackerKnowledge (SubF.internal id) :=
  match id with
  | 0 => Literal.attackerKnowledge
  | 1 => Concat.attackerKnowledge
  | 2 => Hash.attackerKnowledge
  | 3 => Signature.attackerKnowledge
  | 4 => DiffieHellman.attackerKnowledge
  | 5 => Random.attackerKnowledge

def attackerKnowledge: SubAttackerKnowledge SubF :=
  SubAttackerKnowledge.combine attackerKnowledge.internal

instance: AttackerKnowledge.HasStep Literal.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 0) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Concat.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 1) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Hash.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 2) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Signature.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 3) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep DiffieHellman.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 4) (SubAttackerKnowledge.combine attackerKnowledge.internal))
instance: AttackerKnowledge.HasStep Random.attackerKnowledge attackerKnowledge := inferInstanceAs (AttackerKnowledge.HasStep (attackerKnowledge.internal 5) (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledge where
  attackerKnowledge

instance: AttackerKnowledge.Has attackerKnowledge := inferInstanceAs (AttackerKnowledge.Has AttackerKnowledge.attackerKnowledge)

instance: HasExecBytes where

public
abbrev ExecEntryT.internal: Fin 7 → Type
  | 0 => Network.ExecEntryT
  | 1 => Random.ExecEntryT
  | 2 => ProtocolEvent.ExecEntryT SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ServerFinishState
  | 6 => LongTermKeys.ExecEntryT "SignedDH"

public
abbrev ExecEntryT: Type :=
  ExecTraceTypes.combine ExecEntryT.internal

instance: ExecTraceTypes.HasStep Network.ExecEntryT ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 0) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep Random.ExecEntryT ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 1) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (ProtocolEvent.ExecEntryT SignedDH.SignedDHEvent) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 2) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientInitiateState) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 3) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ClientFinishState) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 4) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (PersistentLocalState.CompromisableState.ExecEntryT SignedDH.ServerFinishState) ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 5) (ExecTraceTypes.combine ExecEntryT.internal))
instance: ExecTraceTypes.HasStep (LongTermKeys.ExecEntryT "SignedDH") ExecEntryT := inferInstanceAs (ExecTraceTypes.HasStep (ExecEntryT.internal 6) (ExecTraceTypes.combine ExecEntryT.internal))

instance: ExecTraceTypes where
  ExecT := ExecEntryT

instance: ExecTraceTypes.Has ExecEntryT := inferInstanceAs (ExecTraceTypes.Has ExecTrace.Entry)

public
def baseAttackerKnowledge.internal: (id: Fin 7) → SubBaseAttackerKnowledge (ExecEntryT.internal id)
  | 0 => Network.baseAttackerKnowledge
  | 1 => Random.baseAttackerKnowledge
  | 2 => ProtocolEvent.baseAttackerKnowledge SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.baseAttackerKnowledge SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.baseAttackerKnowledge SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.baseAttackerKnowledge SignedDH.ServerFinishState
  | 6 => LongTermKeys.baseAttackerKnowledge "SignedDH"

public
def baseAttackerKnowledge: SubBaseAttackerKnowledge ExecEntryT :=
  SubBaseAttackerKnowledge.combine baseAttackerKnowledge.internal

instance: BaseAttackerKnowledge where
  attackerKnows := baseAttackerKnowledge

instance: HasExecTrace where

@[expose]
public
def ProofEntryT.internal: Fin 7 → Type
  | 0 => Network.ProofEntryT
  | 1 => Random.ProofEntryT
  | 2 => ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent
  | 3 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState
  | 4 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState
  | 5 => PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState
  | 6 => LongTermKeys.ProofEntryT "SignedDH"

public
abbrev ProofEntryT: Type :=
  ProofTraceTypes.combine ProofEntryT.internal

public
instance: ∀ id, ErasableProofEntry (ExecEntryT.internal id) (ProofEntryT.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => by dsimp only [ExecEntryT.internal, ProofEntryT.internal]; infer_instance

public
instance: ErasableProofEntry ExecEntryT ProofEntryT :=
  (inferInstance: ErasableProofEntry (ExecTraceTypes.combine ExecEntryT.internal) (ProofTraceTypes.combine ProofEntryT.internal))

instance: ProofTraceTypes.HasStep Network.ProofEntryT ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 0) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep Random.ProofEntryT ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 1) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 2) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 3) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 4) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 5) (ProofTraceTypes.combine ProofEntryT.internal))
instance: ProofTraceTypes.HasStep (LongTermKeys.ProofEntryT "SignedDH") ProofEntryT := inferInstanceAs (ProofTraceTypes.HasStep (ProofEntryT.internal 6) (ProofTraceTypes.combine ProofEntryT.internal))

instance: ProofTraceTypes where
  ProofT := ProofEntryT
  tc := inferInstance

instance: ProofTraceTypes.Has ProofEntryT := inferInstanceAs (ProofTraceTypes.Has ProofTrace.Entry)

instance: HasProofTrace where

def invariants.internal: (id: Fin 6) → Bytes.PartialInvariants (SubF.internal id)
  | 0 => Literal.invariants
  | 1 => Concat.invariants
  | 2 => Hash.invariants
  | 3 => Signature.invariants
  | 4 => DiffieHellman.invariants
  | 5 => Random.invariants

abbrev invariants: Bytes.PartialInvariants SubF :=
  Bytes.PartialInvariants.combine invariants.internal

instance [BytesInvariants]: BytesInvariants.HasStep Literal.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 0) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Concat.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 1) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Hash.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 2) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Signature.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 3) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep DiffieHellman.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 4) invariants)
instance [BytesInvariants]: BytesInvariants.HasStep Random.invariants invariants := inferInstanceAs (BytesInvariants.HasStep (invariants.internal 5) invariants)

instance: BytesInvariants where
  invs := invariants

instance: BytesInvariants.Has invariants := inferInstance

def invariantsProofs.internal: (id: Fin 6) → Bytes.PartialInvariantsProofs (invariants.internal id)
  | 0 => Literal.invariantsProofs
  | 1 => Concat.invariantsProofs
  | 2 => Hash.invariantsProofs
  | 3 => Signature.invariantsProofs
  | 4 => DiffieHellman.invariantsProofs
  | 5 => Random.invariantsProofs

abbrev invariantsProofs: Bytes.PartialInvariantsProofs invariants :=
  Bytes.PartialInvariantsProofs.combine invariantsProofs.internal

instance: BytesInvariantsProofs where
  pfs := invariantsProofs

instance: HasBytesInvariants where

public
instance: ∀ id, SubTraceInvariant (ProofEntryT.internal id)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => by dsimp only [ProofEntryT.internal]; infer_instance

public
instance: SubTraceInvariant ProofEntryT :=
  (inferInstance: SubTraceInvariant (ProofTraceTypes.combine ProofEntryT.internal))

instance : TraceInvariant where
  tc_inv := by dsimp only [ProofTrace.Entry, ProofTraceTypes.ProofT]; infer_instance

instance: TraceInvariant.Has ProofEntryT := inferInstanceAs (TraceInvariant.Has ProofTrace.Entry)

instance: TraceInvariant.HasStep Network.ProofEntryT ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 0) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep Random.ProofEntryT ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 1) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (ProtocolEvent.ProofEntryT SignedDH.SignedDHEvent) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 2) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientInitiateState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 3) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ClientFinishState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 4) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (PersistentLocalState.CompromisableState.ProofEntryT SignedDH.ServerFinishState) ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 5) (ProofTraceTypes.combine ProofEntryT.internal))
instance: TraceInvariant.HasStep (LongTermKeys.ProofEntryT "SignedDH") ProofEntryT := inferInstanceAs (TraceInvariant.HasStep (ProofEntryT.internal 6) (ProofTraceTypes.combine ProofEntryT.internal))

instance : ∀ id, SubBaseAttackerKnowledgeTheorem (ProofEntryT.internal id) (baseAttackerKnowledge.internal id)
  -- TODO: investigate why infer_instance doesn't work
  | 0 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Network.baseAttackerKnowledgeTheorem
  | 1 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply Random.baseAttackerKnowledgeTheorem
  | 2 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply ProtocolEvent.baseAttackerKnowledgeTheorem
  | 3 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 4 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 5 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply PersistentLocalState.CompromisableState.baseAttackerKnowledgeTheorem
  | 6 => by dsimp only [ProofEntryT.internal, baseAttackerKnowledge.internal]; apply LongTermKeys.baseAttackerKnowledgeTheorem "SignedDH"

instance: SubBaseAttackerKnowledgeTheorem (ProofEntryT) (baseAttackerKnowledge) := by
  dsimp only [ProofEntryT, baseAttackerKnowledge]
  infer_instance

instance: BaseAttackerKnowledgeTheorem where
  pf := by
    dsimp only [ProofTrace.Entry, ProofTraceTypes.ProofT, BaseAttackerKnowledge.attackerKnows]
    -- TODO infer_instance
    exact instSubBaseAttackerKnowledgeTheoremExecEntryTProofEntryTBaseAttackerKnowledge

instance: (id: Fin 6) → SubAttackerKnowledgeTheorem (attackerKnowledge.internal id)
  | 0 => inferInstanceAs (SubAttackerKnowledgeTheorem Literal.attackerKnowledge)
  | 1 => inferInstanceAs (SubAttackerKnowledgeTheorem Concat.attackerKnowledge)
  | 2 => inferInstanceAs (SubAttackerKnowledgeTheorem Hash.attackerKnowledge)
  | 3 => inferInstanceAs (SubAttackerKnowledgeTheorem Signature.attackerKnowledge)
  | 4 => inferInstanceAs (SubAttackerKnowledgeTheorem DiffieHellman.attackerKnowledge)
  | 5 => inferInstanceAs (SubAttackerKnowledgeTheorem Random.attackerKnowledge)

instance: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstanceAs (SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine attackerKnowledge.internal))

instance: AttackerKnowledgeTheorem where
  inst := inferInstanceAs (SubAttackerKnowledgeTheorem attackerKnowledge)

instance: HasTraceInvariant where

end

end DY.Example.SignedDH
