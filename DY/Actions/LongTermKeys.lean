module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.Random
public import DY.Actions.Network
public import DY.Actions.PersistentGlobalState
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

namespace DY.LongTermKeys

section Execution

public
class ExecConfig [BytesFunctor] (name: String) (skToPk: outParam (Bytes → Bytes)) where

public
structure SecretKeyState [BytesFunctor] (name: String) where
  sk: Bytes

public
instance
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (name: String)
  : Comparse.ParseableSerializeable (SecretKeyState name)
:= .make <|
  .triviallyIsomorphic
    (.bytes)
    (fun sk => { sk })
    (fun { sk := sk } => sk)

theorem SecretKeyState.IsWellFormed_eq
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: SecretKeyState name) (tr: τ):
  Comparse.IsWellFormed pre x tr = pre x.sk tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SecretKeyState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

public
structure PublicKeyState [BytesFunctor] (name: String) where
  p: Participant
  pk: Bytes

public
instance
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (name: String)
  : Comparse.ParseableSerializeable (PublicKeyState name)
:= .make <|
  .triviallyIsomorphic
    (.prod .slowString .bytes)
    (fun ⟨ p, pk ⟩ => { p, pk })
    (fun { p, pk } => ⟨ p, pk ⟩)

theorem PublicKeyState.IsWellFormed_eq
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: PublicKeyState name) (tr: τ):
  Comparse.IsWellFormed pre x tr = pre x.pk tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern PublicKeyState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

#combine [BytesFunctor] (name: String) into
  ExecEntryT,
  baseAttackerKnowledge,
from
  PersistentLocalState.CompromisableState (SecretKeyState name),
  PersistentGlobalState.CompromisableState (PublicKeyState name)

variable [BytesFunctor]
variable (name: String)
variable {skToPk: Bytes → Bytes}
variable [ExecConfig name skToPk]

public
def generateKeyPair
  [ExecConfig name skToPk]
  [ExecTraceTypes]
  [BytesFunctor.Has Random.SubF]
  [ExecTraceTypes.Has Random.ExecEntryT]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has <| ExecEntryT name]
  (p: Participant)
  : Traceful (Nat × Nat × Nat)
:= do
  let sk ← Random.genRand 32
  let pk := skToPk sk
  let tsMsg ← Network.sendMessage pk
  let tsPk ← PersistentGlobalState.storeGlobalState ({p, pk}: PublicKeyState name)
  let tsSk ← PersistentLocalState.storeLocalState p ({sk}: SecretKeyState name)
  pure (tsMsg, tsPk, tsSk)

public
def getPublicKey
  [ExecTraceTypes]
  [ExecTraceTypes.Has <| ExecEntryT name]
  (p: Participant)
  (tsPk: Nat)
  : Traceful Bytes
:= do
  let st: PublicKeyState name ← PersistentGlobalState.getGlobalState tsPk
  guard (st.p = p)
  pure st.pk

public
def getPrivateKey
  [ExecTraceTypes]
  [ExecTraceTypes.Has <| ExecEntryT name]
  (p: Participant)
  (tsSk: Nat)
  : Traceful Bytes
:= do
  let st: SecretKeyState name ← PersistentLocalState.getLocalState p tsSk
  pure st.sk

public
def LongTermKeyCompromised
  [ExecConfig name skToPk] [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT name)]
  (participant: Participant) (pk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  ∃ sk,
    pk = skToPk sk ∧
    PersistentLocalState.LocalStateCompromised participant ({ sk }: SecretKeyState name) tr

public
theorem LongTermKeyCompromised_le
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT name)]
  (participant: Participant) (pk: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    LongTermKeyCompromised name participant pk tr1 →
    LongTermKeyCompromised name participant pk tr2
:= by
  simp [LongTermKeyCompromised]
  grind

grind_pattern LongTermKeyCompromised_le => tr1 ≤ tr2, LongTermKeyCompromised name participant pk tr1
grind_pattern [grind_later] LongTermKeyCompromised_le => tr1 ≤ tr2, LongTermKeyCompromised name participant pk tr1

end Execution

section Proof

@[expose]
public
def label
  [BytesFunctor]
  (name: String) {skToPk: Bytes → Bytes} [ExecConfig name skToPk]
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT name)]
  (participant: Participant) (pk: Bytes)
  : Label
where
  isCorrupt := LongTermKeyCompromised name participant pk

public
class ProofConfig
  [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  (name: String) {skToPk: outParam (Bytes → Bytes)} (usage: outParam (Participant → Usage))
  [ExecConfig name skToPk]
  [ExecTraceTypes.Has (ExecEntryT name)]
where
  IsLongTermPublicKey: Participant → Bytes → ProofTrace → Prop

  IsLongTermPublicKey_le: ∀ p b tr1 tr2,
    tr1 ≤ tr2 →
    IsLongTermPublicKey p b tr1 →
    IsLongTermPublicKey p b tr2
  := by grind

  IsLongTermPublicKey_implied (name): ∀ p b tr,
    b.Invariant tr →
    b.label tr = label name p (skToPk b) →
    b.HasUsage (usage p) tr →
    IsLongTermPublicKey p (skToPk b) tr

  IsLongTermPublicKey_implies (name): ∀ p b tr,
    IsLongTermPublicKey p b tr →
    b.Publishable tr
  := by grind

export ProofConfig (IsLongTermPublicKey)

grind_pattern ProofConfig.IsLongTermPublicKey_le => tr1 ≤ tr2, ProofConfig.IsLongTermPublicKey name p b tr1
grind_pattern [grind_later] ProofConfig.IsLongTermPublicKey_le => tr1 ≤ tr2, ProofConfig.IsLongTermPublicKey name p b tr1

public
theorem IsLongTermPublicKey_implies_Invariant
  [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  (name: String) {skToPk: Bytes → Bytes} (usage: Participant → Usage)
  [ExecTraceTypes.Has (ExecEntryT name)]
  [ExecConfig name skToPk] [ProofConfig name usage]
  (p: Participant) (b: Bytes) (tr: ProofTrace)
  : IsLongTermPublicKey name p b tr →
    b.Invariant tr
:= by
  have := ProofConfig.IsLongTermPublicKey_implies name
  grind

grind_pattern [grind_later] IsLongTermPublicKey_implies_Invariant => IsLongTermPublicKey name p b tr

@[expose]
public
def IsLongTermSecretKey
  [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  (name: String) {skToPk: Bytes → Bytes} {usage: Participant → Usage}
  [ExecTraceTypes.Has (ExecEntryT name)]
  [ExecConfig name skToPk] [ProofConfig name usage]
  (p: Participant) (b: Bytes) (tr: ProofTrace)
  : Prop
:=
  b.Invariant tr ∧
  b.label tr = label name p (skToPk b) ∧
  b.HasUsage (usage p) tr

public
theorem IsLongTermSecretKey_later
  [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
  (name: String) {skToPk: Bytes → Bytes} {usage: Participant → Usage}
  [ExecTraceTypes.Has (ExecEntryT name)]
  [ExecConfig name skToPk] [ProofConfig name usage]
  (p: Participant) (b: Bytes) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    IsLongTermSecretKey name p b tr1 →
    IsLongTermSecretKey name p b tr2
:= by
  grind [IsLongTermSecretKey]

grind_pattern [grind_later] IsLongTermSecretKey_later => tr1 ≤ tr2, IsLongTermSecretKey name p b tr1

section

section
variable [BytesFunctor] [BytesLength] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable (name: String)
variable [ExecTraceTypes.Has <| ExecEntryT name]
variable {skToPk: Bytes → Bytes} {usage: Participant → Usage}
variable [ExecConfig name skToPk] [ProofConfig name usage]

public
instance [ProofConfig name usage]: PersistentLocalState.CompromisableLocalStateInv (SecretKeyState name) where
  invariant p st tr :=
    IsLongTermSecretKey name p st.sk tr
  invariant_later := by grind [IsLongTermSecretKey]
  invariant_implies_KnowableBy := by
    intro participant state tr h
    have: (label name participant (skToPk state.sk)).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      simp [Label.canFlow, label, LongTermKeyCompromised, PersistentLocalState.label_isCorrupt]
      grind
    grind [canFlowTrans, IsLongTermSecretKey]

public
instance: PersistentGlobalState.CompromisableGlobalStateInv (PublicKeyState name) where
  invariant st tr :=
    IsLongTermPublicKey name st.p st.pk tr
  invariant_later := by grind [ProofConfig.IsLongTermPublicKey_le]
  invariant_implies_KnowableBy := by
    intro state tr h
    have := ProofConfig.IsLongTermPublicKey_implies name state.p state.pk tr h
    grind [canFlowTrans]
end

#combine [BytesFunctor] (name: String) into ProofEntryT
from
  PersistentLocalState.CompromisableState (SecretKeyState name),
  PersistentGlobalState.CompromisableState (PublicKeyState name)

#combine
  [BytesFunctor] (name: String)
  [BytesLength] [BytesInvariants] [BytesInvariantsProofs]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  [ExecTraceTypes.Has <| ExecEntryT name]
  {skToPk: Bytes → Bytes} {usage: Participant → Usage}
  [ExecConfig name skToPk] [ProofConfig name usage]
into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem__noExecHas,
from
  PersistentLocalState.CompromisableState (SecretKeyState name),
  PersistentGlobalState.CompromisableState (PublicKeyState name)

end

@[instance]
public
theorem generateKeyPair.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage}

  [BytesFunctor.Has Random.SubF]

  [ExecTraceTypes.Has <| Random.ExecEntryT]
  [ProofTraceTypes.Has <| Random.ProofEntryT]
  [ExecTraceTypes.Has <| Network.ExecEntryT]
  [ProofTraceTypes.Has <| Network.ProofEntryT]
  [ExecTraceTypes.Has <| ExecEntryT name]
  [ProofTraceTypes.Has <| ProofEntryT name]

  [BytesInvariants.Has <| Random.invariants]

  [ExecConfig name skToPk] [ProofConfig name usage]
  [TraceInvariant.Has <| Random.ProofEntryT]
  [TraceInvariant.Has <| Network.ProofEntryT]
  [TraceInvariant.Has <| ProofEntryT name]
  (p: Participant)
  : HoareTriple
    (generateKeyPair name p)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold generateKeyPair
  dsimp only
  step with ⟨ fun sk => label name p (skToPk sk), usage p ⟩
  step by
    have := ProofConfig.IsLongTermPublicKey_implied name
    have := ProofConfig.IsLongTermPublicKey_implies name
    grind
  step by
    have := ProofConfig.IsLongTermPublicKey_implied name
    simp [PersistentGlobalState.GlobalStateInv.invariant]
    grind
  step by
    have := ProofConfig.IsLongTermPublicKey_implied name
    simp [PersistentLocalState.LocalStateInv.invariant, IsLongTermSecretKey]
    grind
  step
  trivial

@[instance]
public
theorem getPublicKey.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage}

  [BytesFunctor.Has Random.SubF]
  [ExecTraceTypes.Has <| ExecEntryT name]
  [ProofTraceTypes.Has <| ProofEntryT name]
  [ExecConfig name skToPk] [ProofConfig name usage]
  [TraceInvariant.Has <| ProofEntryT name]
  (p: Participant)
  : HoareTriple
    (getPublicKey name p tsPk)
    (fun _ => True)
    (fun res tr => ProofConfig.IsLongTermPublicKey name p res tr)
:= by
  unfold getPublicKey
  step
  step
  step
  simp_all [PersistentGlobalState.GlobalStateInv.invariant]

@[instance]
public
theorem getPrivateKey.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage}

  [BytesFunctor.Has Random.SubF]
  [ExecTraceTypes.Has <| ExecEntryT name]
  [ProofTraceTypes.Has <| ProofEntryT name]
  [ExecConfig name skToPk] [ProofConfig name usage]
  [TraceInvariant.Has <| ProofEntryT name]
  (p: Participant)
  : HoareTriple
    (getPrivateKey name p tsSk)
    (fun _ => True)
    (fun res tr => IsLongTermSecretKey name p res tr)
:= by
  unfold getPrivateKey
  step
  step
  simp_all [PersistentLocalState.LocalStateInv.invariant, IsLongTermSecretKey]

end Proof

section Reachability

variable
 [BytesFunctor]
 (name: String)
 {skToPk: Bytes → Bytes}
 [ExecConfig name skToPk]
 [ExecTraceTypes]
 [BytesFunctor.Has Random.SubF]
 [ExecTraceTypes.Has Random.ExecEntryT]
 [ExecTraceTypes.Has Network.ExecEntryT]
 [ExecTraceTypes.Has <| ExecEntryT name]

public
abbrev reachability : ReachabilityConfig :=
  .make (fun p => generateKeyPair name p)

variable
  [ProofTraceTypes]
  [TraceInvariant]

  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  {usage: Participant → Usage}

  [ProofTraceTypes.Has <| Random.ProofEntryT]
  [ProofTraceTypes.Has <| Network.ProofEntryT]
  [ProofTraceTypes.Has <| ProofEntryT name]

  [BytesInvariants.Has <| Random.invariants]

  [ProofConfig name usage]
  [TraceInvariant.Has <| Random.ProofEntryT]
  [TraceInvariant.Has <| Network.ProofEntryT]
  [TraceInvariant.Has <| ProofEntryT name]

public
instance: ReachableImpliesInvariant (reachability name) where
  pf p := generateKeyPair.spec name p

end Reachability

end DY.LongTermKeys
