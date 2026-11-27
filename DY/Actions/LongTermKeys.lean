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
class ExecConfig [Bytes.Def] (name: String) (skToPk: outParam (Bytes → Bytes)) where

public
structure SecretKeyState [Bytes.Def] (name: String) where
  sk: Bytes

public -- it is useful to implement attacker programs
instance
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  (name: String)
  : Comparse.ParseableSerializeable (SecretKeyState name)
:= .make <|
  .triviallyIsomorphic
    (.bytes)
    (fun sk => { sk })
    (fun { sk := sk } => sk)

public -- it is useful to implement attacker programs
theorem SecretKeyState.IsWellFormed_eq
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: SecretKeyState name) (tr: τ):
  Comparse.IsWellFormed pre x tr = pre x.sk tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern SecretKeyState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

public -- it is useful to implement attacker programs
structure PublicKeyState [Bytes.Def] (name: String) where
  p: Participant
  pk: Bytes

public
instance
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  (name: String)
  : Comparse.ParseableSerializeable (PublicKeyState name)
:= .make <|
  .triviallyIsomorphic
    (.prod .unboundedString .bytes)
    (fun ⟨ p, pk ⟩ => { p, pk })
    (fun { p, pk } => ⟨ p, pk ⟩)

public -- it is useful to implement attacker programs
theorem PublicKeyState.IsWellFormed_eq
  [Bytes.Def] [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: PublicKeyState name) (tr: τ):
  Comparse.IsWellFormed pre x tr = pre x.pk tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern PublicKeyState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

#combine [Bytes.Def] (name: String) into
  ExecTrace,
  Trace.BaseAttackerKnows,
from
  PersistentLocalState.CompromisableState (SecretKeyState name),
  PersistentGlobalState.CompromisableState (PublicKeyState name)

variable [Bytes.Def]
variable (name: String)
variable {skToPk: Bytes → Bytes}
variable [ExecConfig name skToPk]

public
def generateKeyPair
  [ExecConfig name skToPk]
  [ExecTrace.Def]
  [Bytes.Has Random.BytesPart.Functor]
  [ExecTrace.Has Random.TracePart.Exec]
  [ExecTrace.Has Network.TracePart.Exec]
  [ExecTrace.Has <| TracePart.Exec name]
  (p: Participant)
  : Traceful (Nat × Nat × Nat)
:= do
  let sk ← Random.genRand 32
  let pk := skToPk sk
  let msgHandle ← Network.sendMessage pk
  let pkHandle ← PersistentGlobalState.storeGlobalState ({p, pk}: PublicKeyState name)
  let skHandle ← PersistentLocalState.storeLocalState p ({sk}: SecretKeyState name)
  pure (msgHandle, pkHandle, skHandle)

public
def getPublicKey
  [ExecTrace.Def]
  [ExecTrace.Has <| TracePart.Exec name]
  (p: Participant)
  (pkHandle: Nat)
  : Traceful Bytes
:= do
  let st: PublicKeyState name ← PersistentGlobalState.getGlobalState pkHandle
  guard (st.p = p)
  pure st.pk

public
def getPrivateKey
  [ExecTrace.Def]
  [ExecTrace.Has <| TracePart.Exec name]
  (p: Participant)
  (skHandle: Nat)
  : Traceful Bytes
:= do
  let st: SecretKeyState name ← PersistentLocalState.getLocalState p skHandle
  pure st.sk

public
def compromisePrivateKey
  [ExecTrace.Def]
  [ExecTrace.Has <| TracePart.Exec name]
  [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  [ExecTrace.Has Network.TracePart.Exec]
  (skHandle: Nat)
  : Traceful Nat
:= do
  PersistentLocalState.compromise (SecretKeyState name) skHandle

public
def LongTermKeyCompromised
  [ExecConfig name skToPk] [ExecTrace.Def] [ExecTrace.Has (TracePart.Exec name)]
  (participant: Participant) (pk: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  ∃ sk,
    pk = skToPk sk ∧
    PersistentLocalState.LocalStateCompromised participant ({ sk }: SecretKeyState name) tr

public
theorem LongTermKeyCompromised_le
  [ExecTrace.Def] [ExecTrace.Has (TracePart.Exec name)]
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
  [Bytes.Def]
  (name: String) {skToPk: Bytes → Bytes} [ExecConfig name skToPk]
  [ExecTrace.Def] [ExecTrace.Has (TracePart.Exec name)]
  (participant: Participant) (pk: Bytes)
  : Label
where
  isCorrupt := LongTermKeyCompromised name participant pk

public
class ProofConfig
  [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Bytes.Invariants.Def]
  (name: String) {skToPk: outParam (Bytes → Bytes)} (usage: outParam (Participant → Usage)) (lab: outParam (Participant → Bytes → Label))
  [ExecConfig name skToPk]
  [ExecTrace.Has (TracePart.Exec name)]
where
  IsLongTermPublicKey: Participant → Bytes → ProofTrace → Prop

  label_canFlow (name): ∀ p b tr, (lab p b).canFlow (label name p b) tr
  := by grind

  IsLongTermPublicKey_le: ∀ p b tr1 tr2,
    tr1 ≤ tr2 →
    IsLongTermPublicKey p b tr1 →
    IsLongTermPublicKey p b tr2
  := by grind

  IsLongTermPublicKey_implied (name): ∀ p b tr,
    b.Invariant tr →
    b.label tr = lab p (skToPk b) →
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
  [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Bytes.Invariants.Def]
  (name: String) {skToPk: Bytes → Bytes} (usage: Participant → Usage) (lab: Participant → Bytes → Label)
  [ExecTrace.Has (TracePart.Exec name)]
  [ExecConfig name skToPk] [ProofConfig name usage lab]
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
  [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Bytes.Invariants.Def]
  (name: String) {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}
  [ExecTrace.Has (TracePart.Exec name)]
  [ExecConfig name skToPk] [ProofConfig name usage lab]
  (p: Participant) (b: Bytes) (tr: ProofTrace)
  : Prop
:=
  b.Invariant tr ∧
  b.label tr = lab p (skToPk b) ∧
  b.HasUsage (usage p) tr

public
theorem IsLongTermSecretKey_later
  [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  (name: String) {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}
  [ExecTrace.Has (TracePart.Exec name)]
  [ExecConfig name skToPk] [ProofConfig name usage lab]
  (p: Participant) (b: Bytes) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    IsLongTermSecretKey name p b tr1 →
    IsLongTermSecretKey name p b tr2
:= by
  grind [IsLongTermSecretKey]

grind_pattern [grind_later] IsLongTermSecretKey_later => tr1 ≤ tr2, IsLongTermSecretKey name p b tr1

section

section
variable [Bytes.Def] [Bytes.length.Def] [ExecTrace.Def] [ProofTrace.Def] [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
variable [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
variable [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
variable [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]
variable (name: String)
variable [ExecTrace.Has <| TracePart.Exec name]
variable {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}
variable [ExecConfig name skToPk] [ProofConfig name usage lab]

public
instance: PersistentLocalState.CompromisableLocalStateInv (SecretKeyState name) where
  invariant p st tr :=
    IsLongTermSecretKey name p st.sk tr
  invariant_later := by grind [IsLongTermSecretKey]
  invariant_implies_KnowableBy := by
    intro participant state tr h
    have: (lab participant (skToPk state.sk)).canFlow (PersistentLocalState.label participant state) tr.erase := by
      cases state
      have := ProofConfig.label_canFlow name participant
      simp_all [Label.canFlow, label, LongTermKeyCompromised, PersistentLocalState.label_isCorrupt]
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

#combine [Bytes.Def] (name: String) into ProofTrace
from
  PersistentLocalState.CompromisableState (SecretKeyState name),
  PersistentGlobalState.CompromisableState (PublicKeyState name)

#combine
  [Bytes.Def] (name: String)
  [Bytes.length.Def] [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]
  [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]
  [ExecTrace.Has <| TracePart.Exec name]
  {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}
  [ExecConfig name skToPk] [ProofConfig name usage lab]
into
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable__noExecHas,
from
  PersistentLocalState.CompromisableState (SecretKeyState name),
  PersistentGlobalState.CompromisableState (PublicKeyState name)

end

@[instance]
public
theorem generateKeyPair.proof
  [Bytes.Def]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.length.Def] [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length] [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}

  [Bytes.Has Random.BytesPart.Functor]

  [ExecTrace.Has <| Random.TracePart.Exec]
  [ProofTrace.Has <| Random.TracePart.Proof]
  [ExecTrace.Has <| Network.TracePart.Exec]
  [ProofTrace.Has <| Network.TracePart.Proof]
  [ExecTrace.Has <| TracePart.Exec name]
  [ProofTrace.Has <| TracePart.Proof name]

  [Bytes.Invariants.Has <| Random.BytesPart.invariants]

  [ExecConfig name skToPk] [ProofConfig name usage lab]
  [Trace.Invariant.Has <| Random.TracePart.Proof]
  [Trace.Invariant.Has <| Network.TracePart.Proof]
  [Trace.Invariant.Has <| TracePart.Proof name]
  (p: Participant)
  : HoareTriple
    (generateKeyPair name p)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold generateKeyPair
  dsimp only
  step with ⟨ fun sk => lab p (skToPk sk), usage p ⟩
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
  grind

@[instance]
public
theorem getPublicKey.proof
  [Bytes.Def]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.length.Def] [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length] [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}

  [Bytes.Has Random.BytesPart.Functor]
  [ExecTrace.Has <| TracePart.Exec name]
  [ProofTrace.Has <| TracePart.Proof name]
  [ExecConfig name skToPk] [ProofConfig name usage lab]
  [Trace.Invariant.Has <| TracePart.Proof name]
  (p: Participant) (pkHandle: Nat)
  : HoareTriple
    (getPublicKey name p pkHandle)
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
theorem getPrivateKey.proof
  [Bytes.Def]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.length.Def] [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length] [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}

  [Bytes.Has Random.BytesPart.Functor]
  [ExecTrace.Has <| TracePart.Exec name]
  [ProofTrace.Has <| TracePart.Proof name]
  [ExecConfig name skToPk] [ProofConfig name usage lab]
  [Trace.Invariant.Has <| TracePart.Proof name]
  (p: Participant) (skHandle: Nat)
  : HoareTriple
    (getPrivateKey name p skHandle)
    (fun _ => True)
    (fun res tr => IsLongTermSecretKey name p res tr)
:= by
  unfold getPrivateKey
  step
  step
  simp_all [PersistentLocalState.LocalStateInv.invariant, IsLongTermSecretKey]

@[instance]
public
theorem compromisePrivateKey.proof
  [Bytes.Def]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.length.Def] [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length] [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]

  (name: String)
  {skToPk: Bytes → Bytes} {usage: Participant → Usage} {lab: Participant → Bytes → Label}

  [Bytes.Has Random.BytesPart.Functor]
  [ExecTrace.Has <| TracePart.Exec name]
  [ProofTrace.Has <| TracePart.Proof name]
  [ExecConfig name skToPk] [ProofConfig name usage lab]
  [Trace.Invariant.Has <| TracePart.Proof name]
  [ExecTrace.Has <| Network.TracePart.Exec]
  [ProofTrace.Has <| Network.TracePart.Proof]
  [Trace.Invariant.Has <| Network.TracePart.Proof]
  (skHandle: Nat)
  : HoareTriple
    (compromisePrivateKey name skHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold compromisePrivateKey
  step
  grind

end Proof

section Reachability

variable
 [Bytes.Def]
 (name: String)
 {skToPk: Bytes → Bytes}
 [ExecConfig name skToPk]
 [ExecTrace.Def]
 [Bytes.Has Random.BytesPart.Functor]
 [ExecTrace.Has Random.TracePart.Exec]
 [ExecTrace.Has Network.TracePart.Exec]
 [ExecTrace.Has <| TracePart.Exec name]

@[expose]
public
def generateKeyPair.transitionSystem : TransitionSystem :=
  .make (fun p => generateKeyPair name p)

variable
  [Bytes.length.Def]
  [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length]
  [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length]

@[expose]
public
def compromisePrivateKey.transitionSystem : TransitionSystem :=
  .make (fun skHandle => compromisePrivateKey name skHandle)

@[expose]
public
def transitionSystem.internal : Fin 2 → TransitionSystem
  | 0 => generateKeyPair.transitionSystem name
  | 1 => compromisePrivateKey.transitionSystem name

@[expose]
public
def transitionSystem : TransitionSystem
:=
  .combine (transitionSystem.internal name)

public instance: TransitionSystem.HasStep (generateKeyPair.transitionSystem name) (transitionSystem name) := inferInstanceAs <| TransitionSystem.HasStep (transitionSystem.internal name 0) (.combine (transitionSystem.internal name))
public instance: TransitionSystem.HasStep (compromisePrivateKey.transitionSystem name) (transitionSystem name) := inferInstanceAs <| TransitionSystem.HasStep (transitionSystem.internal name 1) (.combine (transitionSystem.internal name))

variable
  [ProofTrace.Def]
  [Trace.Invariant.Def]

  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.length.Def] [Bytes.Has Literal.BytesPart.Functor] [Bytes.length.Has Literal.BytesPart.length] [Bytes.Has Concat.BytesPart.Functor] [Bytes.length.Has Concat.BytesPart.length] [Bytes.Invariants.Has Literal.BytesPart.invariants] [Bytes.Invariants.Has Concat.BytesPart.invariants]
  {usage: Participant → Usage}
  {lab: Participant → Bytes → Label}

  [ProofTrace.Has <| Random.TracePart.Proof]
  [ProofTrace.Has <| Network.TracePart.Proof]
  [ProofTrace.Has <| TracePart.Proof name]

  [Bytes.Invariants.Has <| Random.BytesPart.invariants]

  [ProofConfig name usage lab]
  [Trace.Invariant.Has <| Random.TracePart.Proof]
  [Trace.Invariant.Has <| Network.TracePart.Proof]
  [Trace.Invariant.Has <| TracePart.Proof name]

public
instance: Trace.Reachable_implies_Invariant.Part (generateKeyPair.transitionSystem name) where
  pf p := generateKeyPair.proof name p

public
instance: Trace.Reachable_implies_Invariant.Part (compromisePrivateKey.transitionSystem name) where
  pf p := compromisePrivateKey.proof name p

public instance: ∀ id, Trace.Reachable_implies_Invariant.Part (transitionSystem.internal name id)
  | 0 => inferInstanceAs <| Trace.Reachable_implies_Invariant.Part (generateKeyPair.transitionSystem name)
  | 1 => inferInstanceAs <| Trace.Reachable_implies_Invariant.Part (compromisePrivateKey.transitionSystem name)

public instance: Trace.Reachable_implies_Invariant.Part (transitionSystem name) := inferInstanceAs (Trace.Reachable_implies_Invariant.Part (.combine (transitionSystem.internal name)))

end Reachability

end DY.LongTermKeys
