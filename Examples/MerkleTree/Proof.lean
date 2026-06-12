module

import DY.Meta.Step
import DY.Meta.Utils
public import Examples.MerkleTree.Specification
import all Examples.MerkleTree.Specification

namespace DY.Example.MerkleTree

public section MerkleTreeProof

def IsHashCollision
  {Bytes: Type}
  [DY.Hash.CanHash Bytes]
  (x: Bytes × Bytes)
  : Prop
:=
  let (b1, b2) := x
  b1 ≠ b2 ∧
  DY.Hash.hash b1 = DY.Hash.hash b2

def merkleTreeHash_reduceCollision
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  [DecidableEq Bytes] [DecidableEq α]
  (l1 l2: List α)
  : Bytes × Bytes
:=
  let hashInput1 := merkleTreeHashInput mf l1
  let hashInput2 := merkleTreeHashInput mf l2
  if l1 = l2 then
    (Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  else if ¬ (hashInput1 = hashInput2) then
    ((MerkleTreeNode.mf mf).serialize hashInput1, (MerkleTreeNode.mf mf).serialize hashInput2)
  else
    if _: l1 matches _::_::_ ∧ l2 matches _::_::_ then
      let k1 := previousPowerOfTwo l1.length
      let left1 := l1.take k1
      let right1 := l1.drop k1
      let k2 := previousPowerOfTwo l2.length
      let left2 := l2.take k2
      let right2 := l2.drop k2
      if _: ¬ (left1 = left2) then
        merkleTreeHash_reduceCollision mf left1 left2
      else if _: ¬ (right1 = right2) then
        merkleTreeHash_reduceCollision mf right1 right2
      else
        (Comparse.BytesLike.empty, Comparse.BytesLike.empty)
    else
      (Comparse.BytesLike.empty, Comparse.BytesLike.empty)
termination_by l1.length
decreasing_by all_goals grind

theorem merkleTreeHash_reduceCollision_correct
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  [DecidableEq Bytes] [DecidableEq α]
  [mf.IsNonAmbiguous]
  (l1 l2: List α)
  (h: merkleTreeHash mf l1 = merkleTreeHash mf l2)
  : l1 = l2 ∨
    IsHashCollision (merkleTreeHash_reduceCollision mf l1 l2)
:= by
  fun_induction merkleTreeHash_reduceCollision mf l1 l2
  · left; rfl
  · right
    grind [merkleTreeHash, IsHashCollision, Comparse.ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv]
  · right
    grind [merkleTreeHashInput, merkleTreeHash]
  · right
    grind [merkleTreeHashInput, merkleTreeHash]
  · exfalso
    grind [List.take_append_drop]
  · exfalso
    grind (splits := 8) [cases List, merkleTreeHashInput]

def checkInclusionProof_reduceHashCollision
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  [DecidableEq Bytes] [DecidableEq α]
  (proof: List Bytes) (leaf: α)
  (i: Nat) (l: List α)
  : Bytes × Bytes
:=
  let hashInput1 := merkleTreeHashInput mf l
  let hashInput2 := inclusionProofToRootHashInput mf proof leaf i l.length
  if l[i]? = some leaf then
    (Comparse.BytesLike.empty, Comparse.BytesLike.empty)
  else if ¬ (hashInput1 = hashInput2) then
    ((MerkleTreeNode.mf mf).serialize hashInput1, (MerkleTreeNode.mf mf).serialize hashInput2)
  else
    match proof with
    | _::proofTail =>
      let k := previousPowerOfTwo l.length
      if i < k then
        checkInclusionProof_reduceHashCollision mf proofTail leaf i (l.take k)
      else
        checkInclusionProof_reduceHashCollision mf proofTail leaf (i-k) (l.drop k)
    | [] => (Comparse.BytesLike.empty, Comparse.BytesLike.empty)

theorem checkInclusionProof_reduceHashCollision_correct
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  [DecidableEq Bytes] [DecidableEq α]
  [mf.IsNonAmbiguous]
  (proof: List Bytes) (leaf: α)
  (i: Nat)
  (l: List α)
  (h: checkInclusionProof mf proof leaf i (merkleTreeHash mf l) l.length)
  : l[i]? = some leaf ∨
    IsHashCollision (checkInclusionProof_reduceHashCollision mf proof leaf i l)
:= by
  fun_induction checkInclusionProof_reduceHashCollision mf proof leaf i l
  · left; assumption
  · right
    grind [checkInclusionProof, inclusionProofToRootHash, merkleTreeHash, IsHashCollision, Comparse.ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv]
  · have := merkleTreeHashInput.eq_def mf -- ?
    grind [checkInclusionProof, inclusionProofToRootHashInput]
  · have := merkleTreeHashInput.eq_def mf -- ?
    grind [checkInclusionProof, inclusionProofToRootHashInput]
  · exfalso
    have := merkleTreeHashInput.eq_def mf -- ?
    grind [checkInclusionProof, inclusionProofToRootHashInput]


end MerkleTreeProof

public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT TheEvent)]
  [traceProof3: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "MerkleTree PKI")]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerState)]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

structure LongTermKeyUsage where
  principal: Participant

open Comparse in
instance : ParseableSerializeable LongTermKeyUsage := .make <|
  .triviallyIsomorphic
    (.string)
    (fun principal => { principal })
    (fun { principal := principal } => principal)

@[grind]
def mkLongTermKeyUsage (me: Participant): Usage := {
  type := "SigKey",
  tag := "SignedDH PKI",
  data := Comparse.serialize ({ principal := me }: LongTermKeyUsage)
}

instance MerkleTreeSignPred
  : Signature.SignPred
where
  pred skUsg _vk msg tr :=
    ∃ server, skUsg = mkLongTermKeyUsage server ∧ (
      match Comparse.parse msg with
      | none => False
      | some (tbs: SignedRootHashTBS) => (
        ∃ elements,
          tbs.rootHash = merkleTreeHash .bytes elements ∧
          tbs.length = elements.length ∧
          (∀ element, element ∈ elements → tr.erase.EventLogged (TheEvent.ServerAuthenticated server element))
      )
    )

instance
  [HasProofTrace]
  [BytesInvariants]
  : Signature.SignPredProof
where
  pred_later := by
    simp [Signature.SignPred.pred]
    grind

end BytesInvariants

public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInv0: BytesInvariantsProofs]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has Hash.invariants]
  [bytesInv4: BytesInvariants.Has Signature.invariants]
  [bytesInv5: BytesInvariants.Has Random.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3
attribute [           scoped instance] HasBytesInvariants.bytesInv4
attribute [           scoped instance] HasBytesInvariants.bytesInv5

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

instance TheEvent.invariant [HasProofTrace] : ProtocolEvent.EventInv (TheEvent)
where
  invariant tr ev :=
    match ev with
    | .ServerAuthenticated .. => True
    | .ClientAccept server element =>
      tr.erase.EventLogged (TheEvent.ServerAuthenticated server element) ∨
      (∃ spk, (LongTermKeys.label "MerkleTree PKI" server spk).isCorrupt tr.erase)

@[grind]
instance : LongTermKeys.ProofConfig "MerkleTree PKI" mkLongTermKeyUsage (LongTermKeys.label "MerkleTree PKI")
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "MerkleTree PKI" who vk ∧
    vk.SignkeyHasUsage (mkLongTermKeyUsage who) tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

instance ServerStateInv : PersistentLocalState.CompromisableLocalStateInv ServerState
where
  invariant me st tr :=
    Comparse.IsWellFormed Bytes.Publishable st tr
  invariant_later := by grind
  invariant_implies_KnowableBy participant state tr := by
    grind [canFlowTrans]

end TraceInvariant

public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT TheEvent)]
  [traceInv3: TraceInvariant.Has (LongTermKeys.ProofEntryT "MerkleTree PKI")]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT ServerState)]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

section Proofs

theorem pred_merkleTreeHash
  [HasBytesInvariants]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α)
  (pred: Bytes → Prop) [Comparse.BytesCompatiblePred pred] (h_pred: ∀ b, pred b → pred (Hash.hash b))
  : (∀ x ∈ l, mf.wf pred x) →
    pred (merkleTreeHash mf l)
:= by
  intro h_l
  simp only [merkleTreeHash]
  apply h_pred
  suffices (MerkleTreeNode.mf mf).wf pred (merkleTreeHashInput mf l) by simp_all [Comparse.ExtensibleMessageFormat.wf_eq]
  exact match _: l with
  | [] => by
    simp [merkleTreeHashInput]
  | [x] => by
    simp [merkleTreeHashInput]
    grind
  | _::_::_ => by
    simp [merkleTreeHashInput]
    have := pred_merkleTreeHash mf (l.take (previousPowerOfTwo l.length)) pred h_pred
    have := pred_merkleTreeHash mf (l.drop (previousPowerOfTwo l.length)) pred h_pred
    grind
termination_by l.length
decreasing_by all_goals grind

theorem pred_mkInclusionProof
  [HasBytesInvariants]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α) (i: Nat) (h_i: i < l.length)
  (pred: Bytes → Prop) [Comparse.BytesCompatiblePred pred] (h_pred: ∀ b, pred b → pred (Hash.hash b))
  : (∀ x ∈ l, mf.wf pred x) →
    (∀ x ∈ mkInclusionProof mf l i h_i, pred x)
:=
  match _: l with
  | [x] => by
    simp [mkInclusionProof]
  | _::_::_ =>
    let k := previousPowerOfTwo l.length
    if h_i_k: i < k then by
      simp [mkInclusionProof]
      have := pred_merkleTreeHash mf (l.drop k) pred (by assumption)
      have := pred_mkInclusionProof mf (l.take k) i (by grind) pred (by assumption)
      grind
    else by
      simp [mkInclusionProof]
      have := pred_merkleTreeHash mf (l.take k) pred (by assumption)
      have := pred_mkInclusionProof mf (l.drop k) (i-k) (by grind) pred (by assumption)
      grind
termination_by l.length
decreasing_by all_goals grind

attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

@[grind]
def Server.authenticate.loopInv
  [HasTraceInvariant]
  (server: Participant)
  (handles: List Nat)
  : handles.Cursor × Array Bytes → ProofTrace → Prop
:=
  fun (_, elements) tr =>
    ∀ msg, msg ∈ elements → (
      msg.Publishable tr ∧
      tr.erase.EventLogged (TheEvent.ServerAuthenticated server msg)
    )

theorem Server.authenticate.loopInv_le
  [HasTraceInvariant]
  (server: Participant) (handles: List Nat)
  (x: handles.Cursor × Array Bytes)
  (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    Server.authenticate.loopInv server handles x tr1 →
    Server.authenticate.loopInv server handles x tr2
:= by
  grind [Server.authenticate.loopInv]

grind_pattern [grind_later] Server.authenticate.loopInv_le => tr1 ≤ tr2, Server.authenticate.loopInv server handles x tr1

@[instance]
theorem Server.authenticate.spec
  [HasTraceInvariant]
  (server: Participant) (msgHandles: List Nat) (skHandle: Nat)
  : HoareTriple
    (Server.authenticate server msgHandles skHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Server.authenticate
  step_intro
  step with ⟨({ inv := loopInv server msgHandles, step := ?_ }: LoopInvariantAndProof _ _)⟩ by grind
  step_intro
  step
  step_intro
  step_intro
  step_intro
  step with ⟨ fun _ => Label.secret, Usage.nothing ⟩
  have: rootHash.Publishable tr := by
    have := pred_merkleTreeHash .bytes elements.toList (Bytes.Publishable · tr) (by simp [Bytes.Publishable]) (by simp; grind)
    grind
  step with ⟨ mkLongTermKeyUsage server ⟩ by
    dsimp only [Signature.SignPred.pred]
    grind
  step_intro
  have: tbsBytes.Publishable tr := by grind
  have: sig.Publishable tr := by grind
  step
  step by dsimp only [PersistentLocalState.LocalStateInv.invariant]; grind
  step
  grind
where finally
  · intro pref cur suff h messages
    step_intro
    step
    step by simp [ProtocolEvent.EventInv.invariant]
    step_intro
    step
    step
    simp_all
    grind

@[instance]
theorem Server.proveInclusion.spec
  [HasTraceInvariant]
  (server: Participant) (i: Nat) (stHandle: Nat)
  : HoareTriple
    (Server.proveInclusion server i stHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Server.proveInclusion
  step
  step_intro
  split
  · step; grind
  step_intro
  have: elements[i].Publishable tr := by simp_all [PersistentLocalState.LocalStateInv.invariant]; grind
  have: ∀ element, element ∈ mkInclusionProof .bytes elements i (by grind) → element.Publishable tr := by
    have := pred_mkInclusionProof .bytes elements i (by grind) (Bytes.Publishable · tr) (by simp [Bytes.Publishable]) (by simp_all [PersistentLocalState.LocalStateInv.invariant]; grind)
    grind
  step
  step
  grind

@[instance]
theorem Client.checkInclusion.spec
  [HasTraceInvariant]
  (server: Participant) (msgSigHandle: Nat) (msgInclHandle: Nat) (pkHandle: Nat)
  : HoareTriple
    (Client.checkInclusion server msgSigHandle msgInclHandle pkHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold Client.checkInclusion
  step
  step
  step
  step
  step
  step with ⟨ mkLongTermKeyUsage server ⟩
  step
  step by
    have := checkInclusionProof_reduceHashCollision_correct .bytes element.inclusionProof element.element element.i
    simp [ProtocolEvent.EventInv.invariant]
    simp_all [Signature.SignPred.pred]
    grind [Hash.hash_inj, IsHashCollision]
  grind

@[instance]
theorem ServerState.compromise.spec [HasTraceInvariant] (stHandle: Nat): HoareTriple (ServerState.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold ServerState.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

public instance: ReachableImpliesInvariant Server.authenticate.reachability := .mk (fun (server, msgHandles, skHandle) => Server.authenticate.spec server msgHandles skHandle)
public instance: ReachableImpliesInvariant Server.proveInclusion.reachability := .mk (fun (server, i, stHandle) => Server.proveInclusion.spec server i stHandle)
public instance: ReachableImpliesInvariant Client.checkInclusion.reachability := .mk (fun (server, msgSigHandle, msgInclHandle, pkHandle) => Client.checkInclusion.spec server msgSigHandle msgInclHandle pkHandle)
public instance: ReachableImpliesInvariant ServerState.compromise.reachability := .mk (fun (stHandle) => ServerState.compromise.spec stHandle)

#combine into ReachabilityTheorem from
  Network,
  LongTermKeys "MerkleTree PKI",
  Server.authenticate,
  Server.proveInclusion,
  Client.checkInclusion,
  ServerState.compromise,

end ReachabilityImpliesInvariant

end DY.Example.MerkleTree
