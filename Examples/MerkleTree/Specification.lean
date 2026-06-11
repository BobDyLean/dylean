module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.Sign
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Actions.LongTermKeys
public import DY.Comparse

namespace DY.Example.MerkleTree

section MerkleTreeStructures

public
inductive MerkleTreeNode (Bytes: Type) (α: Type) where
  | Empty: MerkleTreeNode Bytes α
  | Leaf: α → MerkleTreeNode Bytes α
  | Internal: Bytes → Bytes → MerkleTreeNode Bytes α
deriving DecidableEq

end MerkleTreeStructures

-- this section could be metaprogrammed
section MerkleTreeFormats

def MerkleTreeNode.internalType (Bytes α: Type) : Fin 3 → Type
  | 0 => Unit
  | 1 => α
  | 2 => Bytes × Bytes

def MerkleTreeNode.internalType.mf (Bytes α: Type) [Comparse.BytesLike Bytes] (mf: Comparse.ExtensibleMessageFormat Bytes α): ∀ id, Comparse.ExtensibleMessageFormat Bytes (internalType Bytes α id)
  | 0 => Comparse.NonExtensibleMessageFormat.toExtensible .unit
  | 1 => mf
  | 2 => .prod (.slowBytes) (.bytes)

def MerkleTreeNode.mf
  {Bytes: Type} [Comparse.BytesLike Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  : Comparse.ExtensibleMessageFormat Bytes (MerkleTreeNode Bytes α)
:=
  .triviallyIsomorphic (.sigma (.fin8 3 (by decide)) (internalType.mf Bytes α mf))
  (fun ⟨id, x⟩ =>
    match id, x with
    | 0, x => MerkleTreeNode.Empty
    | 1, x => MerkleTreeNode.Leaf x
    | 2, (b1, b2) => MerkleTreeNode.Internal b1 b2
  )
  (fun x =>
    match x with
    | .Empty => ⟨ 0, () ⟩
    | .Leaf x => ⟨ 1, x ⟩
    | .Internal b1 b2 => ⟨ 2, (b1, b2) ⟩
  )
  (by grind)
  (by grind)

instance
  {Bytes: Type} [Comparse.BytesLike Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  [mf.IsNonAmbiguous]
  : ∀ id, ((MerkleTreeNode.internalType.mf Bytes α mf id).IsNonAmbiguous)
| 0 | 1 | 2 => by
  dsimp only [MerkleTreeNode.internalType.mf, MerkleTreeNode.internalType]
  infer_instance

instance
  {Bytes: Type} [Comparse.BytesLike Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  [mf.IsNonAmbiguous]
  : ((MerkleTreeNode.mf mf).IsNonAmbiguous)
:= by
  dsimp only [MerkleTreeNode.mf]
  infer_instance

@[simp]
theorem MerkleTreeNode.mf.wf_eq
  {Bytes: Type} [Comparse.BytesLike Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (pred: Bytes → Prop) [Comparse.BytesCompatiblePred pred]
  (x: MerkleTreeNode Bytes α)
  : (MerkleTreeNode.mf mf).wf pred x = (
      match x with
      | .Empty => True
      | .Leaf elem => mf.wf pred elem
      | .Internal left right => pred left ∧ pred right
    )
:= by
  cases x <;>
  simp [MerkleTreeNode.mf, MerkleTreeNode.internalType.mf, MerkleTreeNode.internalType]

end MerkleTreeFormats

section MerkleTreeDefs

-- adapted from Nat.nextPowerOfTwo
def previousPowerOfTwo (n : Nat) : Nat :=
  go 1 (by decide)
where
  go (power : Nat) (h : power > 0) : Nat :=
    if power * 2 < n then
      go (power * 2) (Nat.mul_pos h (by decide))
    else
      power
  termination_by n - power

/-- info: [(0, 1), (1, 1), (2, 1), (3, 2), (4, 2), (5, 4), (6, 4), (7, 4), (8, 4), (9, 8)] -/
#guard_msgs in
#eval List.range 10 |>.map (fun n => (n, previousPowerOfTwo n))

theorem previousPowerOfTwo_le (n: Nat): 2 ≤ n → previousPowerOfTwo n < n := by
  apply previousPowerOfTwo.go_le
where
  previousPowerOfTwo.go_le
    (n: Nat) (power: Nat) (h: power > 0)
    : power < n →
      previousPowerOfTwo.go n power h < n
  := by
    fun_induction previousPowerOfTwo.go n power h <;> grind

grind_pattern previousPowerOfTwo_le => previousPowerOfTwo n

theorem previousPowerOfTwo_mul_2_le (n: Nat): n ≤ (previousPowerOfTwo n)*2 := by
  apply previousPowerOfTwo.go_mul_2_le
where
  previousPowerOfTwo.go_mul_2_le
    (n: Nat) (power: Nat) (h: power > 0)
    : n ≤ (previousPowerOfTwo.go n power h)*2
  := by
    fun_induction previousPowerOfTwo.go n power h <;> grind

grind_pattern previousPowerOfTwo_mul_2_le => previousPowerOfTwo n

mutual

def merkleTreeHashInput
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α)
  : MerkleTreeNode Bytes α
:=
  match _: l with
  | [] =>
    .Empty
  | [x] =>
    .Leaf x
  | _::_::_ =>
    let k := previousPowerOfTwo l.length
    .Internal (merkleTreeHash mf (l.take k)) (merkleTreeHash mf (l.drop k))
termination_by (l.length, 0)
decreasing_by all_goals grind

public
def merkleTreeHash
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α)
  : Bytes
:=
  let node := merkleTreeHashInput mf l
  DY.Hash.hash ((MerkleTreeNode.mf mf).serialize node)
termination_by (l.length, 1)
decreasing_by grind

end

public
def mkInclusionProof
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α) (i: Nat) (h_i: i < l.length)
  : List Bytes
:=
  match _: l with
  | [x] => []
  | _::_::_ =>
    let k := previousPowerOfTwo l.length
    if _: i < k then
      (merkleTreeHash mf (l.drop k))::(mkInclusionProof mf (l.take k) i (by grind))
    else
      (merkleTreeHash mf (l.take k))::(mkInclusionProof mf (l.drop k) (i-k) (by grind))
termination_by l.length
decreasing_by all_goals grind

mutual

def inclusionProofToRootHashInput
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (proof: List Bytes) (leaf: α)
  (i: Nat) (length: Nat)
  : MerkleTreeNode Bytes α
:=
  match proof with
  | [] => .Leaf leaf
  | h::t =>
    let k := previousPowerOfTwo length
    if _: i < k then
      .Internal (inclusionProofToRootHash mf t leaf i k) h
    else
      .Internal h (inclusionProofToRootHash mf t leaf (i-k) (length-k))

def inclusionProofToRootHash
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (proof: List Bytes) (leaf: α)
  (i: Nat) (length: Nat)
  : Bytes
:=
  DY.Hash.hash ((MerkleTreeNode.mf mf).serialize (inclusionProofToRootHashInput mf proof leaf i length))

end

/-
  Sanity check: computing the root hash from an inclusion proof yields the correct root hash.
-/
def inclusionProofToRootHash_mkInclusionProof_correct
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α) (i: Nat) (h_i: i < l.length)
  : inclusionProofToRootHash mf (mkInclusionProof mf l i h_i) l[i] i l.length = merkleTreeHash mf l
:= by
  fun_induction mkInclusionProof mf l i h_i <;>
  grind [inclusionProofToRootHash, merkleTreeHash, inclusionProofToRootHashInput, merkleTreeHashInput]

/-
  Interesting fact:
  an inclusion proof for the last element of the list
  gives the correct root hash when computed for an index out-of-bounds.
  The reason is that for both the last index and index out-of-bounds,
  the else branch from `inclusionProofToRootHashInput` is always taken.
  This shows why when checking the inclusion proof,
  we must check that the index is in bounds of the (claimed) list length.
-/
def inclusionProofToRootHash_mkInclusionProof_outOfBounds
  {Bytes: Type}
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (l: List α)
  (i: Nat) (h_i: i+1 = l.length)
  (j: Nat) (h_j: l.length ≤ j)
  : inclusionProofToRootHash mf (mkInclusionProof mf l i (by grind)) (l[i]'(by grind)) j l.length = merkleTreeHash mf l
:= by
  fun_induction mkInclusionProof mf l i (by grind) generalizing j <;>
  grind [inclusionProofToRootHash, merkleTreeHash, inclusionProofToRootHashInput, merkleTreeHashInput]

public
def checkInclusionProof
  {Bytes: Type} [DecidableEq Bytes]
  [Comparse.BytesLike Bytes] [DY.Hash.CanHash Bytes]
  {α: Type} (mf: Comparse.ExtensibleMessageFormat Bytes α)
  (proof: List Bytes) (leaf: α) (i: Nat)
  (rootHash: Bytes) (length: Nat)
  : Prop
:=
  inclusionProofToRootHash mf proof leaf i length = rootHash ∧
  i < length
deriving Decidable

end MerkleTreeDefs

public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Literal.SubF]
  [bytesFunc1: BytesFunctor.Has Concat.SubF]
  [bytesFunc2: BytesFunctor.Has Hash.SubF]
  [bytesFunc3: BytesFunctor.Has Signature.SubF]
  [bytesFunc4: BytesFunctor.Has Random.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Literal.SubF.length]
  [bytesLen1: BytesLength.Has Concat.SubF.length]
  [bytesLen2: BytesLength.Has Hash.SubF.length]
  [bytesLen3: BytesLength.Has Signature.SubF.length]
  [bytesLen4: BytesLength.Has Random.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att1: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att2: AttackerKnowledge.Has Hash.attackerKnowledge]
  [att3: AttackerKnowledge.Has Signature.attackerKnowledge]
  [att4: AttackerKnowledge.Has Random.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.bytesFunc3
attribute [reducible, scoped instance] HasExecBytes.bytesFunc4
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [           scoped instance] HasExecBytes.bytesLen3
attribute [           scoped instance] HasExecBytes.bytesLen4
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2
attribute [           scoped instance] HasExecBytes.att3
attribute [           scoped instance] HasExecBytes.att4

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

structure SignedRootHashTBS where
  rootHash: Bytes
  length: Nat

structure SignedRootHash where
  tbs: SignedRootHashTBS
  sig: Bytes

structure ElementAndInclusionProof where
  element: Bytes
  i: Nat
  inclusionProof: List Bytes

structure ServerState where
  elements: List Bytes

inductive TheEvent where
  | ServerAuthenticated (server: Participant) (msg: Bytes)
  | ClientAccept (server: Participant) (msg: Bytes)
deriving DecidableEq

end Structures

public section Formats

open Comparse

variable [HasExecBytes]

instance SignedRootHashTBS.ps : ParseableSerializeableNE SignedRootHashTBS := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes .slowNat)
  (fun ⟨ rootHash, length ⟩ => { rootHash, length })
  (fun { rootHash, length } => ⟨ rootHash, length ⟩)

theorem SignedRootHashTBS.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: SignedRootHashTBS) (tr: τ):
  IsWellFormed pre x tr = pre x.rootHash tr
:= by
  simp [IsWellFormed, ParseableSerializeable.mf, ParseableSerializeableNE.mf]

grind_pattern SignedRootHashTBS.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SignedRootHashTBS.IsWellFormed_eq => IsWellFormed pre x tr

instance SignedRootHash.ps : ParseableSerializeableNE SignedRootHash := .make <|
  .triviallyIsomorphic
  (.prod SignedRootHashTBS.ps.mf .slowBytes)
  (fun ⟨ tbs, sig ⟩ => { tbs, sig })
  (fun { tbs, sig } => ⟨ tbs, sig ⟩)

theorem SignedRootHash.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: SignedRootHash) (tr: τ):
  IsWellFormed pre x tr = (
    IsWellFormed pre x.tbs tr ∧
    pre x.sig tr
  )
:= by
  simp [IsWellFormed, ParseableSerializeable.mf, ParseableSerializeableNE.mf]

grind_pattern SignedRootHash.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] SignedRootHash.IsWellFormed_eq => IsWellFormed pre x tr

instance ElementAndInclusionProof.ps: ParseableSerializeable ElementAndInclusionProof := .make <|
  .triviallyIsomorphic
  (.prod .slowBytes (.prod .slowNat (.list .slowBytes)))
  (fun ⟨ element, i, inclusionProof ⟩ => { element, i, inclusionProof })
  (fun { element, i, inclusionProof } => ⟨ element, i, inclusionProof ⟩)

theorem ElementAndInclusionProof.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ElementAndInclusionProof) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.element tr ∧
    (∀ b, b ∈ x.inclusionProof → pre b tr)
  )
:= by
  simp [IsWellFormed, ParseableSerializeable.mf]

grind_pattern ElementAndInclusionProof.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ElementAndInclusionProof.IsWellFormed_eq => IsWellFormed pre x tr

instance ServerState.ps: ParseableSerializeable ServerState := .make <|
  .triviallyIsomorphic
  (.list .slowBytes)
  (ServerState.mk)
  (ServerState.elements)

theorem ServerState.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: ServerState) (tr: τ):
  IsWellFormed pre x tr = (
    ∀ element, element ∈ x.elements → pre element tr
  )
:= by
  simp [IsWellFormed, ParseableSerializeable.mf]

grind_pattern ServerState.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] ServerState.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT TheEvent)]
  [traceExec3: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "MerkleTree PKI")]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT ServerState)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.traceExec4
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

instance: LongTermKeys.ExecConfig "MerkleTree PKI" Signature.vk where

def Server.authenticate (server: Participant) (msgHandles: List Nat) (skHandle: Nat): Traceful (Nat × Nat) := do
  let mut elements := #[]
  for handle in msgHandles do
    let msg ← Network.receiveMessage handle
    ProtocolEvent.logEvent (TheEvent.ServerAuthenticated server msg)
    elements := elements.push msg
  let sk ← LongTermKeys.getPrivateKey "MerkleTree PKI" server skHandle

  let rootHash := merkleTreeHash (.bytes) elements.toList
  let tbs: SignedRootHashTBS := { rootHash, length := elements.size }
  let tbsBytes: Bytes := Comparse.serialize tbs
  let sigNonce ← Random.genRand 32
  let sig := Signature.sign sk sigNonce tbsBytes
  let msg: SignedRootHash := { tbs, sig }

  let msgHandle ← Network.sendMessage (Comparse.serialize msg)
  let stHandle ← PersistentLocalState.storeLocalState server ({ elements := elements.toList}: ServerState)
  return (msgHandle, stHandle)

def Server.proveInclusion (server: Participant) (i: Nat) (stHandle: Nat): Traceful Nat := do
  let st: ServerState ← PersistentLocalState.getLocalState server stHandle
  let elements: List Bytes := st.elements
  -- the line below is like a dependent version of `guard (i < elements.length)`
  if h_i: ¬ (i < elements.length) then failure else
  let msg: ElementAndInclusionProof := {
    element := elements[i]
    i := i
    inclusionProof := mkInclusionProof (.bytes) elements i (by grind)
  }
  let msgHandle ← Network.sendMessage (Comparse.serialize msg)
  return msgHandle

def Client.checkInclusion (server: Participant) (msgSigHandle: Nat) (msgInclHandle: Nat) (pkHandle: Nat): Traceful Unit := do
  let vk ← LongTermKeys.getPublicKey "MerkleTree PKI" server pkHandle
  let signedRootBytes ← Network.receiveMessage msgSigHandle
  let signedRoot: SignedRootHash ← Comparse.parse signedRootBytes
  let elementBytes ← Network.receiveMessage msgInclHandle
  let element: ElementAndInclusionProof ← Comparse.parse elementBytes

  guard (Signature.verify vk (Comparse.serialize signedRoot.tbs) signedRoot.sig)
  guard (checkInclusionProof (.bytes) element.inclusionProof element.element element.i signedRoot.tbs.rootHash signedRoot.tbs.length)

  ProtocolEvent.logEvent (TheEvent.ClientAccept server element.element)

def ServerState.compromise (stHandle: Nat): Traceful Nat := do
  PersistentLocalState.compromise ServerState stHandle

end Specification

public section Reachability

variable [HasExecTrace]

@[expose] public section
def Server.authenticate.reachability: ReachabilityConfig := .make (fun (server, msgHandles, skHandle) => Server.authenticate server msgHandles skHandle)
def Server.proveInclusion.reachability: ReachabilityConfig := .make (fun (server, i, stHandle) => Server.proveInclusion server i stHandle)
def Client.checkInclusion.reachability: ReachabilityConfig := .make (fun (server, msgSigHandle, msgInclHandle, pkHandle) => Client.checkInclusion server msgSigHandle msgInclHandle pkHandle)
def ServerState.compromise.reachability: ReachabilityConfig := .make (fun stHandle => ServerState.compromise stHandle)
end

#combine into ReachabilityConfig from
  Network,
  LongTermKeys "MerkleTree PKI",
  Server.authenticate,
  Server.proveInclusion,
  Client.checkInclusion,
  ServerState.compromise,

end Reachability

end DY.Example.MerkleTree
