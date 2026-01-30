import DY.Bytes.Type
import DY.Label
import DY.Trace

/-
  This module allows to define invariants on `Bytes`.
  TODO: explain what is happening once things are stabilized
-/

namespace DY

variable [BytesFunctor]

-- Well formed

def BytesWellFormedT := ProofTrace → Prop

class BytesWellFormed where
  funs: Bytes.Function BytesWellFormedT

def Bytes.WellFormed [BytesWellFormed] (b: Bytes) : BytesWellFormedT :=
  Bytes.rec BytesWellFormed.funs b

class HasBytesWellFormed [BytesWellFormed] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF BytesWellFormedT)) where
  pf: Bytes.SubFunction binv BytesWellFormed.funs
  dummy: Unit -- leanprover/lean4#11477 workaround

@[simp]
theorem Bytes.WellFormed.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [BytesWellFormed]
  {binv: Bytes.PartialFunction SubF BytesWellFormedT}
  [tc: HasBytesWellFormed binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.WellFormed tr = binv b (fun y _ => Bytes.WellFormed y) tr
  := by
    apply congrFun
    have := tc.pf
    apply Bytes.rec_eq

grind_pattern Bytes.WellFormed.eq => b.pack.WellFormed tr

-- Well formed later

def BytesWellFormedLaterT (bwf: BytesWellFormedT) :=
  ∀ tr1 tr2, tr1 ≤ tr2 → bwf tr1 → bwf tr2

class BytesWellFormedLater [BytesWellFormed] where
  proofs: Bytes.Proof1 BytesWellFormed.funs BytesWellFormedLaterT

theorem Bytes.WellFormed.later
  [BytesWellFormed] [BytesWellFormedLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.WellFormed b tr1 →
  Bytes.WellFormed b tr2
  := by
    apply BytesWellFormedLater.proofs.prove

grind_pattern Bytes.WellFormed.later => Bytes.WellFormed b tr1, tr1 ≤ tr2

-- Usage

structure Usage where
  type: String
  tag: String
  data: Option Bytes

def Usage.nothing: Usage where
  type := ""
  tag := ""
  data := none

def GetUsageT := ProofTrace → Usage

class GetUsage where
  funs: Bytes.Function GetUsageT

def Bytes.usage [GetUsage] (b: Bytes) : GetUsageT :=
  Bytes.rec GetUsage.funs b

class HasGetUsage [GetUsage] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF GetUsageT)) where
  pf: Bytes.SubFunction binv GetUsage.funs
  dummy: Unit -- leanprover/lean4#11477 workaround

@[simp]
theorem Bytes.usage.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [GetUsage]
  {binv: Bytes.PartialFunction SubF GetUsageT}
  [tc: HasGetUsage binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.usage tr = binv b (fun y _ => Bytes.usage y) tr
  := by
    apply congrFun
    have := tc.pf
    apply Bytes.rec_eq

grind_pattern Bytes.usage.eq => (b.pack).usage tr

-- Usage later

def GetUsageLaterT (x: BytesWellFormedT × GetUsageT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

class GetUsageLater [BytesWellFormed] [GetUsage] where
  proofs: Bytes.Proof2 BytesWellFormed.funs GetUsage.funs GetUsageLaterT

theorem Bytes.usage_later
  [BytesWellFormed] [GetUsage] [GetUsageLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.WellFormed b tr1 →
  Bytes.usage b tr1 = Bytes.usage b tr2
  := by
    apply GetUsageLater.proofs.prove

grind_pattern Bytes.usage_later => Bytes.usage b tr1, tr1 ≤ tr2

-- Label

def GetLabelT := ProofTrace → Label

class GetLabel where
  funs: Bytes.Function GetLabelT

def Bytes.label [GetLabel] (b: Bytes) : GetLabelT :=
  Bytes.rec GetLabel.funs b

class HasGetLabel [GetLabel] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF GetLabelT)) where
  pf: Bytes.SubFunction binv GetLabel.funs
  dummy: Unit -- leanprover/lean4#11477 workaround

@[simp]
theorem Bytes.label.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [GetLabel]
  {binv: Bytes.PartialFunction SubF GetLabelT}
  [tc: HasGetLabel binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.label tr = binv b (fun y _ => Bytes.label y) tr
  := by
    apply congrFun
    have := tc.pf
    apply Bytes.rec_eq

grind_pattern Bytes.label.eq => b.pack.label tr

-- Label later

def GetLabelLaterT (x: BytesWellFormedT × GetLabelT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

class GetLabelLater [BytesWellFormed] [GetLabel] where
  proofs: Bytes.Proof2 BytesWellFormed.funs GetLabel.funs GetLabelLaterT

theorem Bytes.label_later
  [BytesWellFormed] [GetLabel] [GetLabelLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.WellFormed b tr1 →
  Bytes.label b tr1 = Bytes.label b tr2
  := by
    apply GetLabelLater.proofs.prove

grind_pattern Bytes.label_later => Bytes.label b tr1, tr1 ≤ tr2

-- Invariant

def BytesInvariantT := ProofTrace → Prop

class BytesInvariant where
  funs: Bytes.Function BytesInvariantT

def Bytes.Invariant [BytesInvariant] (b: Bytes) (tr: ProofTrace) : Prop :=
  Bytes.rec BytesInvariant.funs b tr

class HasBytesInvariant [BytesInvariant] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF BytesInvariantT)) where
  pf: Bytes.SubFunction binv BytesInvariant.funs
  dummy: Unit -- leanprover/lean4#11477 workaround

@[simp]
theorem Bytes.Invariant.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [BytesInvariant]
  {binv: Bytes.PartialFunction SubF BytesInvariantT}
  [tc: HasBytesInvariant binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.Invariant tr = binv b (fun y _ => Bytes.Invariant y) tr
  := by
    apply congrFun
    have := tc.pf
    apply Bytes.rec_eq

grind_pattern Bytes.Invariant.eq => Bytes.Invariant (b.pack) tr

-- Invariant implies well formed

def BytesInvariantImpliesBytesWellFormedT (x: BytesInvariantT × BytesWellFormedT) :=
  let (binv, bwf) := x
  ∀ tr, binv tr → bwf tr

class BytesInvariantImpliesBytesWellFormed [BytesWellFormed] [BytesInvariant] where
  proofs: Bytes.Proof2 BytesInvariant.funs BytesWellFormed.funs BytesInvariantImpliesBytesWellFormedT

theorem Bytes.Invariant_implies_WellFormed
  [BytesWellFormed] [BytesInvariant] [BytesInvariantImpliesBytesWellFormed]
  (b: Bytes)
  (tr: ProofTrace)
  :
  Bytes.Invariant b tr →
  Bytes.WellFormed b tr
  := by
    apply BytesInvariantImpliesBytesWellFormed.proofs.prove

grind_pattern Bytes.Invariant_implies_WellFormed => Bytes.WellFormed b tr

-- Invariant later

def BytesInvariantLaterT (binv: BytesInvariantT) :=
  ∀ tr1 tr2, tr1 ≤ tr2 → binv tr1 → binv tr2

class BytesInvariantLater [BytesInvariant] where
  proofs: Bytes.Proof1 BytesInvariant.funs BytesInvariantLaterT

theorem Bytes.Invariant.later
  [BytesInvariant] [BytesInvariantLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.Invariant b tr1 →
  Bytes.Invariant b tr2
  := by
    apply BytesInvariantLater.proofs.prove

grind_pattern Bytes.Invariant.later => Bytes.Invariant b tr1, tr1 ≤ tr2

/--
  To reduce the boilerplate required to combine all (sub-)invariants,
  we bundle them into this structure,
  so that instead of having to combine each function separately,
  we can simply combine this bundle of functions.
  However, such a bundling prevents
  e.g. the definition of `invariant` to assume that
  `well_formed` is constructed in some particular way
  (e.g. that it contains some Pk invariants).
  Later on we will define properties on these (sub-)invariants:
  we do not bundle them here because in these proofs
  we want to be able to assume a particular implementation of `well_formed`.
-/
structure Bytes.PartialInvariants (SubF: Type → Type) [SubBytesFunctor SubF] where
  well_formed: Bytes.PartialFunction SubF BytesWellFormedT
  usage: Bytes.PartialFunction SubF GetUsageT
  label: [GetUsage] → Bytes.PartialFunction SubF GetLabelT
  invariant: [BytesWellFormed] → [GetUsage] → [GetLabel] → Bytes.PartialFunction SubF BytesInvariantT

class BytesInvariants where
  invs: Bytes.PartialInvariants BytesF

instance [BytesInvariants]: BytesWellFormed where
  funs := BytesInvariants.invs.well_formed

instance [BytesInvariants]: GetUsage where
  funs := BytesInvariants.invs.usage

instance [BytesInvariants]: GetLabel where
  funs := BytesInvariants.invs.label

instance [BytesInvariants]: BytesInvariant where
  funs := BytesInvariants.invs.invariant

/-
  Note: in the tactic scripts provided below,
  we would want to allow `grind` to unfold definitions of `DY.ALaCarte.FunctorSizeOf.sizeOf`.
  Unfortunately, this doesn't work because of lean4#11708.
  Therefore, we put it in the `simp_all`,
  however this might not work for `FunctorSizeOf.sizeOf` instantiated by the lemma `Bytes.sizeOf_view`.
  In this case, the workaround is to write
  a custom lemma proving the unfolding of `FunctorSizeOf.sizeOf`
  and adding a grind pattern.
-/
structure Bytes.PartialInvariantsProofs [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] (invs: Bytes.PartialInvariants SubF) where
  well_formed_later: Bytes.PartialProof1 invs.well_formed Bytes.WellFormed BytesWellFormedLaterT
  := by
    intro x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesWellFormedLaterT] <;> grind

  usage_later: Bytes.PartialProof2 invs.well_formed invs.usage Bytes.WellFormed Bytes.usage GetUsageLaterT
  := by
    intro x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetUsageLaterT] <;> grind

  label_later: [GetUsageLater] → Bytes.PartialProof2 invs.well_formed invs.label Bytes.WellFormed Bytes.label GetLabelLaterT
  := by
    intro _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetLabelLaterT] <;> grind

  invariant_implies_wellformed: Bytes.PartialProof2 invs.invariant invs.well_formed Bytes.Invariant Bytes.WellFormed BytesInvariantImpliesBytesWellFormedT
  := by
    intro x rec tr
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantImpliesBytesWellFormedT] <;> grind

  invariant_later: [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] → [BytesInvariantImpliesBytesWellFormed] → Bytes.PartialProof1 invs.invariant Bytes.Invariant BytesInvariantLaterT
  := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT] <;> grind

class BytesInvariantsProofs [BytesInvariants] where
  pfs: Bytes.PartialInvariantsProofs (BytesInvariants.invs)

instance [BytesInvariants] [BytesInvariantsProofs]: BytesWellFormedLater where
  proofs := BytesInvariantsProofs.pfs.well_formed_later

instance [BytesInvariants] [BytesInvariantsProofs]: GetUsageLater where
  proofs := BytesInvariantsProofs.pfs.usage_later

instance [BytesInvariants] [BytesInvariantsProofs]: GetLabelLater where
  proofs := BytesInvariantsProofs.pfs.label_later

instance [BytesInvariants] [BytesInvariantsProofs]: BytesInvariantImpliesBytesWellFormed where
  proofs := BytesInvariantsProofs.pfs.invariant_implies_wellformed

instance [BytesInvariants] [BytesInvariantsProofs]: BytesInvariantLater where
  proofs := BytesInvariantsProofs.pfs.invariant_later

class BytesInvariants.HasStep
  [BytesInvariants]
  {SubF1 SubF2: Type → Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  (partialInvs1: outParam (Bytes.PartialInvariants SubF1))
  (partialInvs2: Bytes.PartialInvariants SubF2)
  where
    [well_formed_sub: Bytes.SubFunctionStep partialInvs1.well_formed partialInvs2.well_formed]
    [usage_sub: Bytes.SubFunctionStep partialInvs1.usage partialInvs2.usage]
    [label_sub: Bytes.SubFunctionStep partialInvs1.label partialInvs2.label]
    [invariant_sub: Bytes.SubFunctionStep partialInvs1.invariant partialInvs2.invariant]

class BytesInvariants.Has
  [BytesInvariants]
  {SubF: Type → Type}
  [SubBytesFunctor SubF]
  [BytesFunctor.Has SubF]
  (partialInvs: outParam (Bytes.PartialInvariants SubF))
  where
    [well_formed_sub: Bytes.SubFunction partialInvs.well_formed BytesWellFormed.funs]
    [usage_sub: Bytes.SubFunction partialInvs.usage GetUsage.funs]
    [label_sub: Bytes.SubFunction partialInvs.label GetLabel.funs]
    [invariant_sub: Bytes.SubFunction partialInvs.invariant BytesInvariant.funs]

namespace BytesInvariants

instance [BytesInvariants]: BytesInvariants.Has (BytesInvariants.invs) where

instance
  [BytesInvariants]
  {SubF1 SubF2: Type → Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  [BytesFunctor.Has SubF2]
  (partialInvs1: Bytes.PartialInvariants SubF1)
  (partialInvs2: Bytes.PartialInvariants SubF2)
  [inst1: BytesInvariants.HasStep partialInvs1 partialInvs2]
  [inst2: BytesInvariants.Has partialInvs2]
  : BytesInvariants.Has partialInvs1
  := by
    cases inst1
    cases inst2
    exact {}

end BytesInvariants

def Bytes.PartialInvariants.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  (invs: ∀ id, Bytes.PartialInvariants (SubFs id))
  : Bytes.PartialInvariants (BytesFunctor.combine SubFs)
  where
    well_formed := Bytes.PartialFunction.combine (fun id => (invs id).well_formed)
    usage := Bytes.PartialFunction.combine (fun id => (invs id).usage)
    label := Bytes.PartialFunction.combine (fun id => (invs id).label)
    invariant := Bytes.PartialFunction.combine (fun id => (invs id).invariant)

def Bytes.PartialInvariantsProofs.combine
  [BytesInvariants]
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {invs: ∀ id, Bytes.PartialInvariants (SubFs id)}
  (pfs: ∀ id, Bytes.PartialInvariantsProofs (invs id))
  : Bytes.PartialInvariantsProofs (Bytes.PartialInvariants.combine invs)
  where
    well_formed_later := Bytes.PartialProof1.combine (fun id => (pfs id).well_formed_later)
    usage_later := Bytes.PartialProof2.combine (fun id => (pfs id).usage_later)
    label_later := Bytes.PartialProof2.combine (fun id => (pfs id).label_later)
    invariant_implies_wellformed := Bytes.PartialProof2.combine (fun id => (pfs id).invariant_implies_wellformed)
    invariant_later := Bytes.PartialProof1.combine (fun id => (pfs id).invariant_later)

instance
  [BytesInvariants]
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  (SubFs: t → Type → Type) [∀ id, SubBytesFunctor (SubFs id)]
  (invs: ∀ id, Bytes.PartialInvariants (SubFs id))
  (id: t)
  : BytesInvariants.HasStep (invs id) (Bytes.PartialInvariants.combine invs)
  :=
    let wfs := (fun id => (invs id).well_formed)
    let usages := (fun id => (invs id).usage)
    let labels := (fun id => (invs id).label)
    let invariants := (fun id => (invs id).invariant)
    {
      well_formed_sub := inferInstanceAs (Bytes.SubFunctionStep (wfs id) (Bytes.PartialFunction.combine wfs))
      usage_sub := inferInstanceAs (Bytes.SubFunctionStep (usages id) (Bytes.PartialFunction.combine usages))
      label_sub := inferInstanceAs (Bytes.SubFunctionStep (labels id) (Bytes.PartialFunction.combine labels))
      invariant_sub := inferInstanceAs (Bytes.SubFunctionStep (invariants id) (Bytes.PartialFunction.combine invariants))
    }

instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: HasBytesWellFormed invs.well_formed where
  pf := tc.well_formed_sub
  dummy := ()

instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: HasGetUsage invs.usage where
  pf := tc.usage_sub
  dummy := ()

instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: HasGetLabel invs.label where
  pf := tc.label_sub
  dummy := ()

instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: HasBytesInvariant invs.invariant where
  pf := tc.invariant_sub
  dummy := ()

@[grind]
def Bytes.Publishable [BytesInvariants] (b: Bytes) (tr: ProofTrace) :=
  b.Invariant tr ∧
  (b.label tr).canFlow Label.pub tr

def Bytes.HasUsage [GetUsage] [GetLabel] (b: Bytes) (usg: Usage) (tr: ProofTrace) :=
  b.usage tr = usg ∨
  (b.label tr).canFlow Label.pub tr

theorem Bytes.HasUsage_later
  [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.HasUsage usg tr1 →
    b.HasUsage usg tr2
  := by
    grind [Bytes.HasUsage]

grind_pattern Bytes.HasUsage_later => b.HasUsage usg tr1, tr1 ≤ tr2

theorem Bytes.HasUsage_inj
  [BytesWellFormed] [GetUsage] [GetLabel]
  (b: Bytes) (usg1 usg2: Usage) (tr: ProofTrace)
  :
    b.HasUsage usg1 tr →
    b.HasUsage usg2 tr →
    (usg1 = usg2 ∨ ((b.label tr).canFlow Label.pub tr))
  := by
    grind [Bytes.HasUsage]

theorem Bytes.HasUsage_public
  [BytesWellFormed] [GetUsage] [GetLabel]
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
  :
    (b.label tr).canFlow Label.pub tr →
    b.HasUsage usg tr
  := by
    grind [Bytes.HasUsage]

def Bytes.xxxLabel
  [GetLabel]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (tr: ProofTrace) :=
    match extract b with
    | some sk => sk.label tr
    | none => Label.pub

def Bytes.XXXHasUsage
  [GetUsage] [GetLabel]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (usg: Usage) (tr: ProofTrace) :=
    match extract b with
    | some sk => sk.HasUsage usg tr
    | none => True

def ExtractPreservesWellFormed [BytesWellFormed] (extract: Bytes → Option Bytes): Prop :=
  ∀ b tr, b.WellFormed tr → (
    match extract b with
    | some b' => b'.WellFormed tr
    | none => True
  )

theorem Bytes.xxxLabel_later
  [BytesWellFormed] [GetLabel] [GetLabelLater]
  (extract: Bytes → Option Bytes)
  (h_extract: ExtractPreservesWellFormed extract)
  (b: Bytes) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.xxxLabel extract tr1 = b.xxxLabel extract tr2
  := by
    simp [Bytes.xxxLabel]
    grind [ExtractPreservesWellFormed]

theorem Bytes.XXXHasUsage_later
  [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  (extract: Bytes → Option Bytes)
  (h_extract: ExtractPreservesWellFormed extract)
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.XXXHasUsage extract usg tr1 →
    b.XXXHasUsage extract usg tr2
  := by
    simp [Bytes.XXXHasUsage]
    grind [ExtractPreservesWellFormed]

end DY
