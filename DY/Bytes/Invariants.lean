/-
  This module allows to define invariants on `Bytes`.
  TODO: explain what is happening once things are stabilized
-/

module

public import DY.Bytes.Basic
public import DY.Trace.Basic
public import DY.Trace.Invariant
public import DY.Label
public meta import DY.Trace.Grind
public meta import DY.Meta.CombineMacro

namespace DY

variable [BytesFunctor]
variable [ExecTraceTypes] [ProofTraceTypes]

-- Well formed

public
abbrev BytesWellFormedT := ProofTrace → Prop

public
class BytesWellFormed where
  funs: Bytes.Function BytesWellFormedT

public
def Bytes.WellFormed [BytesWellFormed] (b: Bytes) : BytesWellFormedT :=
  Bytes.rec BytesWellFormed.funs b

public
class BytesWellFormed.Has [BytesWellFormed] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF BytesWellFormedT)) where
  pf: Bytes.SubFunction binv BytesWellFormed.funs

@[simp]
public
theorem Bytes.WellFormed.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [BytesWellFormed]
  {binv: Bytes.PartialFunction SubF BytesWellFormedT}
  [tc: BytesWellFormed.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.WellFormed tr = binv b (fun y _ => Bytes.WellFormed y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.WellFormed.eq => b.pack.WellFormed tr

-- Well formed later

@[expose]
public
def BytesWellFormedLaterT (bwf: BytesWellFormedT) :=
  ∀ tr1 tr2, tr1 ≤ tr2 → bwf tr1 → bwf tr2

public
class BytesWellFormedLater [BytesWellFormed] where
  proofs: Bytes.Proof1 BytesWellFormed.funs BytesWellFormedLaterT

public
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

public
structure Usage where
  type: String
  tag: String
  data: Option Bytes

@[expose]
public
def Usage.nothing: Usage where
  type := ""
  tag := ""
  data := none

public
abbrev GetUsageT := ProofTrace → Usage

public
class GetUsage where
  funs: Bytes.Function GetUsageT

public
def Bytes.usage [GetUsage] (b: Bytes) : GetUsageT :=
  Bytes.rec GetUsage.funs b

public
class GetUsage.Has [GetUsage] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF GetUsageT)) where
  pf: Bytes.SubFunction binv GetUsage.funs

@[simp]
public
theorem Bytes.usage.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [GetUsage]
  {binv: Bytes.PartialFunction SubF GetUsageT}
  [tc: GetUsage.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.usage tr = binv b (fun y _ => Bytes.usage y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.usage.eq => (b.pack).usage tr

-- Usage later

@[expose]
public
def GetUsageLaterT (x: BytesWellFormedT × GetUsageT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

public
class GetUsageLater [BytesWellFormed] [GetUsage] where
  proofs: Bytes.Proof2 BytesWellFormed.funs GetUsage.funs GetUsageLaterT

public
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

public
abbrev GetLabelT := ProofTrace → Label

public
class GetLabel where
  funs: Bytes.Function GetLabelT

public
def Bytes.label [GetLabel] (b: Bytes) : GetLabelT :=
  Bytes.rec GetLabel.funs b

public
class GetLabel.Has [GetLabel] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF GetLabelT)) where
  pf: Bytes.SubFunction binv GetLabel.funs

@[simp]
public
theorem Bytes.label.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [GetLabel]
  {binv: Bytes.PartialFunction SubF GetLabelT}
  [tc: GetLabel.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.label tr = binv b (fun y _ => Bytes.label y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.label.eq => b.pack.label tr

-- Label later

@[expose]
public
def GetLabelLaterT (x: BytesWellFormedT × GetLabelT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

public
class GetLabelLater [BytesWellFormed] [GetLabel] where
  proofs: Bytes.Proof2 BytesWellFormed.funs GetLabel.funs GetLabelLaterT

public
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

public
abbrev BytesInvariantT := ProofTrace → Prop

public
class BytesInvariant where
  funs: Bytes.Function BytesInvariantT

public
def Bytes.Invariant [BytesInvariant] (b: Bytes) (tr: ProofTrace) : Prop :=
  Bytes.rec BytesInvariant.funs b tr

public
class BytesInvariant.Has [BytesInvariant] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (binv: outParam (Bytes.PartialFunction SubF BytesInvariantT)) where
  pf: Bytes.SubFunction binv BytesInvariant.funs

@[simp]
public
theorem Bytes.Invariant.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [BytesInvariant]
  {binv: Bytes.PartialFunction SubF BytesInvariantT}
  [tc: BytesInvariant.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.Invariant tr = binv b (fun y _ => Bytes.Invariant y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.Invariant.eq => Bytes.Invariant (b.pack) tr

-- Invariant implies well formed

@[expose]
public
def BytesInvariantImpliesBytesWellFormedT (x: BytesInvariantT × BytesWellFormedT) :=
  let (binv, bwf) := x
  ∀ tr, binv tr → bwf tr

public
class BytesInvariantImpliesBytesWellFormed [BytesWellFormed] [BytesInvariant] where
  proofs: Bytes.Proof2 BytesInvariant.funs BytesWellFormed.funs BytesInvariantImpliesBytesWellFormedT

public
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

@[expose]
public
def BytesInvariantLaterT (binv: BytesInvariantT) :=
  ∀ tr1 tr2, tr1 ≤ tr2 → binv tr1 → binv tr2

public
class BytesInvariantLater [BytesInvariant] where
  proofs: Bytes.Proof1 BytesInvariant.funs BytesInvariantLaterT

public
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
public
structure Bytes.PartialInvariants (SubF: Type → Type) [SubBytesFunctor SubF] where
  well_formed: Bytes.PartialFunction SubF BytesWellFormedT
  usage: Bytes.PartialFunction SubF GetUsageT
  label: [GetUsage] → Bytes.PartialFunction SubF GetLabelT
  invariant: [BytesWellFormed] → [GetUsage] → [GetLabel] → Bytes.PartialFunction SubF BytesInvariantT

public
class BytesInvariants where
  invs: Bytes.PartialInvariants BytesF

public
instance [BytesInvariants]: BytesWellFormed where
  funs := BytesInvariants.invs.well_formed

public
instance [BytesInvariants]: GetUsage where
  funs := BytesInvariants.invs.usage

public
instance [BytesInvariants]: GetLabel where
  funs := BytesInvariants.invs.label

public
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
public
structure Bytes.PartialInvariantsProofs [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] (invs: Bytes.PartialInvariants SubF) where
  well_formed_later: Bytes.PartialProof1 invs.well_formed Bytes.WellFormed BytesWellFormedLaterT := by
    intro x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesWellFormedLaterT] <;> grind

  usage_later: Bytes.PartialProof2 invs.well_formed invs.usage Bytes.WellFormed Bytes.usage GetUsageLaterT := by
    intro x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetUsageLaterT] <;> grind

  label_later: [GetUsageLater] → Bytes.PartialProof2 invs.well_formed invs.label Bytes.WellFormed Bytes.label GetLabelLaterT := by
    intro _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetLabelLaterT] <;> grind

  invariant_implies_wellformed: Bytes.PartialProof2 invs.invariant invs.well_formed Bytes.Invariant Bytes.WellFormed BytesInvariantImpliesBytesWellFormedT := by
    intro x rec tr
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantImpliesBytesWellFormedT] <;> grind

  invariant_later: [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] → [BytesInvariantImpliesBytesWellFormed] → Bytes.PartialProof1 invs.invariant Bytes.Invariant BytesInvariantLaterT := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT] <;> grind

public
class BytesInvariantsProofs [BytesInvariants] where
  pfs: Bytes.PartialInvariantsProofs (BytesInvariants.invs)

public
instance [BytesInvariants] [BytesInvariantsProofs]: BytesWellFormedLater where
  proofs := BytesInvariantsProofs.pfs.well_formed_later

public
instance [BytesInvariants] [BytesInvariantsProofs]: GetUsageLater where
  proofs := BytesInvariantsProofs.pfs.usage_later

public
instance [BytesInvariants] [BytesInvariantsProofs]: GetLabelLater where
  proofs := BytesInvariantsProofs.pfs.label_later

public
instance [BytesInvariants] [BytesInvariantsProofs]: BytesInvariantImpliesBytesWellFormed where
  proofs := BytesInvariantsProofs.pfs.invariant_implies_wellformed

public
instance [BytesInvariants] [BytesInvariantsProofs]: BytesInvariantLater where
  proofs := BytesInvariantsProofs.pfs.invariant_later

public
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

public
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

public
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

public
theorem Bytes.PartialInvariantsProofs.combine
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

namespace BytesInvariants

public instance [BytesInvariants]: BytesInvariants.Has (BytesInvariants.invs) where

public instance
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

public instance
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

public
instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: BytesWellFormed.Has invs.well_formed where
  pf := tc.well_formed_sub

public
instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: GetUsage.Has invs.usage where
  pf := tc.usage_sub

public
instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: GetLabel.Has invs.label where
  pf := tc.label_sub

public
instance [BytesInvariants] {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (invs: Bytes.PartialInvariants SubF) [tc: BytesInvariants.Has invs]: BytesInvariant.Has invs.invariant where
  pf := tc.invariant_sub

end BytesInvariants

@[expose, grind]
public
def Bytes.Publishable [BytesInvariants] (b: Bytes) (tr: ProofTrace) :=
  b.Invariant tr ∧
  (b.label tr).canFlow Label.pub tr.erase

@[expose, grind]
public
def Bytes.KnowableBy [BytesInvariants] (l: Label) (b: Bytes) (tr: ProofTrace) :=
  b.Invariant tr ∧
  (b.label tr).canFlow l tr.erase

@[expose]
public
def Bytes.HasUsage [GetUsage] [GetLabel] (b: Bytes) (usg: Usage) (tr: ProofTrace) :=
  b.usage tr = usg ∨
  (b.label tr).canFlow Label.pub tr.erase

public
theorem Bytes.HasUsage_later
  [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.HasUsage usg tr1 →
    b.HasUsage usg tr2
:= by
  grind [Bytes.HasUsage]

grind_pattern Bytes.HasUsage_later => b.HasUsage usg tr1, tr1 ≤ tr2

public
theorem Bytes.HasUsage_inj
  [BytesWellFormed] [GetUsage] [GetLabel]
  (b: Bytes) (usg1 usg2: Usage) (tr: ProofTrace)
  : b.HasUsage usg1 tr →
    b.HasUsage usg2 tr →
    (usg1 = usg2 ∨ ((b.label tr).canFlow Label.pub tr.erase))
:= by
  grind [Bytes.HasUsage]

public
theorem Bytes.HasUsage_public
  [BytesWellFormed] [GetUsage] [GetLabel]
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
  : (b.label tr).canFlow Label.pub tr.erase →
    b.HasUsage usg tr
:= by
  grind [Bytes.HasUsage]

@[expose]
public
def Bytes.xxxLabel
  [GetLabel]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (tr: ProofTrace)
:=
  match extract b with
  | some sk => sk.label tr
  | none => Label.pub

@[expose]
public
def Bytes.XXXHasUsage
  [GetUsage] [GetLabel]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
:=
  match extract b with
  | some sk => sk.HasUsage usg tr
  | none => True

@[expose]
public
def ExtractPreservesWellFormed [BytesWellFormed] (extract: Bytes → Option Bytes): Prop :=
  ∀ b tr, b.WellFormed tr → (
    match extract b with
    | some b' => b'.WellFormed tr
    | none => True
  )

public
theorem Bytes.xxxLabel_later
  [BytesWellFormed] [GetLabel] [GetLabelLater]
  (extract: Bytes → Option Bytes)
  (h_extract: ExtractPreservesWellFormed extract)
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.xxxLabel extract tr1 = b.xxxLabel extract tr2
:= by
  simp [Bytes.xxxLabel]
  grind [ExtractPreservesWellFormed]

public
theorem Bytes.XXXHasUsage_later
  [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  (extract: Bytes → Option Bytes)
  (h_extract: ExtractPreservesWellFormed extract)
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.XXXHasUsage extract usg tr1 →
    b.XXXHasUsage extract usg tr2
:= by
  simp [Bytes.XXXHasUsage]
  grind [ExtractPreservesWellFormed]

/-
  Fast grind pattern for later lemmas,
  using Invariant instead of WellFormed
-/

public
theorem Bytes.usage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.Invariant b tr1 →
  Bytes.usage b tr1 = Bytes.usage b tr2
:= by grind

grind_pattern [grind_later] Bytes.usage_later_fast => Bytes.usage b tr1, tr1 ≤ tr2

public
theorem Bytes.label_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.Invariant b tr1 →
  Bytes.label b tr1 = Bytes.label b tr2
:= by grind

grind_pattern [grind_later] Bytes.label_later_fast => Bytes.label b tr1, tr1 ≤ tr2

public
theorem Bytes.Invariant.later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.Invariant b tr1 →
  Bytes.Invariant b tr2
:= by grind

grind_pattern [grind_later] Bytes.Invariant.later_fast => Bytes.Invariant b tr1, tr1 ≤ tr2

public
theorem Bytes.Publishable_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.Publishable b tr1 →
  Bytes.Publishable b tr2
:= by grind

grind_pattern [grind_later] Bytes.Publishable_later_fast => Bytes.Publishable b tr1, tr1 ≤ tr2

-- Or do we want to add grind_later attribute to Publishable?
public
theorem Bytes.Publishable_imp_Invariant_fast
  [BytesInvariants] [BytesInvariantsProofs]
  (b: Bytes)
  (tr: ProofTrace)
  :
  Bytes.Publishable b tr →
  Bytes.Invariant b tr
:= by grind

grind_pattern [grind_later] Bytes.Publishable_imp_Invariant_fast => Bytes.Publishable b tr

public
theorem Bytes.HasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.HasUsage usg tr1 →
    b.HasUsage usg tr2
:= by
  grind [Bytes.HasUsage]

grind_pattern [grind_later] Bytes.HasUsage_later_fast => b.HasUsage usg tr1, tr1 ≤ tr2

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* BytesInvariants $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes]))]
    let hasStepBaseParams := #[(← `(bracketedBinder| [DY.BytesInvariants]))]
    let hasStepParams := if options.toplevel then params else baseParams ++ hasStepBaseParams ++ params
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `invariants
      refereeName := `SubF
      combineName := ``DY.Bytes.PartialInvariants.combine
      outTypeName := ``DY.Bytes.PartialInvariants
      isTheorem := false
    }

    let hasStep ← mkHasStep hasStepParams sources <| .makeSimple {
      name := `invariants
      combineName := ``DY.Bytes.PartialInvariants.combine
      hasStepName := ``DY.BytesInvariants.HasStep
    }

    let invariantsStx := Lean.mkIdent `invariants
    let topLevelInst ← `(command| public instance: DY.BytesInvariants where invs := $invariantsStx)
    let topLevelHas ← `(command| public instance: DY.BytesInvariants.Has $invariantsStx := inferInstanceAs (DY.BytesInvariants.Has DY.BytesInvariants.invs))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ topLevel ++ hasStep)

macro_rules
  | `(command| #combine_one $options* BytesInvariantsProofs $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes])), (← `(bracketedBinder| [DY.BytesInvariants]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `invariantsProofs
      refereeName := `invariants
      combineName := ``DY.Bytes.PartialInvariantsProofs.combine
      outTypeName := ``DY.Bytes.PartialInvariantsProofs
      isTheorem := true
    }

    let invariantsProofsStx := Lean.mkIdent `invariantsProofs
    let topLevelInst ← `(command| public instance: DY.BytesInvariantsProofs where pfs := $invariantsProofsStx)
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)


end Meta.CombineMacro

end DY
