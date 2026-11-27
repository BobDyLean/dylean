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

variable [Bytes.Def]
variable [ExecTrace.Def] [ProofTrace.Def]

-- Well formed

public
abbrev BytesWellFormedT := ProofTrace → Prop

public
class Bytes.WellFormed.Def where
  whole: Bytes.Function BytesWellFormedT

public
def Bytes.WellFormed [Bytes.WellFormed.Def] (b: Bytes) : BytesWellFormedT :=
  Bytes.rec Bytes.WellFormed.Def.whole b

@[has_suffix BytesPart.invariants.well_formed]
public
class Bytes.WellFormed.Has [Bytes.WellFormed.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (binv: outParam (Bytes.Function.Part SubF BytesWellFormedT)) where
  pf: Bytes.Function.Has binv Bytes.WellFormed.Def.whole

@[simp]
public
theorem Bytes.WellFormed.eq
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  [Bytes.WellFormed.Def]
  {binv: Bytes.Function.Part SubF BytesWellFormedT}
  [tc: Bytes.WellFormed.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.WellFormed tr = binv b (fun y _ => Bytes.WellFormed y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.WellFormed.eq => b.pack.WellFormed tr

-- Well formed later

public
class Bytes.WellFormed.later.Proof [Bytes.WellFormed.Def] where
  whole: Bytes.Proof1 Bytes.WellFormed.Def.whole (fun bwf => ∀ tr1 tr2, tr1 ≤ tr2 → bwf tr1 → bwf tr2)

public
theorem Bytes.WellFormed.later
  [Bytes.WellFormed.Def] [Bytes.WellFormed.later.Proof]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.WellFormed b tr1 →
  Bytes.WellFormed b tr2
:= by
  apply Bytes.WellFormed.later.Proof.whole.prove

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
class Bytes.usage.Def where
  whole: Bytes.Function GetUsageT

public
def Bytes.usage [Bytes.usage.Def] (b: Bytes) : GetUsageT :=
  Bytes.rec Bytes.usage.Def.whole b

@[has_suffix BytesPart.invariants.usage]
public
class Bytes.usage.Has [Bytes.usage.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (binv: outParam (Bytes.Function.Part SubF GetUsageT)) where
  pf: Bytes.Function.Has binv Bytes.usage.Def.whole

@[simp]
public
theorem Bytes.usage.eq
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  [Bytes.usage.Def]
  {binv: Bytes.Function.Part SubF GetUsageT}
  [tc: Bytes.usage.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.usage tr = binv b (fun y _ => Bytes.usage y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.usage.eq => (b.pack).usage tr

-- Usage later

public
class Bytes.usage_later.Proof [Bytes.WellFormed.Def] [Bytes.usage.Def] where
  whole: Bytes.Proof2 Bytes.WellFormed.Def.whole Bytes.usage.Def.whole (fun (wf, usg) => ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2)

public
theorem Bytes.usage_later
  [Bytes.WellFormed.Def] [Bytes.usage.Def] [Bytes.usage_later.Proof]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.WellFormed b tr1 →
  Bytes.usage b tr1 = Bytes.usage b tr2
:= by
  apply Bytes.usage_later.Proof.whole.prove

grind_pattern Bytes.usage_later => Bytes.usage b tr1, tr1 ≤ tr2

-- Label

public
abbrev GetLabelT := ProofTrace → Label

public
class Bytes.label.Def where
  whole: Bytes.Function GetLabelT

public
def Bytes.label [Bytes.label.Def] (b: Bytes) : GetLabelT :=
  Bytes.rec Bytes.label.Def.whole b

@[has_suffix BytesPart.invariants.label]
public
class Bytes.label.Has [Bytes.label.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (binv: outParam (Bytes.Function.Part SubF GetLabelT)) where
  pf: Bytes.Function.Has binv Bytes.label.Def.whole

@[simp]
public
theorem Bytes.label.eq
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  [Bytes.label.Def]
  {binv: Bytes.Function.Part SubF GetLabelT}
  [tc: Bytes.label.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.label tr = binv b (fun y _ => Bytes.label y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.label.eq => b.pack.label tr

-- Label later

public
class Bytes.label_later.Proof [Bytes.WellFormed.Def] [Bytes.label.Def] where
  whole: Bytes.Proof2 Bytes.WellFormed.Def.whole Bytes.label.Def.whole (fun (wf, lbl) => ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → lbl tr1 = lbl tr2)

public
theorem Bytes.label_later
  [Bytes.WellFormed.Def] [Bytes.label.Def] [Bytes.label_later.Proof]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.WellFormed b tr1 →
  Bytes.label b tr1 = Bytes.label b tr2
:= by
  apply Bytes.label_later.Proof.whole.prove

grind_pattern Bytes.label_later => Bytes.label b tr1, tr1 ≤ tr2

-- Invariant

public
abbrev BytesInvariantT := ProofTrace → Prop

public
class Bytes.Invariant.Def where
  whole: Bytes.Function BytesInvariantT

public
def Bytes.Invariant [Bytes.Invariant.Def] (b: Bytes) (tr: ProofTrace) : Prop :=
  Bytes.rec Bytes.Invariant.Def.whole b tr

@[has_suffix BytesPart.invariants.invariant]
public
class Bytes.Invariant.Has [Bytes.Invariant.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (binv: outParam (Bytes.Function.Part SubF BytesInvariantT)) where
  pf: Bytes.Function.Has binv Bytes.Invariant.Def.whole

@[simp]
public
theorem Bytes.Invariant.eq
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  [Bytes.Invariant.Def]
  {binv: Bytes.Function.Part SubF BytesInvariantT}
  [tc: Bytes.Invariant.Has binv]
  (b: BytesView SubF)
  (tr: ProofTrace)
  : b.pack.Invariant tr = binv b (fun y _ => Bytes.Invariant y) tr
:= by
  apply congrFun
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.Invariant.eq => Bytes.Invariant (b.pack) tr

-- Invariant implies well formed

public
class Bytes.Invariant_implies_WellFormed.Proof [Bytes.WellFormed.Def] [Bytes.Invariant.Def] where
  whole: Bytes.Proof2 Bytes.Invariant.Def.whole Bytes.WellFormed.Def.whole (fun (binv, bwf) => ∀ tr, binv tr → bwf tr)

public
theorem Bytes.Invariant_implies_WellFormed
  [Bytes.WellFormed.Def] [Bytes.Invariant.Def] [Bytes.Invariant_implies_WellFormed.Proof]
  (b: Bytes)
  (tr: ProofTrace)
  :
  Bytes.Invariant b tr →
  Bytes.WellFormed b tr
:= by
  apply Bytes.Invariant_implies_WellFormed.Proof.whole.prove

grind_pattern Bytes.Invariant_implies_WellFormed => Bytes.WellFormed b tr

-- Invariant later

public
class Bytes.Invariant.later.Proof [Bytes.Invariant.Def] where
  whole: Bytes.Proof1 Bytes.Invariant.Def.whole (fun binv => ∀ tr1 tr2, tr1 ≤ tr2 → binv tr1 → binv tr2)

public
theorem Bytes.Invariant.later
  [Bytes.Invariant.Def] [Bytes.Invariant.later.Proof]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.Invariant b tr1 →
  Bytes.Invariant b tr2
:= by
  apply Bytes.Invariant.later.Proof.whole.prove

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
structure Bytes.Invariants.Part (SubF: Type → Type) [Bytes.Part SubF] where
  well_formed: Bytes.Function.Part SubF BytesWellFormedT
  usage: Bytes.Function.Part SubF GetUsageT
  label: [Bytes.usage.Def] → Bytes.Function.Part SubF GetLabelT
  invariant: [Bytes.WellFormed.Def] → [Bytes.usage.Def] → [Bytes.label.Def] → Bytes.Function.Part SubF BytesInvariantT

public
class Bytes.Invariants.Def where
  whole: Bytes.Invariants.Part Bytes.Functor

public
instance [Bytes.Invariants.Def]: Bytes.WellFormed.Def where
  whole := Bytes.Invariants.Def.whole.well_formed

public
instance [Bytes.Invariants.Def]: Bytes.usage.Def where
  whole := Bytes.Invariants.Def.whole.usage

public
instance [Bytes.Invariants.Def]: Bytes.label.Def where
  whole := Bytes.Invariants.Def.whole.label

public
instance [Bytes.Invariants.Def]: Bytes.Invariant.Def where
  whole := Bytes.Invariants.Def.whole.invariant

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
structure Bytes.Invariants.Part.Lawful [Bytes.Invariants.Def] {SubF: Type → Type} [Bytes.Part SubF] (invs: Bytes.Invariants.Part SubF) where
  well_formed_later: Bytes.Proof1.Part invs.well_formed Bytes.WellFormed
    (fun bwf => ∀ tr1 tr2, tr1 ≤ tr2 → bwf tr1 → bwf tr2) := by
    intro x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind

  usage_later: Bytes.Proof2.Part invs.well_formed invs.usage Bytes.WellFormed Bytes.usage
    (fun (wf, usg) => ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2) := by
    intro x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind

  label_later: [Bytes.usage_later.Proof] → Bytes.Proof2.Part invs.well_formed invs.label Bytes.WellFormed Bytes.label
    (fun (wf, lbl) => ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → lbl tr1 = lbl tr2) := by
    intro _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind

  invariant_implies_wellformed: Bytes.Proof2.Part invs.invariant invs.well_formed Bytes.Invariant Bytes.WellFormed
    (fun (binv, bwf) => ∀ tr, binv tr → bwf tr) := by
    intro x rec tr
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind

  invariant_later: [Bytes.WellFormed.later.Proof] → [Bytes.usage_later.Proof] → [Bytes.label_later.Proof] → [Bytes.Invariant_implies_WellFormed.Proof] → Bytes.Proof1.Part invs.invariant Bytes.Invariant
    (fun binv => ∀ tr1 tr2, tr1 ≤ tr2 → binv tr1 → binv tr2) := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind

public
class Bytes.Invariants.Lawful [Bytes.Invariants.Def] where
  whole: Bytes.Invariants.Part.Lawful (Bytes.Invariants.Def.whole)

public
instance [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]: Bytes.WellFormed.later.Proof where
  whole := Bytes.Invariants.Lawful.whole.well_formed_later

public
instance [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]: Bytes.usage_later.Proof where
  whole := Bytes.Invariants.Lawful.whole.usage_later

public
instance [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]: Bytes.label_later.Proof where
  whole := Bytes.Invariants.Lawful.whole.label_later

public
instance [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]: Bytes.Invariant_implies_WellFormed.Proof where
  whole := Bytes.Invariants.Lawful.whole.invariant_implies_wellformed

public
instance [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]: Bytes.Invariant.later.Proof where
  whole := Bytes.Invariants.Lawful.whole.invariant_later

public
class Bytes.Invariants.HasStep
  [Bytes.Invariants.Def]
  {SubF1 SubF2: Type → Type}
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  (partialInvs1: outParam (Bytes.Invariants.Part SubF1))
  (partialInvs2: Bytes.Invariants.Part SubF2)
where
  [well_formed_sub: Bytes.Function.HasStep partialInvs1.well_formed partialInvs2.well_formed]
  [usage_sub: Bytes.Function.HasStep partialInvs1.usage partialInvs2.usage]
  [label_sub: Bytes.Function.HasStep partialInvs1.label partialInvs2.label]
  [invariant_sub: Bytes.Function.HasStep partialInvs1.invariant partialInvs2.invariant]

@[has_suffix BytesPart.invariants]
public
class Bytes.Invariants.Has
  [Bytes.Invariants.Def]
  {SubF: Type → Type}
  [Bytes.Part SubF]
  [Bytes.Has SubF]
  (partialInvs: outParam (Bytes.Invariants.Part SubF))
where
  [well_formed_sub: Bytes.Function.Has partialInvs.well_formed Bytes.WellFormed.Def.whole]
  [usage_sub: Bytes.Function.Has partialInvs.usage Bytes.usage.Def.whole]
  [label_sub: Bytes.Function.Has partialInvs.label Bytes.label.Def.whole]
  [invariant_sub: Bytes.Function.Has partialInvs.invariant Bytes.Invariant.Def.whole]

public
def Bytes.Invariants.combine
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  (invs: ∀ id, Bytes.Invariants.Part (SubFs id))
  : Bytes.Invariants.Part (Bytes.combine SubFs)
where
  well_formed := Bytes.Function.combine (fun id => (invs id).well_formed)
  usage := Bytes.Function.combine (fun id => (invs id).usage)
  label := Bytes.Function.combine (fun id => (invs id).label)
  invariant := Bytes.Function.combine (fun id => (invs id).invariant)

public
theorem Bytes.Invariants.Part.Lawful.combine
  [Bytes.Invariants.Def]
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  {invs: ∀ id, Bytes.Invariants.Part (SubFs id)}
  (pfs: ∀ id, Bytes.Invariants.Part.Lawful (invs id))
  : Bytes.Invariants.Part.Lawful (Bytes.Invariants.combine invs)
where
  well_formed_later := Bytes.Proof1.combine (fun id => (pfs id).well_formed_later)
  usage_later := Bytes.Proof2.combine (fun id => (pfs id).usage_later)
  label_later := Bytes.Proof2.combine (fun id => (pfs id).label_later)
  invariant_implies_wellformed := Bytes.Proof2.combine (fun id => (pfs id).invariant_implies_wellformed)
  invariant_later := Bytes.Proof1.combine (fun id => (pfs id).invariant_later)

namespace Bytes.Invariants.Def

public instance [Bytes.Invariants.Def]: Bytes.Invariants.Has (Bytes.Invariants.Def.whole) where

public instance
  [Bytes.Invariants.Def]
  {SubF1 SubF2: Type → Type}
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  [Bytes.Has SubF2]
  (partialInvs1: Bytes.Invariants.Part SubF1)
  (partialInvs2: Bytes.Invariants.Part SubF2)
  [inst1: Bytes.Invariants.HasStep partialInvs1 partialInvs2]
  [inst2: Bytes.Invariants.Has partialInvs2]
  : Bytes.Invariants.Has partialInvs1
:= by
  cases inst1
  cases inst2
  exact {}

public instance
  [Bytes.Invariants.Def]
  {n: Nat}
  (SubFs: Fin n → Type → Type) [∀ id, Bytes.Part (SubFs id)]
  (invs: ∀ id, Bytes.Invariants.Part (SubFs id))
  (id: Fin n)
  : Bytes.Invariants.HasStep (invs id) (Bytes.Invariants.combine invs)
:=
  let wfs := (fun id => (invs id).well_formed)
  let usages := (fun id => (invs id).usage)
  let labels := (fun id => (invs id).label)
  let invariants := (fun id => (invs id).invariant)
  {
    well_formed_sub := inferInstanceAs (Bytes.Function.HasStep (wfs id) (Bytes.Function.combine wfs))
    usage_sub := inferInstanceAs (Bytes.Function.HasStep (usages id) (Bytes.Function.combine usages))
    label_sub := inferInstanceAs (Bytes.Function.HasStep (labels id) (Bytes.Function.combine labels))
    invariant_sub := inferInstanceAs (Bytes.Function.HasStep (invariants id) (Bytes.Function.combine invariants))
  }

public
instance [Bytes.Invariants.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (invs: Bytes.Invariants.Part SubF) [tc: Bytes.Invariants.Has invs]: Bytes.WellFormed.Has invs.well_formed where
  pf := tc.well_formed_sub

public
instance [Bytes.Invariants.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (invs: Bytes.Invariants.Part SubF) [tc: Bytes.Invariants.Has invs]: Bytes.usage.Has invs.usage where
  pf := tc.usage_sub

public
instance [Bytes.Invariants.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (invs: Bytes.Invariants.Part SubF) [tc: Bytes.Invariants.Has invs]: Bytes.label.Has invs.label where
  pf := tc.label_sub

public
instance [Bytes.Invariants.Def] {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF] (invs: Bytes.Invariants.Part SubF) [tc: Bytes.Invariants.Has invs]: Bytes.Invariant.Has invs.invariant where
  pf := tc.invariant_sub

end Bytes.Invariants.Def

@[expose, grind]
public
def Bytes.Publishable [Bytes.Invariants.Def] (b: Bytes) (tr: ProofTrace) :=
  b.Invariant tr ∧
  (b.label tr).canFlow Label.pub tr.erase

@[expose, grind]
public
def Bytes.KnowableBy [Bytes.Invariants.Def] (l: Label) (b: Bytes) (tr: ProofTrace) :=
  b.Invariant tr ∧
  (b.label tr).canFlow l tr.erase

@[expose]
public
def Bytes.HasUsage [Bytes.usage.Def] [Bytes.label.Def] (b: Bytes) (usg: Usage) (tr: ProofTrace) :=
  b.usage tr = usg ∨
  (b.label tr).canFlow Label.pub tr.erase

public
theorem Bytes.HasUsage_later
  [Bytes.WellFormed.Def] [Bytes.usage.Def] [Bytes.usage_later.Proof] [Bytes.label.Def] [Bytes.label_later.Proof]
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
  [Bytes.WellFormed.Def] [Bytes.usage.Def] [Bytes.label.Def]
  (b: Bytes) (usg1 usg2: Usage) (tr: ProofTrace)
  : b.HasUsage usg1 tr →
    b.HasUsage usg2 tr →
    (usg1 = usg2 ∨ ((b.label tr).canFlow Label.pub tr.erase))
:= by
  grind [Bytes.HasUsage]

public
theorem Bytes.HasUsage_public
  [Bytes.WellFormed.Def] [Bytes.usage.Def] [Bytes.label.Def]
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
  : (b.label tr).canFlow Label.pub tr.erase →
    b.HasUsage usg tr
:= by
  grind [Bytes.HasUsage]

@[expose]
public
def Bytes.xxxLabel
  [Bytes.label.Def]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (tr: ProofTrace)
:=
  match extract b with
  | some sk => sk.label tr
  | none => Label.pub

@[expose]
public
def Bytes.XXXHasUsage
  [Bytes.usage.Def] [Bytes.label.Def]
  (extract: Bytes → Option Bytes)
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
:=
  match extract b with
  | some sk => sk.HasUsage usg tr
  | none => True

@[expose]
public
def ExtractPreservesWellFormed [Bytes.WellFormed.Def] (extract: Bytes → Option Bytes): Prop :=
  ∀ b tr, b.WellFormed tr → (
    match extract b with
    | some b' => b'.WellFormed tr
    | none => True
  )

public
theorem Bytes.xxxLabel_later
  [Bytes.WellFormed.Def] [Bytes.label.Def] [Bytes.label_later.Proof]
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
  [Bytes.WellFormed.Def] [Bytes.usage.Def] [Bytes.usage_later.Proof] [Bytes.label.Def] [Bytes.label_later.Proof]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
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
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  (b: Bytes)
  (tr: ProofTrace)
  :
  Bytes.Publishable b tr →
  Bytes.Invariant b tr
:= by grind

grind_pattern [grind_later] Bytes.Publishable_imp_Invariant_fast => Bytes.Publishable b tr

public
theorem Bytes.HasUsage_later_fast
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
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
  | `(command| #combine_one $options* Bytes.Invariants $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.Bytes.Def])), (← `(bracketedBinder| [DY.ExecTrace.Def])), (← `(bracketedBinder| [DY.ProofTrace.Def]))]
    let hasStepBaseParams := #[(← `(bracketedBinder| [DY.Bytes.Invariants.Def]))]
    let hasStepParams := if options.toplevel then params else baseParams ++ hasStepBaseParams ++ params
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `BytesPart.invariants
      refereeName := `BytesPart.Functor
      combineName := ``DY.Bytes.Invariants.combine
      outTypeName := ``DY.Bytes.Invariants.Part
      isTheorem := false
    }

    let hasStep ← mkHasStep hasStepParams sources <| .makeSimple {
      name := `BytesPart.invariants
      combineName := ``DY.Bytes.Invariants.combine
      hasStepName := ``DY.Bytes.Invariants.HasStep
    }

    let invariantsStx := Lean.mkIdent `BytesPart.invariants
    let topLevelInst ← `(command| public instance: DY.Bytes.Invariants.Def where whole := $invariantsStx)
    let topLevelHas ← `(command| public instance: DY.Bytes.Invariants.Has $invariantsStx := inferInstanceAs (DY.Bytes.Invariants.Has DY.Bytes.Invariants.Def.whole))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ topLevel ++ hasStep)

macro_rules
  | `(command| #combine_one $options* Bytes.Invariants.Lawful $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.Bytes.Def])), (← `(bracketedBinder| [DY.ExecTrace.Def])), (← `(bracketedBinder| [DY.ProofTrace.Def])), (← `(bracketedBinder| [DY.Bytes.Invariants.Def]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources <| .makeSimple {
      name := `BytesPart.invariantsLawful
      refereeName := `BytesPart.invariants
      combineName := ``DY.Bytes.Invariants.Part.Lawful.combine
      outTypeName := ``DY.Bytes.Invariants.Part.Lawful
      isTheorem := true
    }

    let invariantsLawfulStx := Lean.mkIdent `BytesPart.invariantsLawful
    let topLevelInst ← `(command| public instance: DY.Bytes.Invariants.Lawful where whole := $invariantsLawfulStx)
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)


end Meta.CombineMacro

end DY
