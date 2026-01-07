import DY.Bytes.Type
import DY.Label
import DY.Trace

namespace DY

variable {CtorId: Type}
variable [BytesCtors CtorId]

-- Well formed

def BytesWellFormedT := ProofTrace → Prop
def BytesWellFormedT.default: BytesWellFormedT := fun _ => False

class BytesWellFormed where
  funs: BytesFunCtors BytesWellFormedT

def Bytes.WellFormed [BytesWellFormed] (b: Bytes) : BytesWellFormedT :=
  Bytes.mkRec BytesWellFormed.funs .default b

class HasBytesWellFormed [BytesWellFormed] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (binv: outParam (BytesFunCtor id BytesWellFormedT)) where
  pf: BytesWellFormed.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.WellFormed.eq
  [tc_binv: BytesWellFormed]
  (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id]
  {binv: BytesFunCtor id BytesWellFormedT}
  [tc: HasBytesWellFormed id binv]
  (b: BytesView id)
  (tr: ProofTrace)
  : Bytes.WellFormed (b.pack) tr = binv.func b.data b.dataBytes Bytes.WellFormed tr
  := by
    have lem {a b} (f g: a → b) (x: a): f = g → f x = g x := by grind
    apply lem
    apply Bytes.mkRec.eqView
    exact tc.pf

grind_pattern Bytes.WellFormed.eq => Bytes.WellFormed (b.pack) tr

-- Well formed later

def BytesWellFormedLaterT (bwf: BytesWellFormedT) :=
  ∀ tr1 tr2, tr1 ≤ tr2 → bwf tr1 → bwf tr2

class BytesWellFormedLater [BytesWellFormed] where
  proofs: BytesFunCtorsProof1 BytesWellFormed.funs BytesWellFormedT.default BytesWellFormedLaterT

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
def GetUsageT.default: GetUsageT := fun _ => Usage.nothing

class GetUsage where
  funs: BytesFunCtors GetUsageT

noncomputable
def Bytes.usage [GetUsage] (b: Bytes) : GetUsageT :=
  Bytes.mkRec GetUsage.funs .default b

class HasGetUsage [GetUsage] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (binv: outParam (BytesFunCtor id GetUsageT)) where
  pf: GetUsage.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.usage.eq
  [tc_binv: GetUsage]
  (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id]
  {binv: BytesFunCtor id GetUsageT}
  [tc: HasGetUsage id binv]
  (b: BytesView id)
  (tr: ProofTrace)
  : Bytes.usage (b.pack) tr = binv.func b.data b.dataBytes Bytes.usage tr
  := by
    have lem {a b} (f g: a → b) (x: a): f = g → f x = g x := by grind
    apply lem
    apply Bytes.mkRec.eqView
    exact tc.pf

grind_pattern Bytes.usage.eq => Bytes.usage (b.pack) tr

-- Usage later

def GetUsageLaterT (x: BytesWellFormedT × GetUsageT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

class GetUsageLater [BytesWellFormed] [GetUsage] where
  proofs: BytesFunCtorsProof2 BytesWellFormed.funs GetUsage.funs BytesWellFormedT.default GetUsageT.default GetUsageLaterT

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
def GetLabelT.default: GetLabelT := fun _ => Label.secret

class GetLabel where
  funs: BytesFunCtors GetLabelT

noncomputable
def Bytes.label [GetLabel] (b: Bytes) : GetLabelT :=
  Bytes.mkRec GetLabel.funs .default b

class HasGetLabel [GetLabel] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (binv: outParam (BytesFunCtor id GetLabelT)) where
  pf: GetLabel.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.label.eq
  [tc_binv: GetLabel]
  (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id]
  {binv: BytesFunCtor id GetLabelT}
  [tc: HasGetLabel id binv]
  (b: BytesView id)
  (tr: ProofTrace)
  : Bytes.label (b.pack) tr = binv.func b.data b.dataBytes Bytes.label tr
  := by
    have lem {a b} (f g: a → b) (x: a): f = g → f x = g x := by grind
    apply lem
    apply Bytes.mkRec.eqView
    exact tc.pf

grind_pattern Bytes.label.eq => Bytes.label (b.pack) tr

-- Label later

def GetLabelLaterT (x: BytesWellFormedT × GetLabelT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

class GetLabelLater [BytesWellFormed] [GetLabel] where
  proofs: BytesFunCtorsProof2 BytesWellFormed.funs GetLabel.funs BytesWellFormedT.default GetLabelT.default GetLabelLaterT

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

def BytesInvariantT.default: BytesInvariantT := fun _ => False

class BytesInvariant where
  funs: BytesFunCtors BytesInvariantT

def Bytes.Invariant [BytesInvariant] (b: Bytes) (tr: ProofTrace) : Prop :=
  Bytes.mkRec BytesInvariant.funs .default b tr

class HasBytesInvariant [BytesInvariant] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (binv: outParam (BytesFunCtor id BytesInvariantT)) where
  pf: BytesInvariant.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.Invariant.eq
  [tc_binv: BytesInvariant]
  (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id]
  {binv: BytesFunCtor id BytesInvariantT}
  [tc: HasBytesInvariant id binv]
  (b: BytesView id)
  (tr: ProofTrace)
  : Bytes.Invariant (b.pack) tr = binv.func b.data b.dataBytes Bytes.Invariant tr
  := by
    have lem {a b} (f g: a → b) (x: a): f = g → f x = g x := by grind
    apply lem
    apply Bytes.mkRec.eqView
    exact tc.pf

grind_pattern Bytes.Invariant.eq => Bytes.Invariant (b.pack) tr

-- Invariant implies well formed

def BytesInvariantImpliesBytesWellFormedT (x: BytesInvariantT × BytesWellFormedT) :=
  let (binv, bwf) := x
  ∀ tr, binv tr → bwf tr

class BytesInvariantImpliesBytesWellFormed [BytesWellFormed] [BytesInvariant] where
  proofs: BytesFunCtorsProof2 BytesInvariant.funs BytesWellFormed.funs BytesInvariantT.default BytesWellFormedT.default BytesInvariantImpliesBytesWellFormedT

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
  proofs: BytesFunCtorsProof1 BytesInvariant.funs BytesInvariantT.default BytesInvariantLaterT

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

structure BytesCtorInvariants.Internal (ctor: BytesCtor) where
  well_formed: BytesFunCtor.Internal ctor BytesWellFormedT
  well_formed_later: [BytesWellFormed] → BytesFunCtorProof1.Internal Bytes.WellFormed well_formed BytesWellFormedLaterT

  usage: BytesFunCtor.Internal ctor GetUsageT
  usage_later: [BytesWellFormed] → [GetUsage] → BytesFunCtorProof2.Internal Bytes.WellFormed Bytes.usage well_formed usage GetUsageLaterT

  label: [GetUsage] → BytesFunCtor.Internal ctor GetLabelT
  label_later: [BytesWellFormed] → [GetUsage] → [GetUsageLater] → [GetLabel] → BytesFunCtorProof2.Internal Bytes.WellFormed Bytes.label well_formed label GetLabelLaterT

  invariant: [BytesWellFormed] → [GetUsage] → [GetLabel] → BytesFunCtor.Internal ctor BytesInvariantT
  invariant_implies_wellformed: [BytesWellFormed] → [GetUsage] → [GetLabel] → [BytesInvariant] → BytesFunCtorProof2.Internal Bytes.Invariant Bytes.WellFormed invariant well_formed BytesInvariantImpliesBytesWellFormedT
  invariant_later: [BytesWellFormed] → [BytesWellFormedLater] → [GetUsage] → [GetUsageLater] → [GetLabel] → [GetLabelLater] → [BytesInvariant] → [BytesInvariantImpliesBytesWellFormed] → BytesFunCtorProof1.Internal Bytes.Invariant invariant BytesInvariantLaterT
  -- ...

def BytesCtorInvariants.ById (id: CtorId) := BytesCtorInvariants.Internal (BytesCtors.ctors id)
def BytesCtorInvariants (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] := BytesCtorInvariants.Internal ctor

def BytesCtorInvariants.into
  {id: CtorId} {ctor: BytesCtor} [ctor.HasCtorAt id]
  (f: BytesCtorInvariants id)
  : BytesCtorInvariants.ById id
  where
    well_formed := BytesFunCtor.into f.well_formed
    well_formed_later := BytesFunCtorProof1.into f.well_formed_later

    usage := BytesFunCtor.into f.usage
    usage_later := BytesFunCtorProof2.into f.usage_later

    label := BytesFunCtor.into f.label
    label_later := BytesFunCtorProof2.into f.label_later

    invariant := BytesFunCtor.into f.invariant
    invariant_implies_wellformed := BytesFunCtorProof2.into f.invariant_implies_wellformed
    invariant_later := BytesFunCtorProof1.into f.invariant_later


class BytesCtorsInvariants where
  funs: (id: CtorId) → BytesCtorInvariants.ById id

instance [BytesCtorsInvariants]: BytesWellFormed where
  funs id := (BytesCtorsInvariants.funs id).well_formed

instance [BytesCtorsInvariants]: BytesWellFormedLater where
  proofs id := (BytesCtorsInvariants.funs id).well_formed_later

instance [BytesCtorsInvariants]: GetUsage where
  funs id := (BytesCtorsInvariants.funs id).usage

instance [BytesCtorsInvariants]: GetUsageLater where
  proofs id := (BytesCtorsInvariants.funs id).usage_later

instance [BytesCtorsInvariants]: GetLabel where
  funs id := (BytesCtorsInvariants.funs id).label

instance [BytesCtorsInvariants]: GetLabelLater where
  proofs id := (BytesCtorsInvariants.funs id).label_later

instance [BytesCtorsInvariants]: BytesInvariant where
  funs id := (BytesCtorsInvariants.funs id).invariant

instance [BytesCtorsInvariants]: BytesInvariantImpliesBytesWellFormed where
  proofs id := (BytesCtorsInvariants.funs id).invariant_implies_wellformed

instance [BytesCtorsInvariants]: BytesInvariantLater where
  proofs id := (BytesCtorsInvariants.funs id).invariant_later

class HasBytesInvariants [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (funs: outParam (BytesCtorInvariants id)) where
  pf: BytesCtorsInvariants.funs id = funs.into

instance [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasBytesWellFormed id funs.well_formed where
  pf := by simp only [BytesWellFormed.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

instance [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasGetUsage id funs.usage where
  pf := by simp only [GetUsage.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

instance [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasGetLabel id funs.label where
  pf := by simp only [GetLabel.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

instance [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasBytesInvariant id funs.invariant where
  pf := by simp only [BytesInvariant.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

@[grind]
def Bytes.Publishable [BytesCtorsInvariants] (b: Bytes) (tr: ProofTrace) :=
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
  [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  (b: Bytes) (usg1 usg2: Usage) (tr: ProofTrace)
  :
    b.HasUsage usg1 tr →
    b.HasUsage usg2 tr →
    (usg1 = usg2 ∨ ((b.label tr).canFlow Label.pub tr))
  := by
    grind [Bytes.HasUsage]

theorem Bytes.HasUsage_public
  [BytesWellFormed] [GetUsage] [GetUsageLater] [GetLabel] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr: ProofTrace)
  :
    (b.label tr).canFlow Label.pub tr →
    b.HasUsage usg tr
  := by
    grind [Bytes.HasUsage]

noncomputable
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
