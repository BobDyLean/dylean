import DY.Bytes.Type
import DY.Label
import DY.Trace

namespace DY
-- Well formed

def BytesWellFormedT [BytesCtors] := ProofTrace → Prop
def BytesWellFormedT.default [BytesCtors]: BytesWellFormedT := fun _ => False

class BytesWellFormed [BytesCtors] where
  funs: BytesFunCtors BytesWellFormedT

def Bytes.wellFormed [BytesCtors] [BytesWellFormed] (b: Bytes) : BytesWellFormedT :=
  Bytes.mkRec BytesWellFormed.funs .default b

class HasBytesWellFormed [BytesCtors] [BytesWellFormed] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (binv: outParam (BytesFunCtor id BytesWellFormedT)) where
  pf: BytesWellFormed.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.wellFormed.eq
  [BytesCtors] [tc_binv: BytesWellFormed]
  (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor]
  {binv: BytesFunCtor id BytesWellFormedT}
  [tc: HasBytesWellFormed id binv]
  (b: BytesView id)
  (tr: ProofTrace)
  : Bytes.wellFormed (b.pack) tr = binv.func b.data b.dataBytes Bytes.wellFormed tr
  := by
    have lem {a b} (f g: a → b) (x: a): f = g → f x = g x := by grind
    apply lem
    apply Bytes.mkRec.eqView
    exact tc.pf

grind_pattern Bytes.wellFormed.eq => Bytes.wellFormed (b.pack) tr

-- Usage

structure Usage [BytesCtors] where
  type: String
  tag: String
  data: Option Bytes

def Usage.nothing [BytesCtors]: Usage where
  type := ""
  tag := ""
  data := none

def GetUsageT [BytesCtors] := ProofTrace → Usage
def GetUsageT.default [BytesCtors]: GetUsageT := fun _ => Usage.nothing

class GetUsage [BytesCtors] where
  funs: BytesFunCtors GetUsageT

noncomputable
def Bytes.usage [BytesCtors] [GetUsage] (b: Bytes) : GetUsageT :=
  Bytes.mkRec GetUsage.funs .default b

class HasGetUsage [BytesCtors] [GetUsage] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (binv: outParam (BytesFunCtor id GetUsageT)) where
  pf: GetUsage.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.usage.eq
  [BytesCtors] [tc_binv: GetUsage]
  (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor]
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

def GetUsageLaterT [BytesCtors] (x: BytesWellFormedT × GetUsageT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

class GetUsageLater [BytesCtors] [BytesWellFormed] [GetUsage] where
  proofs: BytesFunCtorsProof2 BytesWellFormed.funs GetUsage.funs GetUsageLaterT

theorem Bytes.usage_later
  [BytesCtors] [BytesWellFormed] [GetUsage] [GetUsageLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.wellFormed b tr1 →
  Bytes.usage b tr1 = Bytes.usage b tr2
  := by
    apply GetUsageLater.proofs.prove

grind_pattern Bytes.usage_later => Bytes.usage b tr1, tr1 ≤ tr2

-- Label

def GetLabelT [BytesCtors] := ProofTrace → Label
def GetLabelT.default [BytesCtors]: GetLabelT := fun _ => Label.secret

class GetLabel [BytesCtors] where
  funs: BytesFunCtors GetLabelT

noncomputable
def Bytes.label [BytesCtors] [GetLabel] (b: Bytes) : GetLabelT :=
  Bytes.mkRec GetLabel.funs .default b

class HasGetLabel [BytesCtors] [GetLabel] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (binv: outParam (BytesFunCtor id GetLabelT)) where
  pf: GetLabel.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.label.eq
  [BytesCtors] [tc_binv: GetLabel]
  (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor]
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

def GetLabelLaterT [BytesCtors] (x: BytesWellFormedT × GetLabelT) :=
  let (wf, usg) := x
  ∀ tr1 tr2: ProofTrace, tr1 ≤ tr2 → wf tr1 → usg tr1 = usg tr2

class GetLabelLater [BytesCtors] [BytesWellFormed] [GetLabel] where
  proofs: BytesFunCtorsProof2 BytesWellFormed.funs GetLabel.funs GetLabelLaterT

theorem Bytes.label_later
  [BytesCtors] [BytesWellFormed] [GetLabel] [GetLabelLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.wellFormed b tr1 →
  Bytes.label b tr1 = Bytes.label b tr2
  := by
    apply GetLabelLater.proofs.prove

grind_pattern Bytes.label_later => Bytes.label b tr1, tr1 ≤ tr2

-- Invariant

def BytesInvariantT [BytesCtors] := ProofTrace → Prop

def BytesInvariantT.default [BytesCtors]: BytesInvariantT := fun _ => False

class BytesInvariant [BytesCtors] where
  funs: BytesFunCtors BytesInvariantT

def Bytes.invariant [BytesCtors] [BytesInvariant] (b: Bytes) (tr: ProofTrace) : Prop :=
  Bytes.mkRec BytesInvariant.funs .default b tr

class HasBytesInvariant [BytesCtors] [BytesInvariant] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (binv: outParam (BytesFunCtor id BytesInvariantT)) where
  pf: BytesInvariant.funs id = binv.into
  dummy: Unit -- leanprover/lean4#11477 workaround

theorem Bytes.invariant.eq
  [BytesCtors] [tc_binv: BytesInvariant]
  (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor]
  {binv: BytesFunCtor id BytesInvariantT}
  [tc: HasBytesInvariant id binv]
  (b: BytesView id)
  (tr: ProofTrace)
  : Bytes.invariant (b.pack) tr = binv.func b.data b.dataBytes Bytes.invariant tr
  := by
    have lem {a b} (f g: a → b) (x: a): f = g → f x = g x := by grind
    apply lem
    apply Bytes.mkRec.eqView
    exact tc.pf

grind_pattern Bytes.invariant.eq => Bytes.invariant (b.pack) tr

-- Invariant implies well formed

def BytesInvariantImpliesBytesWellFormedT [BytesCtors] (x: BytesInvariantT × BytesWellFormedT) :=
  let (binv, bwf) := x
  ∀ tr, binv tr → bwf tr

class BytesInvariantImpliesBytesWellFormed [BytesCtors] [BytesWellFormed] [BytesInvariant] where
  proofs: BytesFunCtorsProof2 BytesInvariant.funs BytesWellFormed.funs BytesInvariantImpliesBytesWellFormedT

theorem Bytes.invariant_implies_wellformed
  [BytesCtors] [BytesWellFormed] [BytesInvariant] [BytesInvariantImpliesBytesWellFormed]
  (b: Bytes)
  (tr: ProofTrace)
  :
  Bytes.invariant b tr →
  Bytes.wellFormed b tr
  := by
    apply BytesInvariantImpliesBytesWellFormed.proofs.prove

grind_pattern Bytes.invariant_implies_wellformed => Bytes.wellFormed b tr, Bytes.invariant b tr

-- Invariant later

def BytesInvariantLaterT [BytesCtors] (binv: BytesInvariantT) :=
  ∀ tr1 tr2, tr1 ≤ tr2 → binv tr1 → binv tr2

class BytesInvariantLater [BytesCtors] [BytesInvariant] where
  proofs: BytesFunCtorsProof1 BytesInvariant.funs BytesInvariantLaterT

theorem Bytes.invariant.later
  [BytesCtors] [BytesInvariant] [BytesInvariantLater]
  (b: Bytes)
  (tr1 tr2: ProofTrace)
  :
  tr1 ≤ tr2 →
  Bytes.invariant b tr1 →
  Bytes.invariant b tr2
  := by
    apply BytesInvariantLater.proofs.prove

grind_pattern Bytes.invariant.later => Bytes.invariant b tr1, tr1 ≤ tr2

structure BytesCtorInvariants.Internal [BytesCtors] (ctor: BytesCtor) where
  well_formed: BytesFunCtor.Internal ctor BytesWellFormedT

  usage: BytesFunCtor.Internal ctor GetUsageT
  usage_later: BytesFunCtorProof2.Internal well_formed usage GetUsageLaterT

  label: [GetUsage] → BytesFunCtor.Internal ctor GetLabelT
  label_later: [BytesWellFormed] → [GetUsage] → [GetUsageLater] → BytesFunCtorProof2.Internal well_formed label GetLabelLaterT

  invariant: [GetUsage] → [GetLabel] → BytesFunCtor.Internal ctor BytesInvariantT
  invariant_implies_wellformed: [GetUsage] → [GetLabel] → BytesFunCtorProof2.Internal invariant well_formed BytesInvariantImpliesBytesWellFormedT
  invariant_later: [GetUsage] → [GetLabel] → BytesFunCtorProof1.Internal invariant BytesInvariantLaterT
  -- ...

def BytesCtorInvariants.ById [BytesCtors] (id: CtorId) := BytesCtorInvariants.Internal (BytesCtors.ctors id)
def BytesCtorInvariants [BytesCtors] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] := BytesCtorInvariants.Internal ctor

def BytesCtorInvariants.into
  [BytesCtors] {id: CtorId} {ctor: BytesCtor} [Bytes.HasCtorAt id ctor]
  (f: BytesCtorInvariants id)
  : BytesCtorInvariants.ById id
  where
    well_formed := BytesFunCtor.into f.well_formed

    usage := BytesFunCtor.into f.usage
    usage_later := BytesFunCtorProof2.into f.usage_later

    label := BytesFunCtor.into f.label
    label_later := BytesFunCtorProof2.into f.label_later

    invariant := BytesFunCtor.into f.invariant
    invariant_implies_wellformed := BytesFunCtorProof2.into f.invariant_implies_wellformed
    invariant_later := BytesFunCtorProof1.into f.invariant_later


class BytesCtorsInvariants [BytesCtors] where
  funs: (id: CtorId) → BytesCtorInvariants.ById id

instance [BytesCtors] [BytesCtorsInvariants]: BytesWellFormed where
  funs id := (BytesCtorsInvariants.funs id).well_formed

instance [BytesCtors] [BytesCtorsInvariants]: GetUsage where
  funs id := (BytesCtorsInvariants.funs id).usage

instance [BytesCtors] [BytesCtorsInvariants]: GetUsageLater where
  proofs id := (BytesCtorsInvariants.funs id).usage_later

instance [BytesCtors] [BytesCtorsInvariants]: GetLabel where
  funs id := (BytesCtorsInvariants.funs id).label

instance [BytesCtors] [BytesCtorsInvariants]: GetLabelLater where
  proofs id := (BytesCtorsInvariants.funs id).label_later

instance [BytesCtors] [BytesCtorsInvariants]: BytesInvariant where
  funs id := (BytesCtorsInvariants.funs id).invariant

instance [BytesCtors] [BytesCtorsInvariants]: BytesInvariantImpliesBytesWellFormed where
  proofs id := (BytesCtorsInvariants.funs id).invariant_implies_wellformed

instance [BytesCtors] [BytesCtorsInvariants]: BytesInvariantLater where
  proofs id := (BytesCtorsInvariants.funs id).invariant_later

class HasBytesInvariants [BytesCtors] [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (funs: outParam (BytesCtorInvariants id)) where
  pf: BytesCtorsInvariants.funs id = funs.into

instance [BytesCtors] [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasBytesWellFormed id funs.well_formed where
  pf := by simp only [BytesWellFormed.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

instance [BytesCtors] [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasGetUsage id funs.usage where
  pf := by simp only [GetUsage.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

instance [BytesCtors] [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasGetLabel id funs.label where
  pf := by simp only [GetLabel.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

instance [BytesCtors] [BytesCtorsInvariants] (id: CtorId) {ctor: BytesCtor} [Bytes.HasCtorAt id ctor] (funs: BytesCtorInvariants id) [tc: HasBytesInvariants id funs]: HasBytesInvariant id funs.invariant where
  pf := by simp only [BytesInvariant.funs, tc.pf, BytesCtorInvariants.into]
  dummy := ()

@[grind]
def Bytes.Publishable [BytesCtors] [BytesCtorsInvariants] (b: Bytes) (tr: ProofTrace) :=
  b.invariant tr ∧
  (b.label tr).canFlow Label.pub tr

end DY
