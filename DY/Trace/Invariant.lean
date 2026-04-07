module

public import DY.Trace.Basic
import all DY.Trace.Basic
public meta import DY.Trace.Grind

namespace DY

public
class ErasableProofEntry (ExecEntryT: outParam Type) (ProofEntryT: Type) where
  erase: ProofEntryT → ExecEntryT

public
abbrev ErasableProofEntry.default (ExecEntryT: Type): ErasableProofEntry ExecEntryT ExecEntryT where
  erase x := x

public
class TraceTypes extends ExecTraceTypes where
  ProofT: Type
  tc: ErasableProofEntry ExecT ProofT

@[expose]
public
def ProofTrace.Entry [TraceTypes] := TraceTypes.ProofT

public
instance [TraceTypes]: ErasableProofEntry ExecTrace.Entry ProofTrace.Entry where
  erase entry := TraceTypes.tc.erase entry

public
abbrev ProofTrace [TraceTypes] := Trace ProofTrace.Entry

@[expose]
public
def ProofTrace.Entry.erase
  [TraceTypes]
  (entry: ProofTrace.Entry)
  : ExecTrace.Entry
:=
  ErasableProofEntry.erase entry

public
def Trace.erase
  [TraceTypes]
  (tr: ProofTrace)
  : ExecTrace
:=
  match tr with
  | .nil => .nil
  | .snoc trBefore entry => .snoc trBefore.erase entry.erase

public
theorem Trace.erase_le
  [TraceTypes]
  (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    tr1.erase ≤ tr2.erase
:= by
  intro h_le
  induction h_le
  · apply Trace.le.equal
  · apply Trace.le.extend
    assumption

grind_pattern Trace.erase_le => tr1 ≤ tr2, tr1.erase
grind_pattern [grind_later] Trace.erase_le => tr1 ≤ tr2, tr1.erase

public
theorem Trace.erase_length
  [TraceTypes]
  (tr: ProofTrace)
  : tr.erase.length = tr.length
:= by
  induction tr <;>
  simp_all [Trace.length, Trace.erase]

grind_pattern Trace.erase_length => tr.erase.length

public
def Trace.erase_at
  [TraceTypes]
  (tr: ProofTrace)
  (i: Nat) (h_i: i < tr.erase.length)
  : tr.erase.at i h_i = (tr.at i (Trace.erase_length tr ▸ h_i)).erase
:= by
  induction tr <;>
  simp only [Trace.at, Trace.erase]
  · grind
  split <;>
  grind [Trace.erase_length]

-- TODO test coercion
example [TraceTypes]: Coe ProofTrace ExecTrace where
  coe tr := tr.erase

public
class TraceTypes.Has
  [TraceTypes]
  {ExecEntryT: outParam Type} (ProofEntryT: Type)
  [ErasableProofEntry ExecEntryT ProofEntryT]
  extends ExecTraceTypes.Has ExecEntryT
where
  proofInj: ProofEntryT → ProofTrace.Entry
  proofProj: ProofTrace.Entry → Option ProofEntryT
  proof_inj_proj_eq: ∀ x y, (proofProj x = some y) = (x = proofInj y)
  proofProj_none_eq_erase: ∀ x, ((proofProj x: Option ProofEntryT) = none) = ((proj x.erase: Option ExecEntryT) = none)
  erase_commutes: ∀ entry, (proofInj entry).erase = inj (ErasableProofEntry.erase entry)

public
class TraceTypes.HasStep
  {ExecEntryT1 ExecEntryT2: outParam Type}
  (ProofEntryT1: Type) (ProofEntryT2: semiOutParam Type)
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  extends ExecTraceTypes.HasStep ExecEntryT1 ExecEntryT2
where
  proofInj: ProofEntryT1 → ProofEntryT2
  proofProj: ProofEntryT2 → Option ProofEntryT1
  proof_inj_proj_eq: ∀ x y, (proofProj x = some y) = (x = proofInj y)
  proofProj_none_eq_erase: ∀ x, ((proofProj x: Option ProofEntryT1) = none) = ((proj (ErasableProofEntry.erase x): Option ExecEntryT1) = none)
  erase_commutes: ∀ entry, ErasableProofEntry.erase (proofInj entry) = inj (ErasableProofEntry.erase entry)

public
instance instTraceTypesHasItself
  [TraceTypes]
  : TraceTypes.Has ProofTrace.Entry
where
  proofInj entry := entry
  proofProj entry := some entry
  proof_inj_proj_eq := by grind
  proofProj_none_eq_erase := by simp [ExecTraceTypes.Has.proj]
  erase_commutes := by simp [ExecTraceTypes.Has.inj, ProofTrace.Entry.erase]

public
instance instTraceTypesHasStep
  [TraceTypes]
  {ExecEntryT1 ExecEntryT2: Type}
  (ProofEntryT1 ProofEntryT2: Type)
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [TraceTypes.HasStep ProofEntryT1 ProofEntryT2]
  [TraceTypes.Has ProofEntryT2]
  : TraceTypes.Has ProofEntryT1
where
  proofInj entry := TraceTypes.Has.proofInj (TraceTypes.HasStep.proofInj (ProofEntryT2 := ProofEntryT2) entry)
  proofProj entry :=
    match TraceTypes.Has.proofProj (ProofEntryT := ProofEntryT2) entry with
    | none => none
    | some y => TraceTypes.HasStep.proofProj y

  proof_inj_proj_eq x y := by
    have := TraceTypes.Has.proof_inj_proj_eq (ProofEntryT := ProofEntryT2) x
    have := TraceTypes.HasStep.proof_inj_proj_eq (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    grind
  proofProj_none_eq_erase := by
    intro x
    have := ExecTraceTypes.Has.inj_proj_eq (ExecEntryT := ExecEntryT2)
    have := TraceTypes.Has.proof_inj_proj_eq (ProofEntryT := ProofEntryT2)
    have := TraceTypes.Has.proofProj_none_eq_erase (ProofEntryT := ProofEntryT2)
    have := TraceTypes.HasStep.proofProj_none_eq_erase (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    have := TraceTypes.Has.erase_commutes (ProofEntryT := ProofEntryT2)
    simp [ExecTraceTypes.Has.proj]
    grind
  erase_commutes := by
    have := TraceTypes.Has.erase_commutes (ProofEntryT := ProofEntryT2)
    have := TraceTypes.HasStep.erase_commutes (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    simp [ExecTraceTypes.Has.inj]
    grind

public
instance [TraceTypes] {ExecEntryT: Type} (ProofEntryT: Type) [ErasableProofEntry ExecEntryT ProofEntryT] [TraceTypes.Has ProofEntryT]: IntoTraceEntry ProofEntryT ProofTrace.Entry where
  make entry := TraceTypes.Has.proofInj entry

public
structure TraceTypes.combine {n: Nat} (ProofTypes: Fin n → Type): Type where
  id: Fin n
  entry: ProofTypes id

public
instance
  {n: Nat}
  (ExecTypes: Fin n → Type)
  (ProofTypes: Fin n → Type)
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  : ErasableProofEntry (ExecTraceTypes.combine ExecTypes) (TraceTypes.combine ProofTypes)
where
  erase := fun { id, entry } => { id, entry := ErasableProofEntry.erase entry }

public
instance instTraceTypesCombineHasStep
  {n: Nat}
  (ExecTypes: Fin n → Type)
  (ProofTypes: Fin n → Type)
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  (id: Fin n):
  TraceTypes.HasStep (ProofTypes id) (TraceTypes.combine ProofTypes)
where
  proofInj entry := { id, entry }
  proofProj entry :=
    if h: entry.id = id then
      some (h ▸ entry.entry)
    else
      none
  proof_inj_proj_eq x y := by
    cases x
    grind
  proofProj_none_eq_erase x := by
    simp [ExecTraceTypes.HasStep.proj, ErasableProofEntry.erase]
  erase_commutes _ := rfl

public
theorem ProofTrace.Entry.erase_eq_imp_exists
  [TraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [TraceTypes.Has ProofEntryT]
  {entry: ProofTrace.Entry}
  {result: ExecEntryT}
  : entry.erase = ExecTraceTypes.Has.inj result ↔ (
      ∃ result': ProofEntryT,
      entry = TraceTypes.Has.proofInj result' ∧
      ErasableProofEntry.erase result' = result
    )
:= by
  cases h: (TraceTypes.Has.proofProj entry: Option ProofEntryT)
  · have := TraceTypes.Has.proofProj_none_eq_erase (ProofEntryT := ProofEntryT) entry
    rewrite [← ExecTraceTypes.Has.inj_proj_eq]
    simp_all only [reduceCtorEq, false_iff, not_exists]
    intro x
    have := TraceTypes.Has.proof_inj_proj_eq entry x
    grind
  · rename_i result'
    rewrite [TraceTypes.Has.proof_inj_proj_eq] at h
    grind [TraceTypes.Has.erase_commutes]

public
theorem Trace.append_erase
  [TraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [TraceTypes.Has ProofEntryT]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).erase = tr.erase.append (ErasableProofEntry.erase entry)
:= by
  simp [Trace.append, Trace.erase, IntoTraceEntry.make, TraceTypes.Has.erase_commutes]

public
theorem Trace.at_is_imp_proofProj_at
  [TraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [TraceTypes.Has ProofEntryT]
  (tr: ProofTrace) (i: Nat) (entry: ProofEntryT)
  : tr.at_is i entry →
    exists h: i < tr.length,
    TraceTypes.Has.proofProj (tr.at i h) = some entry
:= by
  simp only [Trace.at_is, IntoTraceEntry.make]
  intro ⟨ h1, h2 ⟩
  exists h1
  grind [TraceTypes.Has.proof_inj_proj_eq]

public
theorem Trace.at_is_erase
  [TraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [TraceTypes.Has ProofEntryT]
  (tr: ProofTrace) (i: Nat) (entry: ProofEntryT)
  : tr.at_is i entry →
    tr.erase.at_is i (ErasableProofEntry.erase entry)
:= by
  simp only [Trace.at_is, IntoTraceEntry.make]
  intro ⟨ h1, h2 ⟩
  simp_all [Trace.erase_at, TraceTypes.Has.erase_commutes]
  grind

-- Invariant

public
class ProofEntryInvariant [TraceTypes] {ExecEntryT: outParam Type} (ProofEntryT: Type) [ErasableProofEntry ExecEntryT ProofEntryT] where
  invariant: ProofTrace → ProofEntryT → Prop

public
class TraceInvariant extends TraceTypes where
  tc_inv: ProofEntryInvariant ProofTrace.Entry

public
instance [TraceInvariant]: ProofEntryInvariant ProofTrace.Entry where
  invariant := TraceInvariant.tc_inv.invariant

public
def ProofTrace.Entry.Invariant
  [TraceInvariant]
  (trBefore: ProofTrace)
  (entry: ProofTrace.Entry)
  : Prop
:=
  ProofEntryInvariant.invariant trBefore entry

public
def Trace.Invariant
  [TraceInvariant]
  (tr: ProofTrace)
  : Prop
:=
  match tr with
  | .nil => True
  | .snoc trBefore entry =>
    trBefore.Invariant ∧
    entry.Invariant trBefore

public
class TraceInvariant.Has
  [TraceInvariant]
  {ExecEntryT: outParam Type}
  (ProofEntryT: Type)
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [TraceTypes.Has ProofEntryT]
  [ProofEntryInvariant ProofEntryT]
where
  inv_commutes: ∀ trBefore: ProofTrace, ∀ entry: ProofEntryT, (TraceTypes.Has.proofInj entry).Invariant trBefore = ProofEntryInvariant.invariant trBefore entry

public
class TraceInvariant.HasStep
  [TraceTypes]
  {ExecEntryT1 ExecEntryT2: outParam Type}
  (ProofEntryT1 ProofEntryT2: Type)
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [TraceTypes.HasStep ProofEntryT1 ProofEntryT2]
  [ProofEntryInvariant ProofEntryT1]
  [ProofEntryInvariant ProofEntryT2]
where
  inv_commutes: ∀ trBefore: ProofTrace, ∀ entry: ProofEntryT1, ProofEntryInvariant.invariant trBefore (TraceTypes.HasStep.proofInj entry: ProofEntryT2) = ProofEntryInvariant.invariant trBefore entry

public
instance instTraceInvariantHasItself
  [TraceInvariant]
  : TraceInvariant.Has ProofTrace.Entry
where
  inv_commutes := by simp [TraceTypes.Has.proofInj, ProofTrace.Entry.Invariant]

public
instance instTraceInvariantHasStep
  [TraceInvariant]
  {ExecEntryT1 ProofEntryT1: Type}
  {ExecEntryT2 ProofEntryT2: Type}
  [ErasableProofEntry ExecEntryT1 ProofEntryT1]
  [ErasableProofEntry ExecEntryT2 ProofEntryT2]
  [TraceTypes.HasStep ProofEntryT1 ProofEntryT2]
  [TraceTypes.Has ProofEntryT2]
  [ProofEntryInvariant ProofEntryT1]
  [ProofEntryInvariant ProofEntryT2]
  [TraceInvariant.HasStep ProofEntryT1 ProofEntryT2]
  [TraceInvariant.Has ProofEntryT2]
  : TraceInvariant.Has ProofEntryT1
where
  inv_commutes := by
    have := TraceInvariant.HasStep.inv_commutes (ProofEntryT1 := ProofEntryT1) (ProofEntryT2 := ProofEntryT2)
    have := TraceInvariant.Has.inv_commutes (ProofEntryT := ProofEntryT2)
    simp_all [TraceTypes.Has.proofInj]

public
instance ProofEntryInvariant.combine
  [TraceTypes]
  {n: Nat}
  {ExecTypes: Fin n → Type}
  {ProofTypes: Fin n → Type}
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  [∀ id, ProofEntryInvariant (ProofTypes id)]
  : ProofEntryInvariant (TraceTypes.combine ProofTypes)
where
  invariant := fun trBefore { id := _, entry } =>
    ProofEntryInvariant.invariant trBefore entry

public
instance instTraceInvariantCombineHasStep
  [TraceTypes]
  {n: Nat}
  {ExecTypes: Fin n → Type}
  (ProofTypes: Fin n → Type)
  [∀ id, ErasableProofEntry (ExecTypes id) (ProofTypes id)]
  [∀ id, ProofEntryInvariant (ProofTypes id)]
  (id: Fin n)
  : TraceInvariant.HasStep (ProofTypes id) (TraceTypes.combine ProofTypes)
where
  inv_commutes trBefore entry := by rfl

public
theorem Trace.invariant_append
  [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [TraceTypes.Has ProofEntryT]
  [ProofEntryInvariant ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (tr: ProofTrace) (entry: ProofEntryT)
  : (tr.append entry).Invariant = (tr.Invariant ∧ ProofEntryInvariant.invariant tr entry)
:= by
  have := TraceInvariant.Has.inv_commutes (ProofEntryT := ProofEntryT)
  simp_all [Trace.Invariant, Trace.append, IntoTraceEntry.make]

public
theorem Trace.invariant_at
  [TraceInvariant]
  (tr: ProofTrace)
  (i: Nat)
  (h_i: i < tr.length)
  : tr.Invariant →
    (tr.at i h_i).Invariant (tr.prefix i)
:= by
  fun_induction Trace.at <;>
  grind [Trace.Invariant, Trace.prefix, Trace.length]

end DY
