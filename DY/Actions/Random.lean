module

public import DY.Trace
public import DY.Bytes
public import DY.Trace.Manipulation
public import DY.Misc.Instances
import DY.Step.Init

namespace DY.Random

section Trace

public
structure ExecEntryT where
  length: Nat

public
def attKnows [BytesFunctor] [ExecTraceTypes]: ExecEntryAttackerKnowledge ExecEntryT where
  attackerKnows _ _ _ := False

public
structure ProofEntryT [BytesFunctor] [ExecTraceTypes] where
  length: Nat
  label: Label
  usage: Usage

public
def ProofEntryFunc [BytesFunctor] [ExecTraceTypes]: ProofEntryFun ExecEntryT ProofEntryT where
  erase | {length, label := _, usage := _} => { length }

public
def Invariant [BytesFunctor] [TraceTypes]: TraceEntryInvariant ProofEntryFunc where
  invariant _ _ := True

-- TODO attacker knowledge theorem

end Trace

section Bytes

section Constructors

public
structure Random (Bytes: Type) where
  timestamp: Nat
  size: Nat

public
instance: ALaCarte.FunctorSizeOf Random where
  sizeOf | {timestamp := _, size := _} => 0

public
instance: ALaCarte.Representable Random where
  CtorId := Unit
  ctors | () => { Data := Nat × Nat, nRec := 0 }

  toRepr | {timestamp, size} => {
    id := ()
    data := (timestamp, size)
    as := #v[]
  }
  fromRepr
  | {id, data := (timestamp, size), as} =>
    { timestamp, size }
  from_to | {timestamp, size} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {timestamp := _, size := _} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq Random where
public instance: ALaCarte.RepresentableOrd Random where
  ctorDataOrd | () => Ord.lex inferInstance inferInstance

public instance: SubBytesFunctor Random where

public
abbrev SubF := Random

public
def Random.length [BytesFunctor]: Bytes.PartialLength Random :=
  fun { timestamp := _, size := size } _ =>
    size

public
abbrev SubF.length [BytesFunctor]: Bytes.PartialLength SubF := Random.length

public
abbrev Random.pack [BytesFunctor] [BytesFunctor.Has SubF] (x: Random Bytes) := BytesView.pack x

def makeRand [BytesFunctor] [BytesFunctor.Has SubF] (timestamp size: Nat): Bytes :=
  ({timestamp, size}: Random Bytes).pack

end Constructors

section AttackerKnowledge

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def attKnowsRand: SubAttackerKnowledge Random where
  pred p out := False

public
abbrev attackerKnowledge := attKnowsRand

end AttackerKnowledge

section Invariants

variable [TraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [TraceTypes.Has ProofEntryFunc]

public
def Random.invariants: Bytes.PartialInvariants Random where
  well_formed := fun {timestamp, size} _rec tr =>
    ∃ (label: Label) (usage: Usage),
    tr.at_is timestamp ({length := size, label, usage}: ProofEntryT)

  usage := fun {timestamp, size := _} _rec tr =>
    if h_timestamp: timestamp < tr.length then
      match TraceTypes.Has.proofProj (tr.at timestamp h_timestamp) with
      | some (entry: ProofEntryT) =>
        entry.usage
      | none => Usage.nothing
    else
      Usage.nothing

  label := fun {timestamp, size := _} _rec tr =>
    if h_timestamp: timestamp < tr.length then
      match TraceTypes.Has.proofProj (tr.at timestamp h_timestamp) with
      | some (entry: ProofEntryT) =>
        entry.label
      | none => Label.pub
    else
      Label.pub

  invariant := fun {timestamp, size} _rec tr =>
    ∃ (label: Label) (usage: Usage),
    tr.at_is timestamp ({length := size, label, usage}: ProofEntryT)

public
abbrev invariants: Bytes.PartialInvariants SubF := Random.Random.invariants

public
def Random.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Random.invariants where
  usage_later := by
    intro x rec tr1 tr2
    let {timestamp, size} := x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetUsageLaterT, Trace.at_le tr1 tr2 timestamp]
    grind [Trace.at_is_imp_proofProj_at]

  label_later := by
    intro _ x rec tr1 tr2
    let {timestamp, size} := x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetLabelLaterT, Trace.at_le tr1 tr2 timestamp]
    grind [Trace.at_is_imp_proofProj_at]

public
abbrev invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs invariants := Random.Random.invariantsProofs

variable [BytesInvariants] [BytesInvariants.Has invariants]

theorem makeRand.Invariant
  (timestamp size: Nat) (tr: ProofTrace)
  (label: Label) (usage: Usage)
  : Trace.at_is tr timestamp ({ length := size, label := label, usage := usage }: ProofEntryT) → (
      (makeRand timestamp size: Bytes).Invariant tr ∧
      (makeRand timestamp size: Bytes).label tr = label ∧
      (makeRand timestamp size: Bytes).HasUsage usage tr
    )
:= by
  simp [makeRand, Bytes.label.eq, Bytes.usage.eq, Bytes.HasUsage, Bytes.Invariant.eq, Random.invariants]
  grind [Trace.at_is_imp_proofProj_at]

end Invariants

section AttackerKnowledgeTheorem

variable [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [TraceTypes.Has ProofEntryFunc]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem attKnowsRand where
  pf := by simp [attKnowsRand]

example: SubAttackerKnowledgeTheorem attackerKnowledge := inferInstance

end AttackerKnowledgeTheorem

end Bytes

public
def genRand [BytesFunctor] [BytesFunctor.Has SubF] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT] (size: Nat): Traceful Bytes :=
  do
  let entry: ExecEntryT := { length := size }
  let time ← appendEntry entry
  return makeRand time size

public
instance
  [BytesFunctor] [BytesFunctor.Has SubF] [ExecTraceTypes] [ExecTraceTypes.Has ExecEntryT]
  (size: Nat)
  : HasGhostArgumentType (genRand size) (Label × Usage)
where
  dummy := ()

@[instance]
public
theorem genRand.spec
  [BytesFunctor]
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesFunctor.Has SubF]
  [TraceInvariant.Has Invariant]
  [BytesInvariants.Has invariants]
  (size: Nat)
  (label: Label) (usage: Usage)
  : HoareTripleGhost
    (genRand size)
    (label, usage)
    (fun _ => True)
    (fun res tr =>
      -- length?
      -- last event in the trace? (for injectivity properties)
      res.Invariant tr ∧
      res.label tr = label ∧
      res.HasUsage usage tr
    )
:= by
  apply HoareTripleGhost.mk
  unfold genRand
  dsimp only
  step with ⟨ ProofEntryT.mk size label usage ⟩ by
    simp_all [ProofEntryFunc, Invariant]
  step
  grind [makeRand.Invariant]

end DY.Random
