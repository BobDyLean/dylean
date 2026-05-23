module

public import DY.Trace
public import DY.Bytes
public import DY.Misc.Instances
import DY.Meta.Step

namespace DY.Random

section Trace

public
structure ExecEntryT where
  length: Nat

public
def baseAttackerKnowledge [BytesFunctor] [ExecTraceTypes]: SubBaseAttackerKnowledge ExecEntryT where
  attackerKnows _ _ _ := False

public
structure ProofEntryT [BytesFunctor] [ExecTraceTypes] where
  length: Nat
  label: Label
  usage: Usage

public
instance [BytesFunctor] [ExecTraceTypes]: ErasableProofEntry ExecEntryT ProofEntryT where
  erase | {length, label := _, usage := _} => { length }

public
instance[BytesFunctor] [ExecTraceTypes]: ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT where

public
instance [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]: SubTraceInvariant ProofEntryT where
  invariant _ _ := True

public
instance baseAttackerKnowledgeTheorem
  [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesInvariants]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  : SubBaseAttackerKnowledgeTheorem ProofEntryT baseAttackerKnowledge
where
  pf trBefore entry b := by
    simp [baseAttackerKnowledge]

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

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes.Has ExecEntryT]
variable [ProofTraceTypes.Has ProofEntryT]

public
def Random.invariants: Bytes.PartialInvariants Random where
  well_formed := fun {timestamp, size} _rec tr =>
    ∃ (label: Label) (usage: Usage),
    tr.at? timestamp = some ({length := size, label, usage}: ProofEntryT)

  usage := fun {timestamp, size := _} _rec tr =>
    match (tr.at? timestamp: Option ProofEntryT) with
    | some entry => entry.usage
    | none => Usage.nothing

  label := fun {timestamp, size := _} _rec tr =>
    match (tr.at? timestamp: Option ProofEntryT) with
    | some entry => entry.label
    | none => Label.pub

  invariant := fun {timestamp, size} _rec tr =>
    ∃ (label: Label) (usage: Usage),
    tr.at? timestamp = some ({length := size, label, usage}: ProofEntryT)

public
abbrev invariants: Bytes.PartialInvariants SubF := Random.Random.invariants

public
def Random.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Random.invariants where
  usage_later := by
    intro x rec tr1 tr2
    simp only [invariants]
    grind

  label_later := by
    intro _ x rec tr1 tr2
    simp only [invariants]
    grind

public
abbrev invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs invariants := Random.Random.invariantsProofs

variable [BytesInvariants] [BytesInvariants.Has invariants]

theorem makeRand.Invariant
  (timestamp size: Nat) (tr: ProofTrace)
  (label: Label) (usage: Usage)
  : Trace.at? tr timestamp = some ({ length := size, label := label, usage := usage }: ProofEntryT) → (
      (makeRand timestamp size: Bytes).Invariant tr ∧
      (makeRand timestamp size: Bytes).label tr = label ∧
      (makeRand timestamp size: Bytes).HasUsage usage tr
    )
:= by
  simp [makeRand, Bytes.label.eq, Bytes.usage.eq, Bytes.HasUsage, Bytes.Invariant.eq, Random.invariants]
  grind [Trace.at?_eq_some]

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [ExecTraceTypes.Has ExecEntryT]
variable [ProofTraceTypes.Has ProofEntryT]
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
  : HasGhostArgumentType (genRand size) ((Bytes → Label) × Usage)
where
  dummy := ()

@[instance]
public
theorem genRand.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesFunctor.Has SubF]
  [ExecTraceTypes.Has ExecEntryT] [ProofTraceTypes.Has ProofEntryT] [TraceInvariant.Has ProofEntryT]
  [BytesInvariants.Has invariants]
  (size: Nat)
  (label: Bytes → Label) (usage: Usage)
  : HoareTripleGhost
    (genRand size)
    (label, usage)
    (fun _ => True)
    (fun res tr =>
      -- length?
      -- last event in the trace? (for injectivity properties)
      res.Invariant tr ∧
      res.label tr = label res ∧
      res.HasUsage usage tr
    )
:= by
  apply HoareTripleGhost.mk
  unfold genRand
  dsimp only
  step with ⟨ fun time => ProofEntryT.mk size (label (makeRand time size)) usage ⟩ by
    simp_all [ErasableProofEntry.erase, SubTraceInvariant.invariant]
  step
  grind [makeRand.Invariant]

end DY.Random
