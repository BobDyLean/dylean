module

public import DY.Trace
public import DY.Bytes
public import DY.Misc.Instances
public import DY.Actions.Network
import DY.Meta.Step

namespace DY.Random

section Trace

public
structure TracePart.Exec where
  length: Nat

public
def TracePart.baseAttackerKnows [Bytes.Def] [ExecTrace.Def]: Trace.BaseAttackerKnows.Part TracePart.Exec where
  attackerKnows _ _ _ := False

public
structure TracePart.Proof [Bytes.Def] [ExecTrace.Def] where
  length: Nat
  label: Label
  usage: Usage

public
instance [Bytes.Def] [ExecTrace.Def]: ProofTrace.Part TracePart.Exec TracePart.Proof where
  erase | {length, label := _, usage := _} => { length }

public
instance[Bytes.Def] [ExecTrace.Def]: ExecEntryAssociatedWithProofEntry TracePart.Exec TracePart.Proof where

public
instance TracePart.invariant [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def]: Trace.Invariant.Part TracePart.Proof where
  invariant _ _ := True

public
instance
  [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def] [Bytes.Invariants.Def]
  [ExecTrace.Has TracePart.Exec]
  [ProofTrace.Has TracePart.Proof]
  [Trace.Invariant.Has TracePart.Proof]
  : Trace.BaseAttackerKnows_implies_Publishable.Part TracePart.Proof TracePart.baseAttackerKnows
where
  pf trBefore entry b := by
    simp [TracePart.baseAttackerKnows]

end Trace

section Bytes

section Constructors

public
structure BytesPart.Functor (Bytes: Type) where
  timestamp: Nat
  size: Nat

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {timestamp := _, size := _} => 0

public
instance: ALaCarte.Representable BytesPart.Functor where
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

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
  ctorDataOrd | () => Ord.lex inferInstance inferInstance

public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun { timestamp := _, size := size } _ =>
    size

public
abbrev BytesPart.Functor.pack [Bytes.Def] [Bytes.Has BytesPart.Functor] (x: BytesPart.Functor Bytes) := BytesView.pack x

def makeRand [Bytes.Def] [Bytes.Has BytesPart.Functor] (timestamp size: Nat): Bytes :=
  ({timestamp, size}: BytesPart.Functor Bytes).pack

end Constructors

section AttackerKnowledge

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

public
def attackerKnows: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out := False

end AttackerKnowledge

section Invariants

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def]
variable [ExecTrace.Has TracePart.Exec]
variable [ProofTrace.Has TracePart.Proof]

public
def BytesPart.invariants: Bytes.Invariants.Part BytesPart.Functor where
  well_formed := fun {timestamp, size} _rec tr =>
    ∃ (label: Label) (usage: Usage),
    tr.at? timestamp = some ({length := size, label, usage}: TracePart.Proof)

  usage := fun {timestamp, size := _} _rec tr =>
    match (tr.at? timestamp: Option TracePart.Proof) with
    | some entry => entry.usage
    | none => Usage.nothing

  label := fun {timestamp, size := _} _rec tr =>
    match (tr.at? timestamp: Option TracePart.Proof) with
    | some entry => entry.label
    | none => Label.pub

  invariant := fun {timestamp, size} _rec tr =>
    ∃ (label: Label) (usage: Usage),
    tr.at? timestamp = some ({length := size, label, usage}: TracePart.Proof)

public
theorem BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful BytesPart.invariants where
  usage_later := by
    intro x rec tr1 tr2
    simp only [BytesPart.invariants]
    grind

  label_later := by
    intro _ x rec tr1 tr2
    simp only [BytesPart.invariants]
    grind

variable [Bytes.Has BytesPart.Functor]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]

theorem makeRand.Invariant
  (timestamp size: Nat) (tr: ProofTrace)
  (label: Label) (usage: Usage)
  : Trace.at? tr timestamp = some ({ length := size, label := label, usage := usage }: TracePart.Proof) → (
      (makeRand timestamp size: Bytes).Invariant tr ∧
      (makeRand timestamp size: Bytes).label tr = label ∧
      (makeRand timestamp size: Bytes).HasUsage usage tr
    )
:= by
  simp [makeRand, Bytes.label.eq, Bytes.usage.eq, Bytes.HasUsage, Bytes.Invariant.eq, BytesPart.invariants]
  grind [Trace.at?_eq_some]

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Has TracePart.Exec]
variable [ProofTrace.Has TracePart.Proof]
variable [Bytes.Invariants.Has BytesPart.invariants]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part attackerKnows where
  pf := by simp [attackerKnows]

end AttackerKnowledgeTheorem

end Bytes

public
def genRand [Bytes.Def] [Bytes.Has BytesPart.Functor] [ExecTrace.Def] [ExecTrace.Has TracePart.Exec] (size: Nat): Traceful Bytes :=
  do
  let entry: TracePart.Exec := { length := size }
  let time ← appendEntry entry
  return makeRand time size

public
instance
  [Bytes.Def] [Bytes.Has BytesPart.Functor] [ExecTrace.Def] [ExecTrace.Has TracePart.Exec]
  (size: Nat)
  : HasGhostArgumentType (genRand size) ((Bytes → Label) × Usage)
where
  dummy := ()

@[instance]
public
theorem genRand.proof
  [Bytes.Def]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.Has BytesPart.Functor]
  [ExecTrace.Has TracePart.Exec] [ProofTrace.Has TracePart.Proof] [Trace.Invariant.Has TracePart.Proof]
  [Bytes.Invariants.Has BytesPart.invariants]
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
  step with ⟨ fun time => TracePart.Proof.mk size (label (makeRand time size)) usage ⟩ by
    simp_all [ProofTrace.Part.erase, Trace.Invariant.Part.invariant]
  step
  grind [makeRand.Invariant]

public
def attackerGenRandAux [Bytes.Def] [Bytes.Has BytesPart.Functor] [ExecTrace.Def] [ExecTrace.Has TracePart.Exec] [ExecTrace.Has Network.TracePart.Exec] (size: Nat): Traceful Nat :=
  do
  let r ← genRand size
  Network.sendMessage r

@[instance]
public
theorem attackerGenRandAux.proof
  [Bytes.Def]
  [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.Has BytesPart.Functor]
  [ExecTrace.Has TracePart.Exec] [ProofTrace.Has TracePart.Proof] [Trace.Invariant.Has TracePart.Proof]
  [ExecTrace.Has Network.TracePart.Exec] [ProofTrace.Has Network.TracePart.Proof] [Trace.Invariant.Has Network.TracePart.Proof]
  [Bytes.Invariants.Has BytesPart.invariants]
  (size: Nat)
  : HoareTriple
    (attackerGenRandAux size)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold attackerGenRandAux
  step with ⟨ fun _ => Label.pub, Usage.nothing ⟩
  step
  grind


public
def attackerGenRand [Bytes.Def] [Bytes.Has BytesPart.Functor] [ExecTrace.Def] [ExecTrace.Has TracePart.Exec] [ExecTrace.Has Network.TracePart.Exec] (size: Nat): Traceful Bytes :=
  do
  let rHandle ← attackerGenRandAux size
  Network.receiveMessage rHandle

section Reachability

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [ExecTrace.Has TracePart.Exec] [ExecTrace.Has Network.TracePart.Exec]
variable [Trace.BaseAttackerKnows.Def] [Bytes.AttackerKnows.Def]

public
abbrev transitionSystem : TransitionSystem where
  Input := Nat
  PreCond _ _ := True
  step size := ⟨ _, attackerGenRandAux size ⟩

public
theorem attackerGenRand.preservesReachability
  [Trace.BaseAttackerKnows.Has Network.TracePart.baseAttackerKnows]
  (config: TransitionSystem)
  [TransitionSystem.Has transitionSystem config]
  (size: Nat)
  : (attackerGenRand size).PreservesReachability config (fun _ => True) (fun r tr => r.AttackerKnows tr)
:= by
  dsimp only [attackerGenRand, Traceful.PreservesReachability]
  intro tr h_reach h_pre
  apply Traceful.PreservesReachabilityFrom_bind
  · apply Traceful.PreservesReachability_base (transitionSystem)
  · grind
  · grind
  intro entry tr h_post h_reach h_le

  apply Network.receiveMessage.preservesReachability
  · grind
  · grind


variable [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
variable [ProofTrace.Has TracePart.Proof] [Trace.Invariant.Has TracePart.Proof]
variable [ProofTrace.Has Network.TracePart.Proof] [Trace.Invariant.Has Network.TracePart.Proof]
variable [Bytes.Invariants.Has BytesPart.invariants]
variable [Trace.BaseAttackerKnows_implies_Publishable.Proof] [Bytes.AttackerKnows_implies_Publishable.Proof]

public
instance: Trace.Reachable_implies_Invariant.Part transitionSystem
where
  pf size := by
    apply HoareTriple.mk
    have := (attackerGenRandAux.proof size).pf
    unfold hoareTriple at *
    grind [Bytes.AttackerKnows_implies_Publishable]

end Reachability

end DY.Random
