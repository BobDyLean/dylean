module

import Init.Control.Lawful.Basic
public import Lean
public import DY.Bytes.Basic
public import DY.Trace.Basic
public import DY.Trace.Invariant
public import DY.Label

@[expose] public section

namespace DY

abbrev Traceful [ExecTraceTypes] := OptionT (StateT ExecTrace Id)
abbrev Err := OptionT Id

instance [ExecTraceTypes]: MonadLift Err Traceful := {
  monadLift := fun x => StateT.pure x.run
}

def Traceful.run [ExecTraceTypes] (x: Traceful a) (tr: ExecTrace): (Option a × ExecTrace) :=
  Id.run (StateT.run (OptionT.run x) tr)

def Traceful.mk [ExecTraceTypes] {α: Type} (f: ExecTrace → (Option α × ExecTrace)): Traceful α :=
  OptionT.mk (StateT.mk f)

def Traceful.run_mk
  [ExecTraceTypes] {α: Type}
  (f: ExecTrace → (Option α × ExecTrace))
  : Traceful.run (Traceful.mk f) = f
:= by
  rfl

-- This is missing from Lean's standard library??
theorem OptionT.run_pure {m : Type u → Type v} [Monad m] {α : Type u} (x : α) :
  OptionT.run (pure x) = some (pure x)
  := rfl

-- This is missing from Lean's standard library??
theorem OptionT.run_bind {m : Type u → Type v} [Monad m] {α β : Type u} (x : OptionT m α) (f : α → OptionT m β) :
  (x >>= f).run = (do
    match (← x.run) with
    | some a => (f a).run
    | none   => pure none
  )
  := rfl

theorem Traceful.run_pure
  [ExecTraceTypes]
  (x: a) (tr: ExecTrace)
  : Traceful.run (pure x) tr = (some x, tr)
:= by
  rfl

theorem Traceful.run_bind
  [ExecTraceTypes]
  (x: Traceful a) (f: a → Traceful b) (tr: ExecTrace)
  : Traceful.run (x >>= f) tr = (
    let (opt_x, tr) := x.run tr
    match opt_x with
    | some x => (f x).run tr
    | none => (none, tr)
  )
:= by
  simp only [Traceful.run, OptionT.run_bind, StateT.run_bind, Id.run_bind]
  split
  · simp_all
  · simp_all

theorem Traceful.run_failure
  [ExecTraceTypes]
  (tr: ExecTrace)
  : Traceful.run (failure: Traceful a) tr = (none, tr)
:= by
  rfl


class WP [ExecTraceTypes] [ProofTraceTypes] (m: Type u → Type v) where
  wp: m a → (a → ProofTrace → Prop) → (ProofTrace → Prop)

export WP (wp)

instance [ExecTraceTypes] [ProofTraceTypes]: WP Id where
  wp f post tr_proof :=
    post f.run tr_proof

instance [ExecTraceTypes] [ProofTraceTypes]: WP Err where
  wp f post tr_proof :=
    match f.run with
    | .none => True
    | .some x => post x tr_proof

instance [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]: WP Traceful where
  wp f post tr_proof :=
    let (opt_x, tr_exec') := f.run tr_proof.erase
    ∃ tr_proof',
      (
        match opt_x with
        | .none => True
        | .some x => post x tr_proof'
      ) ∧
      Trace.Invariant tr_proof' ∧
      tr_exec' = tr_proof'.erase ∧
      tr_proof ≤ tr_proof'

def hoareTriple [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [WP m] (f: m a) (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop): Prop :=
  ∀ tr,
    pre tr →
    Trace.Invariant tr →
    WP.wp f post tr

/--
  This typeclass notifies the `step` tactic that
  the hoare triple for `x` expects a ghost parameter of type `g`.
  Knowing this type is crucial to provide useful error message
  when a user provides a ghost parameter with the wrong type.
-/
class HasGhostArgumentType (x: a) (g: outParam (Type u_g)) where
  dummy: Unit

/--
  Some ghost parameters can be found automatically
  by looking into the context.
  This structure holds a metaprogram
  which is called with a metavariable for the ghost parameter,
  and the expression corresponding to the hoare triple that requires the ghost parameter.
  It is expected to assign the ghost parameter metavariable.
-/
structure GhostParameterFinder where
  findGhost: Lean.MVarId → Lean.Expr → Lean.MetaM Unit

/--
  This typeclass notifies the `step` tactic that
  `metaprog` can automatically find the ghost parameter
  of the the hoare triple associated with `x`.
  For technical reasons, `metaprog` must be a top-level declaration,
  it cannot be written inline in the declaration.
  This is to prevent it to depend on local variables specific to this instance.
-/
class HasGhostMetaprogram {a: Sort u_1} (x: a) (metaprog: outParam GhostParameterFinder) where
  dummy: Unit

/--
  Some hoare triples are derived from others,
  for example we can create a hoare triple for `lift x` given a hoare triple for `x`.
  In this case, both hoare triple use the same ghost parameter,
  but the metaprogram that finds the ghost parameter for `x`
  won't work if we feed it `lift x` instead of `x`.
  To solve this issue,
  `HasIndirectGhostMetaprogram x metaprog y`
  notifies the `step` tactic
  that `metaprog` is expected to be called with the expression of `y`
  instead of the expression of `x`.
-/
class HasIndirectGhostMetaprogram {a: Sort u_1} {b: outParam (Sort u_2)} (x: a) (metaprog: outParam GhostParameterFinder) (y: outParam b) where
  dummy: Unit

instance [HasGhostMetaprogram x metaprog]: HasIndirectGhostMetaprogram x metaprog x
where
  dummy := ()

class HoareTripleGhost [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [WP m] (f: m a) [HasGhostArgumentType f g] (ghost: g) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: hoareTriple f pre post

class HoareTriple [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [WP m] (f: m a) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: hoareTriple f pre post

instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {m :Type u → Type v} [WP m]
  {a: Type u}
  (f: m a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriple f pre post]
  : HasGhostArgumentType f Unit
where
  dummy := ()

instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {m :Type u → Type v} [WP m]
  {a: Type u}
  (f: m a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriple f pre post]
  : HoareTripleGhost f () pre post
where
  pf := HoareTriple.pf

class WPLift
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  (m: Type u → Type v) (n : Type u → Type w)
  [MonadLift m n] [WP m] [WP n]
where
  pf {a: Type u} (x: m a) (post: a → ProofTrace → Prop) (tr: ProofTrace):
    tr.Invariant →
    wp x post tr →
    wp (liftM x: n a) post tr

instance
  {m: Type u → Type v} {n: Type u → Type w} [MonadLift m n]
  {a: Type u} {g: Type u_g}
  (x: m a)
  [HasGhostArgumentType x g]
  : HasGhostArgumentType (liftM x: n a) g
where
  dummy := ()

instance
  {m: Type u → Type v} {n: Type u → Type w} [MonadLift m n]
  {a: Type u} {b: Type z}
  (x: m a)
  (y: b)
  [HasIndirectGhostMetaprogram x metaprog y]
  : HasIndirectGhostMetaprogram (liftM x: n a) metaprog y
where
  dummy := ()

instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {m: Type u → Type v} {n: Type u → Type w} [MonadLift m n] [WP m] [WP n] [wplift: WPLift m n]
  {a: Type u} {g: Type u_g}
  (x: m a) (ghost: g) (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HasGhostArgumentType x g]
  [ht: HoareTripleGhost x ghost pre post]
  : HoareTripleGhost (liftM x: n a) ghost pre post
where
  pf := by
    have := ht.pf
    have := wplift.pf x
    grind [hoareTriple]

instance [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]: WPLift Err Traceful where
  pf := by
    -- ugh
    simp only [wp, liftM, monadLift, MonadLift.monadLift, Traceful.run, OptionT.run]
    unfold StateT.pure
    simp only [StateT.run, Id.run_pure]
    grind

theorem Traceful.bind_wp
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {a b g}
  (ghost: g)
  (x: Traceful a) (f: a -> Traceful b)
  (post_f: b -> ProofTrace -> Prop)
  (tr: ProofTrace)
  {pre_x post_x}
  [HasGhostArgumentType x g]
  [ht: HoareTripleGhost x ghost pre_x post_x]
  (pf_tr_inv: Trace.Invariant tr)
  (pf_pre_x: pre_x tr)
  (pf_next: ∀ tr_mid x',
    post_x x' tr_mid →
    Trace.Invariant tr_mid →
    tr ≤ tr_mid → (
      WP.wp (f x') (post_f) tr_mid
    )
  )
  : WP.wp (x >>= f) (post_f) tr
  := by
    have := ht.pf
    simp_all only [WP.wp, hoareTriple, Traceful.run_bind]
    grind [Trace.le_trans]

theorem Traceful.finish_wp
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {a g}
  (ghost: g)
  (x: Traceful a)
  (post: a -> ProofTrace -> Prop)
  (tr: ProofTrace)
  {pre_x post_x}
  [HasGhostArgumentType x g]
  [ht: HoareTripleGhost x ghost pre_x post_x]
  (pf_tr_inv: Trace.Invariant tr)
  (pf_pre_x: pre_x tr)
  (pf_next: ∀ tr_mid x',
    post_x x' tr_mid →
    Trace.Invariant tr_mid →
    tr ≤ tr_mid → (
      post x' tr_mid
    )
  )
  : WP.wp x post tr
  := by
    have := ht.pf
    simp_all only [WP.wp, hoareTriple]
    grind

class HoareTriplePureGhost [ExecTraceTypes] [ProofTraceTypes] (x: a) [HasGhostArgumentType x g] (ghost: g) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: ∀ tr, pre tr → post x tr

class HoareTriplePure [ExecTraceTypes] [ProofTraceTypes] (x: a) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: ∀ tr, pre tr → post x tr

instance
  [ExecTraceTypes] [ProofTraceTypes]
  (x: a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriplePure x pre post]
  : HasGhostArgumentType x Unit
where
  dummy := ()

instance [ExecTraceTypes] [ProofTraceTypes] (x: a) (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop) [HoareTriplePure x pre post]: HoareTriplePureGhost x () pre post where
  pf := HoareTriplePure.pf

theorem apply_hoare_triple_pure
  [ExecTraceTypes] [ProofTraceTypes]
  {a g}
  (ghost: g) (x: a)
  {pre: ProofTrace → Prop} {post: a → ProofTrace → Prop}
  [HasGhostArgumentType x g]
  [ht: HoareTriplePureGhost x ghost pre post]
  (tr: ProofTrace)
  (p: pre tr)
  : post x tr
  := ht.pf tr p

instance
  [ExecTraceTypes] [ProofTraceTypes]
  (b: Bool)
  [HasGhostArgumentType b g]
  : HasGhostArgumentType (guard b: Traceful Unit) g
where
  dummy := ()

instance
  [ExecTraceTypes] [ProofTraceTypes]
  (b: Bool)
  [HasIndirectGhostMetaprogram b metaprog y]
  : HasIndirectGhostMetaprogram (guard b: Traceful Unit) metaprog y
where
  dummy := ()

instance [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] (b: Bool) (pre: ProofTrace → Prop) (post: Bool → ProofTrace → Prop) [HasGhostArgumentType b g] [ht: HoareTriplePureGhost b ghost pre post]:
  HoareTripleGhost
    (guard (b = true): Traceful Unit)
    (ghost)
    (fun tr => pre tr)
    (fun () tr => post true tr)
where
  pf := by
    have := ht.pf
    simp [hoareTriple, wp, guard]
    intro tr h_pre h_inv
    exists tr
    cases b
    · simp [Traceful.run_failure]
      grind
    · simp_all [Traceful.run_pure]
      grind

instance (priority := low) [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] (b: Prop) [Decidable b]:
  HoareTriple
    (guard b: Traceful Unit)
    (fun _ => True)
    (fun () _ => b)
where
  pf := by
    simp only [hoareTriple, wp, guard]
    intro tr h_pre h_inv
    exists tr
    by_cases b
    · simp_all [Traceful.run_pure]
      grind
    · simp_all [Traceful.run_failure]
      grind

instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  : HoareTriple
    (pure x: Traceful a)
    (fun _ => True)
    (fun res _ => res = x)
where
  pf := by
    simp only [hoareTriple, forall_const]
    intro tr h_inv
    exists tr

instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  : HoareTriple
    (OptionT.fail: Traceful a)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    simp only [hoareTriple, forall_const]
    intro tr h_inv
    exists tr

public
def appendEntry
  [ExecTraceTypes] {EntryT: Type} [ExecTraceTypes.Has EntryT]
  (entry: EntryT)
  : Traceful Nat
:=
  Traceful.mk (fun tr =>
    (some tr.length, tr.append entry)
  )

instance
  [ExecTraceTypes] [ProofTraceTypes]
  {ExecEntryT ProofEntryT: Type}
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  (entry: ExecEntryT)
  : HasGhostArgumentType (appendEntry entry) (Nat → ProofEntryT)
where
  dummy := ()

@[instance]
public
theorem appendEntry.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [SubTraceInvariant ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (execEntry: ExecEntryT) (mkProofEntry: Nat → ProofEntryT)
  : HoareTripleGhost
    (appendEntry execEntry)
    (mkProofEntry)
    (fun tr =>
      ∀ time,
      ErasableProofEntry.erase (mkProofEntry time) = execEntry ∧
      SubTraceInvariant.invariant tr (mkProofEntry time)
    )
    (fun time tr =>
      tr.at_is time (mkProofEntry time)
    )
:= by
  apply HoareTripleGhost.mk
  simp only [hoareTriple, wp, appendEntry, Traceful.run_mk]
  intro trProof h_pre h_inv
  exists trProof.append (mkProofEntry trProof.length)
  simp_all [Trace.append_erase, Trace.append_le, Trace.invariant_append, Trace.at_is_append, Trace.erase_length]

public
def getEntry
  [ExecTraceTypes] {EntryT: Type} [ExecTraceTypes.Has EntryT]
  (timestamp: Nat)
  : Traceful EntryT
:=
  Traceful.mk (fun tr =>
    let result :=
      if h: timestamp < tr.length then
        ExecTraceTypes.Has.proj (tr.at timestamp h)
      else
        none
    (result, tr)
  )

@[instance]
public
theorem getEntry.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [SubTraceInvariant ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (timestamp: Nat)
  : HoareTriple
    (getEntry timestamp: Traceful ExecEntryT)
    (fun _ => True)
    (fun entry tr =>
      exists proofEntry: ProofEntryT,
      entry = ErasableProofEntry.erase proofEntry ∧
      SubTraceInvariant.invariant (tr.prefix timestamp) proofEntry
    )
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, wp, getEntry, Traceful.run_mk]
  intro trProof h_pre h_inv
  exists trProof
  split
  · grind
  rename_i execEntry heq
  simp only [h_inv, Trace.le_refl, and_true]
  simp only [Option.dite_none_right_eq_some] at heq
  obtain ⟨ h_timestamp, heq ⟩ := heq
  cases h: (ProofTraceTypes.Has.proofProj (tr_proof'.at timestamp (by grind [Trace.erase_length])): Option ProofEntryT)
  · simp_all [ProofTraceTypes.Has.proofProj_none_eq_erase, Trace.erase_at]
  rename_i proofEntry
  exists proofEntry
  simp only [ProofTraceTypes.Has.proof_inj_proj_eq] at h
  simp only [ExecTraceTypes.Has.inj_proj_eq, Trace.erase_at, ProofTraceTypes.Has.erase_commutes, h] at heq
  constructor
  · grind
  rewrite [← TraceInvariant.Has.inv_commutes, ← h]
  apply Trace.invariant_at
  assumption

public
def getTimestamp [ExecTraceTypes]: Traceful Nat
:=
  Traceful.mk (fun tr =>
    (some tr.length, tr)
  )

@[instance]
public
theorem getTimestamp.spec [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]:
  HoareTriple
    (getTimestamp)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  simp [hoareTriple, wp, getTimestamp]
  intro tr h_inv
  exists tr

end DY

end
