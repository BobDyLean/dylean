module

import Init.Control.Lawful.Basic
public import Lean
public import DY.Trace.Basic
public import DY.Label

@[expose] public section

namespace DY

variable [BytesFunctor]

abbrev ExecutionTrace := Trace Unit
abbrev ProofTrace := Trace Label -- TODO and usage

abbrev Traceful := OptionT (StateT ExecutionTrace Id)
abbrev Err := OptionT Id

instance : MonadLift Err Traceful := {
  monadLift := fun x => StateT.pure x.run
}

def Traceful.run (x: Traceful a) (tr: ExecutionTrace): (Option a × ExecutionTrace) :=
  Id.run (StateT.run (OptionT.run x) tr)

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
  (x: a) (tr: ExecutionTrace)
  : Traceful.run (pure x) tr = (some x, tr)
  := by
    rfl

theorem Traceful.run_bind
  (x: Traceful a) (f: a → Traceful b) (tr: ExecutionTrace)
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

axiom Trace.invariant: ProofTrace -> Prop

class WP (m: Type u → Type v) where
  wp: m a → (a → ProofTrace → Prop) → (ProofTrace → Prop)

export WP (wp)

instance: WP Id where
  wp f post tr_proof :=
    post f.run tr_proof

instance: WP Err where
  wp f post tr_proof :=
    match f.run with
    | .none => True
    | .some x => post x tr_proof

instance: WP Traceful where
  wp f post tr_proof :=
    let (opt_x, tr_exec') := f.run tr_proof.erase
    ∃ tr_proof',
      (
        match opt_x with
        | .none => True
        | .some x => post x tr_proof'
      ) ∧
      Trace.invariant tr_proof' ∧
      tr_exec' = tr_proof'.erase ∧
      tr_proof ≤ tr_proof'

def hoareTriple [WP m] (f: m a) (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop): Prop :=
  ∀ tr,
    pre tr →
    Trace.invariant tr →
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

class HoareTripleGhost [WP m] (f: m a) [HasGhostArgumentType f g] (ghost: g) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: hoareTriple f pre post

class HoareTriple [WP m] (f: m a) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: hoareTriple f pre post

instance
  {m :Type u → Type v} [WP m]
  {a: Type u}
  (f: m a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriple f pre post]
  : HasGhostArgumentType f Unit
where
  dummy := ()

instance
  {m :Type u → Type v} [WP m]
  {a: Type u}
  (f: m a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriple f pre post]
  : HoareTripleGhost f () pre post
where
  pf := HoareTriple.pf

class WPLift
  (m: Type u → Type v) (n : Type u → Type w)
  [MonadLift m n] [WP m] [WP n]
where
  pf {a: Type u} (x: m a) (post: a → ProofTrace → Prop) (tr: ProofTrace):
    tr.invariant →
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

instance: WPLift Err Traceful where
  pf := by
    -- ugh
    simp only [wp, liftM, monadLift, MonadLift.monadLift, Traceful.run, OptionT.run]
    unfold StateT.pure
    simp only [StateT.run, Id.run_pure]
    grind

theorem Traceful.bind_wp
  {a b g}
  (ghost: g)
  (x: Traceful a) (f: a -> Traceful b)
  (post_f: b -> ProofTrace -> Prop)
  (tr: ProofTrace)
  {pre_x post_x}
  [HasGhostArgumentType x g]
  [ht: HoareTripleGhost x ghost pre_x post_x]
  (pf_tr_inv: Trace.invariant tr)
  (pf_pre_x: pre_x tr)
  (pf_next: ∀ tr_mid x',
    post_x x' tr_mid →
    Trace.invariant tr_mid →
    tr ≤ tr_mid → (
      WP.wp (f x') (post_f) tr_mid
    )
  )
  : WP.wp (x >>= f) (post_f) tr
  := by
    have := ht.pf
    simp_all only [WP.wp, hoareTriple, Traceful.run_bind]
    grind [Trace.trace_le_trans]

theorem Traceful.finish_wp
  {a g}
  (ghost: g)
  (x: Traceful a)
  (post: a -> ProofTrace -> Prop)
  (tr: ProofTrace)
  {pre_x post_x}
  [HasGhostArgumentType x g]
  [ht: HoareTripleGhost x ghost pre_x post_x]
  (pf_tr_inv: Trace.invariant tr)
  (pf_pre_x: pre_x tr)
  (pf_next: ∀ tr_mid x',
    post_x x' tr_mid →
    Trace.invariant tr_mid →
    tr ≤ tr_mid → (
      post x' tr_mid
    )
  )
  : WP.wp x post tr
  := by
    have := ht.pf
    simp_all only [WP.wp, hoareTriple]
    grind

class HoareTriplePureGhost (x: a) [HasGhostArgumentType x g] (ghost: g) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: ∀ tr, pre tr → post x tr

class HoareTriplePure (x: a) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: ∀ tr, pre tr → post x tr

instance
  (x: a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriplePure x pre post]
  : HasGhostArgumentType x Unit
where
  dummy := ()

instance [HoareTriplePure x pre post]: HoareTriplePureGhost x () pre post where
  pf := HoareTriplePure.pf

theorem apply_hoare_triple_pure
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
  (b: Bool)
  [HasGhostArgumentType b g]
  : HasGhostArgumentType (guard b: Traceful Unit) g
where
  dummy := ()

instance
  (b: Bool)
  [HasIndirectGhostMetaprogram b metaprog y]
  : HasIndirectGhostMetaprogram (guard b: Traceful Unit) metaprog y
where
  dummy := ()

instance (b: Bool) [HasGhostArgumentType b g] [ht: HoareTriplePureGhost b ghost pre post]:
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
    · simp [failure, Traceful.run, OptionT.fail, OptionT.mk, OptionT.run]
      grind
    · simp [pure, Traceful.run, OptionT.pure, OptionT.mk, OptionT.run]
      unfold StateT.pure
      simp [StateT.run]
      grind

end DY

end
