module

import Init.Control.Lawful.Basic
public import Lean
public import DY.Bytes.Basic
public import DY.Trace.Basic
public import DY.Trace.Monad
public import DY.Trace.Reachability
public import DY.Trace.Invariant
public import DY.Label

namespace DY

public
class WP [ExecTraceTypes] [ProofTraceTypes] (m: Type u → Type v) where
  wp: m a → (a → ProofTrace → Prop) → (ProofTrace → Prop)

export WP (wp)

public
instance [ExecTraceTypes] [ProofTraceTypes]: WP Id where
  wp f post tr_proof :=
    post f.run tr_proof

public
instance [ExecTraceTypes] [ProofTraceTypes]: WP Err where
  wp f post tr_proof :=
    match f.run with
    | .none => True
    | .some x => post x tr_proof

public
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

@[expose]
public
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
public
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
public
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
public
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
public
class HasIndirectGhostMetaprogram {a: Sort u_1} {b: outParam (Sort u_2)} (x: a) (metaprog: outParam GhostParameterFinder) (y: outParam b) where
  dummy: Unit

public
instance [HasGhostMetaprogram x metaprog]: HasIndirectGhostMetaprogram x metaprog x
where
  dummy := ()

public
class HoareTripleGhost [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [WP m] (f: m a) [HasGhostArgumentType f g] (ghost: g) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: hoareTriple f pre post

public
class HoareTriple [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [WP m] (f: m a) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: hoareTriple f pre post

public
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

public
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

public
class WPLift
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  (m: Type u → Type v) (n : Type u → Type w)
  [MonadLift m n] [WP m] [WP n]
where
  pf {a: Type u} (x: m a) (post: a → ProofTrace → Prop) (tr: ProofTrace):
    tr.Invariant →
    wp x post tr →
    wp (liftM x: n a) post tr

public
instance
  {m: Type u → Type v} {n: Type u → Type w} [MonadLift m n]
  {a: Type u} {g: Type u_g}
  (x: m a)
  [HasGhostArgumentType x g]
  : HasGhostArgumentType (liftM x: n a) g
where
  dummy := ()

public
instance
  {m: Type u → Type v} {n: Type u → Type w} [MonadLift m n]
  {a: Type u} {b: Type z}
  (x: m a)
  (y: b)
  [HasIndirectGhostMetaprogram x metaprog y]
  : HasIndirectGhostMetaprogram (liftM x: n a) metaprog y
where
  dummy := ()

public
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

public
instance [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]: WPLift Err Traceful where
  pf := by
    simp only [wp, liftM, monadLift, MonadLift.monadLift, Traceful.run_mk, OptionT.run]
    grind

public
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

public
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

public
class HoareTriplePureGhost [ExecTraceTypes] [ProofTraceTypes] (x: a) [HasGhostArgumentType x g] (ghost: g) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: ∀ tr, pre tr → post x tr

public
class HoareTriplePure [ExecTraceTypes] [ProofTraceTypes] (x: a) (pre: outParam (ProofTrace → Prop)) (post: outParam (a → ProofTrace → Prop)) where
  pf: ∀ tr, pre tr → post x tr

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  (x: a)
  (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop)
  [HoareTriplePure x pre post]
  : HasGhostArgumentType x Unit
where
  dummy := ()

public
instance [ExecTraceTypes] [ProofTraceTypes] (x: a) (pre: ProofTrace → Prop) (post: a → ProofTrace → Prop) [HoareTriplePure x pre post]: HoareTriplePureGhost x () pre post where
  pf := HoareTriplePure.pf

public
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

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  (b: Bool)
  [HasGhostArgumentType b g]
  : HasGhostArgumentType (guard b: Traceful Unit) g
where
  dummy := ()

public
instance
  [ExecTraceTypes] [ProofTraceTypes]
  (b: Bool)
  [HasIndirectGhostMetaprogram b metaprog y]
  : HasIndirectGhostMetaprogram (guard b: Traceful Unit) metaprog y
where
  dummy := ()

public
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

public
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

public
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
    grind [Traceful.run_pure]

public
instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  : HoareTriple
    (failure: Traceful a)
    (fun _ => True)
    (fun _ _ => True)
where
  pf := by
    simp only [hoareTriple, forall_const]
    intro tr h_inv
    exists tr
    grind [Traceful.run_failure]

public
def appendEntry
  [ExecTraceTypes] {EntryT: Type} [ExecTraceTypes.Has EntryT]
  (entry: EntryT)
  : Traceful Nat
:=
  Traceful.mk (fun tr =>
    (some tr.length, ⟨ tr.append entry, by simp [Trace.append_le] ⟩ )
  )

public
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
      tr.at? time = some (mkProofEntry time)
    )
:= by
  apply HoareTripleGhost.mk
  simp only [hoareTriple, wp, appendEntry, Traceful.run_mk]
  intro trProof h_pre h_inv
  exists trProof.append (mkProofEntry trProof.length)
  simp_all [Trace.append_erase, Trace.append_le, Trace.invariant_append, Trace.at?_append, Trace.erase_length]

public
def getEntry
  [ExecTraceTypes] {EntryT: Type} [ExecTraceTypes.Has EntryT]
  (timestamp: Nat)
  : Traceful EntryT
:=
  Traceful.mk (fun tr =>
    let result := tr.at? timestamp
    (result, ⟨ tr, by grind ⟩ )
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
      ∃ proofEntry: ProofEntryT,
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
  simp only [h_inv, Trace.le_refl, and_true]
  rename_i trProof execEntry heq
  cases h: (tr_proof'.at? timestamp: Option ProofEntryT)
  · simp_all [ProofTrace.Entry.at?_eq_none_erase]
  rename_i proofEntry
  exists proofEntry
  have := ProofTrace.Entry.at?_eq_some_erase tr_proof' timestamp proofEntry h
  constructor
  · grind
  rewrite [← TraceInvariant.Has.inv_commutes]
  grind [Trace.at?_eq_some, Trace.invariant_at]

public
theorem getEntry.preservesReachability
  [ExecTraceTypes]
  {ExecEntryT: Type}
  [ExecTraceTypes.Has ExecEntryT]
  (config: ReachabilityConfig)
  (timestamp: Nat)
  : Traceful.PreservesReachability config
    (getEntry timestamp: Traceful ExecEntryT)
    (fun _ => True)
    (fun entry tr => tr.at? timestamp = some entry)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, getEntry, Traceful.run_mk]
  grind

public
def getTimestamp [ExecTraceTypes]: Traceful Nat
:=
  Traceful.mk (fun tr =>
    (some tr.length, ⟨ tr, by grind ⟩)
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
  simp [hoareTriple, wp, getTimestamp, Traceful.run_mk]
  intro tr h_inv
  exists tr

public
structure LoopInvariantAndProof'
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {α : Type} {xs : List α} {β : Type}
  (f: (a: α) → a ∈ xs → β → Traceful (ForInStep β))
where
  inv: List.Cursor xs × β → ProofTrace → Prop
  step:
    ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      HoareTriple
        (f cur (by simp [h]) b)
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨xs, [], by simp⟩, b')
        )

public
instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {α β: Type}
  (xs: List α) (init: β) (f : (a: α) → a ∈ xs → β → Traceful (ForInStep β))
  : HasGhostArgumentType
    (forIn' xs init f)
    (LoopInvariantAndProof' f)
where
  dummy := ()

@[instance]
public
theorem forIn'.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {α β: Type}
  (xs: List α) (init: β) {f : (a: α) → a ∈ xs → β → Traceful (ForInStep β)}
  (invAndProof : LoopInvariantAndProof' f)
  : HoareTripleGhost
    (forIn' xs init f)
    (invAndProof)
    (invAndProof.inv (⟨[], xs, rfl⟩, init))
    (fun b => invAndProof.inv (⟨xs, [], by simp⟩, b))
:= by
  apply HoareTripleGhost.mk
  suffices h : ∀ c,
    hoareTriple
      (forIn' (m:=Traceful) c.suffix init (fun a ha b => f a (by simp [←c.property, ha]) b))
      (invAndProof.inv (c, init))
      (fun b => invAndProof.inv (⟨xs, [], by simp⟩, b))
  from h ⟨[], xs, rfl⟩
  intro ⟨ pref, suff, h ⟩
  induction suff generalizing pref init
  · simp only [hoareTriple]
    intro tr h h_inv
    exists tr
    grind [Traceful.run_pure]
  rename_i head tail ih
  simp only [hoareTriple, List.forIn'_cons]
  intro tr h h_inv
  have := invAndProof.step pref head tail (by grind) init
  apply Traceful.bind_wp ()
  · assumption
  · assumption
  intro tr res h' h_inv h_le
  split
  · exists tr
    grind [Traceful.run_pure]
  rename_i x h
  exact ih h (pref ++ [head]) (by grind) tr (by grind) (by grind)

public
structure LoopInvariantAndProof
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {α : Type} (xs : List α) {β : Type}
  (f: (a: α) → β → Traceful (ForInStep β))
where
  inv: List.Cursor xs × β → ProofTrace → Prop
  step:
    ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      HoareTriple
        (f cur b)
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨xs, [], by simp⟩, b')
        )

public
instance
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {α β: Type}
  (xs: List α) (init: β) (f : (a: α) → β → Traceful (ForInStep β))
  : HasGhostArgumentType
    (forIn xs init f)
    (LoopInvariantAndProof xs f)
where
  dummy := ()

@[instance]
public
theorem forIn.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {α β: Type}
  (xs: List α) (init: β) {f : (a: α) → β → Traceful (ForInStep β)}
  (invAndProof: LoopInvariantAndProof xs f)
  : HoareTripleGhost
    (forIn xs init f)
    invAndProof
    (invAndProof.inv (⟨[], xs, rfl⟩, init))
    (fun b => invAndProof.inv (⟨xs, [], by simp⟩, b))
:= by
  apply HoareTripleGhost.mk
  simp only [← forIn'_eq_forIn]
  exact (forIn'.spec xs init ⟨ invAndProof.inv, invAndProof.step ⟩).pf

end DY
