module

public import DY.Trace.Basic

namespace DY

@[expose]
public
def Traceful [ExecTraceTypes] (a: Type) := (trIn: ExecTrace) → Option a × { trOut: ExecTrace // trIn ≤ trOut }

public
instance [ExecTraceTypes]: Monad Traceful where
  pure x := fun tr => (some x, ⟨ tr, by grind ⟩)
  bind x f := fun tr =>
    let (xOptVal, trMid) := x tr
    match xOptVal with
    | none => (none, trMid)
    | some xVal =>
      let (optRes, trOut) := f xVal trMid.val
      (optRes, ⟨ trOut.val, by grind [Trace.le_trans] ⟩)

public
instance [ExecTraceTypes]: Alternative Traceful where
  failure := fun tr => (none, ⟨ tr, by grind ⟩)
  orElse x y := fun tr =>
    let (xOptVal, trMid) := x tr
    match xOptVal with
    | some xVal => (some xVal, trMid)
    | none =>
      let (optRes, trOut) := y () trMid.val
      (optRes, ⟨ trOut.val, by grind [Trace.le_trans] ⟩)

public
def Traceful.run [ExecTraceTypes] (x: Traceful a) (tr: ExecTrace): (Option a × { trOut: ExecTrace // tr ≤ trOut}) :=
  x tr

public
def Traceful.mk [ExecTraceTypes] {α: Type} (f: (tr: ExecTrace) → (Option α × { trOut: ExecTrace // tr ≤ trOut})): Traceful α :=
  f

@[expose, implicit_reducible]
public
def Err := OptionT Id
deriving Monad, Alternative

public
instance [ExecTraceTypes]: MonadLift Err Traceful := {
  monadLift x := Traceful.mk fun tr => (x, ⟨ tr, by grind ⟩ )
}

public
theorem Traceful.run_mk
  [ExecTraceTypes] {α: Type}
  (f: (tr: ExecTrace) → (Option α × { trOut: ExecTrace // tr ≤ trOut}))
  : Traceful.run (Traceful.mk f) = f
:= by
  rfl

public
theorem Traceful.run_pure
  [ExecTraceTypes]
  (x: a) (tr: ExecTrace)
  : Traceful.run (pure x) tr = (some x, ⟨ tr, by grind ⟩)
:= by
  rfl

public
theorem Traceful.run_bind
  [ExecTraceTypes]
  (x: Traceful a) (f: a → Traceful b) (tr: ExecTrace)
  : Traceful.run (x >>= f) tr = (
    let (opt_x, tr) := x.run tr
    match opt_x with
    | some x =>
      let (opt_y, tr) := (f x).run tr
      (opt_y, ⟨ tr.val, by grind [Trace.le_trans]⟩)
    | none => (none, tr)
  )
:= by
  simp [Traceful.run, Bind.bind]
  grind

public
theorem Traceful.run_failure
  [ExecTraceTypes]
  (tr: ExecTrace)
  : Traceful.run (failure: Traceful a) tr = (none, ⟨ tr, by grind ⟩)
:= by
  rfl

end DY

/-!
  Unfolding lemmas for downstream developments.

  The definitions above are `public` but not `@[expose]`d. Downstream proofs that
  reason about the operational semantics directly (e.g. refinement proofs) use these
  theorems instead of `import all`.
-/

public section

theorem DY.Traceful.run_eq_1 :
    ∀ {a : Type} [DY.ExecTraceTypes] (x : DY.Traceful a) (tr : DY.ExecTrace),
      x.run tr = x tr :=
  @_root_.DY.Traceful.run.eq_1

theorem DY.Traceful.mk_eq_1 :
    ∀ [DY.ExecTraceTypes] {α : Type}
      (f : (tr : DY.ExecTrace) → Option α × { trOut // tr ≤ trOut }),
      DY.Traceful.mk f = f :=
  @_root_.DY.Traceful.mk.eq_1

end
