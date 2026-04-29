module

public import Lean
import DY.Trace
public meta import DY.Meta.Utils

open Lean Elab Term Meta Tactic

namespace DY.Step

meta
def swapAppLetAux (e: Expr): TacticM (Expr × Option (Name × Expr × Expr × Bool)) := do
  match e with
  | .app fn arg =>
    let (fn', optLetBind) ← swapAppLetAux fn
    match optLetBind with
    | .some _ => pure (.app fn' arg, optLetBind)
    | .none =>
      let (arg', optLetBind) ← swapAppLetAux arg
      match optLetBind with
      | .some _ => pure (.app fn arg', optLetBind)
      | .none => pure (e, none)
  | .letE declName type value body nondep =>
    pure (body, some (declName, type, value, nondep))
  | .mdata data expr =>
    let (expr, optLetBind) ← swapAppLetAux expr
    pure (.mdata data expr, optLetBind)
  | _ => pure (e, none)

/-
  Turn an expression
    `f (let x := y; ...) ...`
  into
    `let x := y; f ... ...`
  The transformed expression is definitionally equal to the initial expression
  (via inlining of the let binding)
-/
meta
def swapAppLet (e: Expr): TacticM Expr := do
  let (body, optLetBind) ← swapAppLetAux e
  let .some (declName, type, value, nondep) := optLetBind
    | throwError "swap_app_let: no let :("
  pure (.letE declName type value body nondep)

/-
  Introduce a `let` from wp.
  From a goal
  ... |- wp (let x := y; z) ...
  creates the goal
  ...; x := y |- wp z ...
-/
public meta
def stepIntro (mvar: MVarId): TacticM (FVarId × MVarId) :=
  mvar.withContext do
  let goal ← mvar.getType
  let goal ← goal.sanitize
  let newGoal ← swapAppLet goal
  unless ← isDefEq goal newGoal do
    throwError "swap_app_let: internal bug, {goal} and {newGoal} are not definitionally equal"
  let mvar ← mvar.replaceTargetDefEq newGoal
  mvar.intro1P

elab (name := step_intro) "step_intro" : tactic => do
  replaceMainGoal ([(← stepIntro (← getMainGoal)).snd])

namespace Test

def f (n1 n2 n3: Nat): Prop := n1 + n2 = n3

example:
  f
    (let x := 1; x+x)
    (let y := 1; y+y)
    (let z := 1; z+3)
  := by
    step_intro
    step_intro
    grind [f]

end Test

structure HoistInfo where
  name: Name
  type: Expr
  info: BinderInfo
deriving Inhabited

/- when `e` is a function,
  returns the name, type and binder info
  of its arguments
-/
meta
def getArgsInfo
  (e: Expr)
  (args: Array Expr)
  : MetaM (Array HoistInfo)
  := do
    let ty ← inferType e
    pure (process ty #[])
where
  process (ty: Expr) (acc: Array HoistInfo): Array HoistInfo :=
    match ty with
    | .forallE binderName binderType body binderInfo =>
      -- in case there is a dependent arrow, binderType will contain loose bvars,
      -- which we instantiate here
      process body (acc.push ⟨ binderName, binderType.instantiateRev (args.take acc.size), binderInfo ⟩ )
    | .mdata _ body =>
      process body acc
    | _ => acc

/- Given an expression `f x1 ... xn`,
  replace the `xi` that satisfy the predicate `p`
  by loose bvars,
  and return the expressions to introduce (e.g. via let or lambda)
-/
meta
def hoistArgumentsAux
  (p: Expr → HoistInfo → Bool) (e: Expr)
  : MetaM (Expr × List (Expr × HoistInfo))
  := do
    let (fn, args) := e.withApp Prod.mk
    let argsInfo ← getArgsInfo fn args
    guard (args.size = argsInfo.size)
    let (_, args, hoistedArgs) := (args.zip argsInfo).foldr (fun (arg, info) (n, args, hoistedArgs) =>
      if p arg info then
        (n+1, (.bvar n)::args, (arg, info)::hoistedArgs)
      else
        (n, arg::args, hoistedArgs)
    ) (0, [], [])
    pure (args.foldl mkApp fn, hoistedArgs)

meta
def addLet
  (pre: String) (arg: (Expr × HoistInfo)) (e: Expr)
  : Expr
  :=
    let (arg, argInfo) := arg
    let name := prepend pre argInfo.name
    .letE name argInfo.type arg e true

meta
def addLets
  (pre: String) (args: List (Expr × HoistInfo)) (e: Expr)
  : Expr
  :=
    args.foldr (addLet pre) e

/-
  Given an expression
    (f x1 ... xn) >>= g
  or
    let x := f x1 ... xn; g
  hoist the `xi` that satisfy the predicate `p`
  into let-bindings
-/
meta
def hoistArguments
  (p: Expr → HoistInfo → Bool) (e: Expr)
  : MetaM (Option Expr)
  := do
    match e.consumeMData with
    | .letE declName type value body nondep =>
      let (value, hoisted) ← hoistArgumentsAux p value
      if hoisted.isEmpty then
        return none
      let pre := declName.getString! ++ "_"
      pure (addLets pre hoisted (.letE declName type value body nondep))
    | .app _ _ =>
      -- this handles Bind.bind,
      -- but what if the instruction is simply the last one
      -- (hence is an .app but not a bind?)
      let (fn, args) := e.withApp Prod.mk
      unless fn.constName = ``Bind.bind && args.size = 6 do
        return none
      let (value, hoisted) ← hoistArgumentsAux p args[4]!
      let args := args.set! 4 value
      let pre :=
        match args[5]! with
        | .lam binderName _ _ _ =>
          if binderName.isStr then
            binderName.getString! ++ "_"
          else
            ""
        | _ => ""
      pure (addLets pre hoisted (args.foldl mkApp fn))
    | _ => pure none

meta
def isExplicitComplexExpr
  (e: Expr) (info: HoistInfo)
  : Bool
  :=
    let isComplex := ¬ (e.isFVar || e.isBVar)
    let isExplicit := info.info.isExplicit
    -- could also check if `info.type` is `Bytes` here
    isComplex && isExplicit

/-
  When the goal is
    ... |- wp x ...
  Apply `hoistArguments` inside `x`
-/
meta
def hoistArgumentsInWpAux
  (e: Expr)
  : MetaM (Option Expr)
  := do
    let (fn, args) := e.withApp Prod.mk
    unless fn.constName = ``DY.wp && args.size = 8 do
      return none
    match ← hoistArguments isExplicitComplexExpr args[5]! with
    | .some arg1 =>
      let args := args.set! 5 arg1
      pure (some (mkAppN fn args))
    | .none => pure none

meta
def hoist (mvar: MVarId): TacticM MVarId :=
  mvar.withContext do
  let goal ← mvar.getType
  let goal ← goal.sanitize
  let some newGoal ← hoistArgumentsInWpAux goal
    | pure mvar
  unless ← isDefEq goal newGoal do
    throwError "hoist: internal bug, {goal} and {newGoal} are not definitionally equal"
  mvar.replaceTargetDefEq newGoal

elab "hoist" : tactic => do
  replaceMainGoal ([← hoist (← getMainGoal)])

namespace Test
  variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  def g (foo: Bytes) (bar: Bytes) := foo
  def send_message (b: Bytes): Traceful Nat := sorry

  example:
    wp (
      have b := g (g (g b1 b2) (g b3 b4)) (g (g b5 b6) (g b7 b8))
      send_message b
    )
    (fun _ _ => True) tr
  := by
    hoist
    hoist
    step_intro
    step_intro
    step_intro
    hoist
    step_intro
    step_intro
    step_intro
    sorry

  example:
    wp (
      do
        let i ← send_message (g (g (g b1 b2) (g b3 b4)) (g (g b5 b6) (g b7 b8)));
        pure i
    )
    (fun _ _ => True) tr
  := by
    hoist
    hoist
    hoist
    step_intro
    step_intro
    step_intro
    hoist
    step_intro
    step_intro
    step_intro
    step_intro
    sorry

end Test

end DY.Step
