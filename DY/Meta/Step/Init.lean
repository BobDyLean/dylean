module

import Lean
import DY.Meta.Step.Trace
public meta import DY.Meta.Step.Options
public meta import DY.Meta.LetUtils
import DY.Trace
import DY.Meta.GrindAttribute
public meta import DY.Trace.Grind

open Lean Elab Term Meta Tactic Sym Grind

namespace DY.Step

inductive StepSpecTheorem where
  | wp
    (func: Expr)
    (post: Expr)
    (tr: Expr)
  | hoareTriple
    (func: Expr)
    (pre: Expr)
    (post: Expr)
  | hoareTripleTC
  | hoareTripleGhostTC
deriving Repr

meta
def preservesInvariantTelescope
  (type: Expr)
  : MetaM ((Array (MVarId × BinderInfo)) × StepSpecTheorem)
  := do
    withTraceNode `Step (fun _ => pure m!"Analyze the goal") do
    -- type = ∀ b1 ... bn, preserves_invariant(_on) f ...
    let type ← type.sanitize
    trace[Step] "Theorem: {type}"
    let (xs, xs_bi, type) ← forallMetaTelescope type
    let type ← type.sanitize
    let xs_and_bi := Array.zip (Array.map (·.mvarId!) xs) xs_bi
    -- type = preserves_invariant(_on) f ...
    trace[Step] "Theorem after forall intro: {type}"
    let (fName, args) := type.getAppFnArgs
    trace[Step] "function name: {fName}, arguments: {args}"
    if fName = ``DY.hoareTriple then
      guard (args.size = 9)
      pure (xs_and_bi, StepSpecTheorem.hoareTriple args[6]! args[7]! args[8]!)
    else if fName = ``DY.wp then
      guard (args.size = 8)
      pure (xs_and_bi, StepSpecTheorem.wp args[5]! args[6]! args[7]!)
    else if fName = ``DY.HoareTriple then
      pure (xs_and_bi, StepSpecTheorem.hoareTripleTC)
    else
      throwError "not a constant"

inductive SpecType where
  | let_binding (x:Expr) (xName:Name)
  | bind (x:Expr) (f:Expr) (xName:Name)
  | final (x:Expr)

meta
def specTypeTelescope
  (type: Expr)
  : MetaM SpecType
  := do
    withTraceNode `Step (fun _ => pure m!"Analyze the function to prove") do
    let type ← type.sanitize
    match type with
    | .letE declName _type value _body _nondep =>
      pure (.let_binding value declName)
    | .app _ _ =>
      let (funcName, args) := type.getAppFnArgs
      trace[Step] "specTypeTelescope: got {funcName} and {args}"
      if funcName = ``Bind.bind then
        guard (args.size = 6)
        let x := args[4]!
        let f := args[5]!
        let xName ←
          match f with
          | .lam xName _ _ _ => pure xName
          | _ => throwError "bind's f is not a lambda?"
        pure (.bind x f xName)
      else
        pure (.final type)
        --throwError "unknown case"
    | _ =>
      pure (.final type)

public
syntax stepArgs := ("with" " ⟨ " term,* " ⟩")? ("by" tacticSeq)?

structure StepArgs where
  xGhostTerm : Expr
  xGhostTermProvided: Bool
  preTactic: Option Syntax

meta
def parseStepArgs (args: TSyntax ``DY.Step.stepArgs): TacticM StepArgs
  :=
  withMainContext do
  trace[Step] "Step arguments: {args.raw}"
  match args with
  | `(stepArgs| $[with ⟨ $xGhosts,* ⟩ ]? $[by $disch]? ) =>
    let xGhostTerms ←
      match xGhosts with
      | none => pure #[]
      | some xGhosts =>
        xGhosts.getElems.mapM (fun xGhost =>
          Tactic.elabTerm xGhost none
        )
    pure {
      xGhostTerm := ← makeTuple xGhostTerms
      xGhostTermProvided := xGhosts.isSome
      preTactic := disch
    }
  | _ => throwUnsupportedSyntax

meta
def solvePrecondition
  (args: StepArgs)
  (pre: MVarId)
  : TacticM Unit
  := do
    match args.preTactic with
    | some tac =>
      let currentGoals ← getGoals
      setGoals [pre]
      evalTactic tac
      unless (← getGoals).isEmpty do
        throwError "unsolved goal in precondition proof"
      setGoals currentGoals
    | none =>
      let _ ← grind pre {} false #[] none
      pure ()

meta
def isAnd (e : Expr) : Bool :=
  let (name, args) := e.getAppFnArgs
  name = `And ∧ args.size = 2

meta partial
def splitAndAt (goal: MVarId) (fv: FVarId) (name: Name) (i: Nat := 0): TacticM (MVarId) :=
  goal.withContext do
  let fvTy ← (← fv.getType).sanitize
  if isAnd fvTy then
    let newGoals ← goal.cases fv
    match newGoals.toList with
    | [newGoal] =>
      guard (newGoal.fields.size = 2)
      let [fv1, fv2] := newGoal.fields.toList.map Expr.fvarId!
        | throwError "unreachable: And must have 2 arguments"
      let goal := newGoal.mvarId
      let hypName ← mkFreshBinderNameForTactic name
      goal.modifyLCtx (fun lctx => lctx.setUserName fv1 hypName)
      let goal ← splitAndAt goal fv2 name (i+1)
      pure goal
    | _ => throwError "unreachable: And must have 1 constructor"
  else
    let hypName ← mkFreshBinderNameForTactic name
    goal.modifyLCtx (fun lctx => lctx.setUserName fv hypName)
    pure goal

meta
def clearFvIfTrue (goal: MVarId) (fv: FVarId): MetaM MVarId :=
  goal.withContext do
  if ← isDefEq (← fv.getType) (.const ``True []) then
    goal.clear fv
  else
    pure goal

meta
def introAndMassagePostX
  (xFv: FVarId)
  (goal: MVarId)
  : TacticM MVarId
:= do
  let (postXFv, goal) ← goal.intro1
  goal.withContext do
  -- TODO: run a pass of simplification on post_x (e.g. iota reduction etc)
  let goal ← do
    if ← isDefEq (.fvar xFv) (.const ``Unit.unit []) then
      try
        goal.clear xFv
      catch _ =>
        pure goal -- silently fail
    else
      pure goal
  let goal ← do
    if ← isDefEq (← postXFv.getType) (.const ``True []) then
      goal.clear postXFv
    else
      splitAndAt goal postXFv (prepend "h_" (← xFv.getUserName))
  pure goal

-- Cannot mark it `reducible`
-- because the monotonization pass using GrindM
-- unfolds every reducible definition.
@[expose, grind, simp]
public
def nonMono (α : Sort u) : Sort u := α

public
theorem makeNonMono {p: Prop} (h: p): Step.nonMono p := h

syntax (name := make_non_monotone) "mark_non_monotone " ident : tactic

macro_rules
  | `(tactic| mark_non_monotone $t) =>
    `(tactic|
      replace $t := DY.Step.makeNonMono $t
    )

-- Revert every fvar starting from `fvFrom` except the one satisfying `p`
-- (adapted from Lean.MVarId.revertAll)
meta
def revertAllStartingFromExcept (mvarId : MVarId) (fvFrom: FVarId) (p: FVarId → MetaM Bool): MetaM (MVarId × Nat) := mvarId.withContext do
  mvarId.checkNotAssigned `revertAllStartingFromExcept
  let mut toRevert := #[]
  let mut beforeRevert := true
  for fvarId in (← getLCtx).getFVarIds do
    unless beforeRevert ∨ (← p fvarId) ∨ (← fvarId.getDecl).isAuxDecl do
      toRevert := toRevert.push fvarId
    if fvarId == fvFrom then
      beforeRevert := false
  mvarId.setKind .natural
  let (_, mvarId) ← mvarId.revert toRevert
    (preserveOrder := true)
    (clearAuxDeclsInsteadOfRevert := true)
  return (mvarId, toRevert.size)

-- adapted from Lean.MVarId.assert
meta
def myAssert (goal: Goal) (name: Name) (type: Expr): SymM (Goal × Goal) := do
  let mvarId := goal.mvarId
  let (valMvarId, mvarId) ← mvarId.withContext do
    mvarId.checkNotAssigned `myAssert
    let tag    ← mvarId.getTag
    let target ← mvarId.getType
    let newType := Lean.mkForall name BinderInfo.default type target
    let valMVar ← mkFreshExprSyntheticOpaqueMVar type
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag
    mvarId.assign (mkApp newMVar valMVar)
    return (valMVar.mvarId!, newMVar.mvarId!)
  pure ({ goal with mvarId := valMvarId }, { goal with mvarId })

meta
def getFirstBinderName (goal: Goal): SymM Name :=
  goal.withContext do
  let type := ← (← goal.mvarId.getType).sanitize
  match type with
  | .forallE name _ _ _ => pure name
  | .letE name _ _ _ _ => pure name
  | _ => throwError "cannot get name {type}"

/--
  Apply monotonicity lemmas on the context,
  while preserving the order assumptions appear in.
  We could do this with Lean.MVarId.replace,
  however this function may trash fvar ids
  (because it reverts and re-introduces assumptions),
  hence give a map from old to new fvar ids,
  which is a bit cumbersome,
  especially because we want to replace many of the assumptions.
  Instead, we do something similar to Lean.MVarId.replace ourselves:
  revert all assumptions (except the core ones about traces such as trace invariant etc)
  and re-introduce them one by one, applying monotonicity lemmas if needed.
  We prove the monotonized hypothesis using `grind`,
  via the grind-set `grind_later`.
  Because the context only grows, we use SymM,
  which allows to use incremental internalization and e-matching in grind.
-/
meta
def monotonizeContext
  (trOldFv trMidFv trInvOldFv trInvFv trGrowsFv: FVarId)
  (goal: MVarId)
  : TacticM (MVarId × Array FVarId × Array (FVarId × Name))
:= do
  withTraceNode `Step (fun _ => pure m!"Monotonize the next goal") do

  -- Revert all hypotheses in the context.
  -- There are some hypotheses we don't want to revert,
  -- such as implicit types or typeclass instances.
  -- We use the following heuristic:
  -- we assume these hypothesis we don't want to revert happen *before* the old trace.
  -- Therefore, we revert every hypothesis happening *after* the old trace,
  -- *except* for some specific hypothesis
  -- (i.e. old/new trace, old/new trace invariant, relation between traces).
  let (goal, nHyp) ← revertAllStartingFromExcept goal trOldFv (fun fvar => do
    pure (
      fvar == trOldFv ∨
      fvar == trMidFv ∨
      fvar == trInvOldFv ∨
      fvar == trInvFv ∨
      fvar == trGrowsFv
    )
  )
  trace[Step] "reverted goal: {← goal.getType}"

  -- Sanity check: we didn't trash the fvars we obtained earlier
  trace[Step] "checking fvars are still in local context"
  do
    let lctx ← goal.withContext getLCtx
    guard (lctx.contains trOldFv)
    guard (lctx.contains trMidFv)
    guard (lctx.contains trInvOldFv)
    guard (lctx.contains trInvFv)
    guard (lctx.contains trGrowsFv)

  let admitProofs: Bool ← do
    let opts ← getOptions
    pure (opts.get step.admitMono.name step.admitMono.defValue)

  let config: Grind.Config := {
    -- Disable extensionality
    ext := false
    extAll := false
    etaStruct := false
    funext := false

    -- Disable all solver modules
    ring := false
    linarith := false
    lia := false
    ac := false
    order := false

    matchEqs := true, -- to reduce matches
    -- Splitting
    splits := 1, -- useful to "case split" on ∃
    splitMatch := false,
    splitIte := false,
    splitIndPred := false,
    splitImp := false,

    -- We need a high ematch number
    -- because we run a round of ematching each time we introduce an hypothesis.
    -- Roughly, the value we put in `ematch`
    -- corresponds to the context size we can monotize.
    ematch := 10000,
    -- hot-take: low generation limit is for cowards who don't trust their grind patterns
    gen := 1000,
  }
  -- params emulate: grind only [grind_later]
  let params ← mkParams config #[DY.grindLaterExt.getState (← Lean.getEnv)]

  -- Introduce each assumption one by one,
  -- and register old assumptions that were monotonized
  -- to clear them afterward.
  -- We don't clear them on the fly,
  -- as a old assumption (e.g. bytes_invariant)
  -- might be useful to monotonize other assumptions (e.g. involving get_label).
  -- We also store the old name of hypthoses to rename them later,
  -- because GrindM does not offer a function similar to `Lean.MVarId.intro1P` to preserve the name.
  GrindM.run (params := params) <| do
    let mut goal ← mkGoal goal
    goal ← goal.internalizeAll
    let mut monotonizedFv := #[]
    let mut fvRename := #[]
    trace[Step] "now processing {nHyp} hypothesis"
    for _ in [0:nHyp] do
      trace[Step] "intro hypothesis"
      -- user name is hygienized by goal.introN, store it for future renaming
      let hypUserName ← getFirstBinderName goal
      let .goal #[hypFv] newGoal ← goal.introN 1 | failure
      goal := newGoal
      unless admitProofs do
        goal ← goal.internalize 1

      -- incremental e-matching
      unless admitProofs do
        goal ← do
          let step := Lean.Meta.Grind.Action.instantiate
          let action := Lean.Meta.Grind.Action.assertAll >> step.loop 10000
          match ← action.run goal with
          | .closed _ => throwError "internal error: closed goal??"
          | .stuck [newGoal] => pure newGoal
          | .stuck _ => throwError "internal error: more than one goal?"

      let isNonMonotonic ← goal.withContext do
        let ty ← hypFv.getType
        let ty ← ty.sanitize
        let (name, _) := ty.getAppFnArgs
        pure (name = ``Step.nonMono: Bool)

      let dependsOnOldTrace: Bool ←
        goal.withContext do
        localDeclDependsOn (← hypFv.getDecl) trOldFv

      goal.withContext do trace[Step] "introduced: {hypUserName} of type {← hypFv.getType} (depends on old trace: {dependsOnOldTrace})"
      if isNonMonotonic then
        monotonizedFv := monotonizedFv.push hypFv -- clear this hypothesis afterward
      else if dependsOnOldTrace then
        -- Some assumptions depend on the trace but shouldn't me monotonized
        -- e.g. trace invariant, etc
        -- However, note they were not reverted,
        -- hence everything we introduce needs monotonizing.
        trace[Step] "depends on trace, monotonizing"
        let (newHyp, newGoal) ← goal.withContext do
          let oldHypType ← hypFv.getType
          let newHypType := oldHypType.replaceFVarId trOldFv (mkFVar trMidFv)
          trace[Step] "new hypothesis {oldHypType} to {newHypType}"
          myAssert goal hypUserName newHypType
        goal := newGoal

        trace[Step] "grinding"
        if admitProofs then
          newHyp.admit
        else
          match ← newHyp.grind with
          | .closed => pure ()
          | .failed newGoal =>
            -- TODO: could open a new goal with it, to allow for easier debugging in interactive mode?
            goal.withContext do throwError "cannot monotonize {← hypFv.getType}.\n grind failure: {← goalToMessageData newGoal config}"
        trace[Step] "intro new hypothesis"
        let .goal _ newGoal ← goal.introN 1 | failure
        goal := newGoal
        unless admitProofs do
          goal ← goal.internalize 1
        monotonizedFv := monotonizedFv.push hypFv
      else
        fvRename := fvRename.push (hypFv, hypUserName)

    return (goal.mvarId, monotonizedFv, fvRename)

structure EvalStepConfig where
  theoremName: Name
  nbArgs: Nat
  nbUnifiedArgs: Nat
  ghostPosition: Nat
  hasGhostPosition: Nat
  xSpecTheoremPosition: Nat
  trInvPosition: Nat
  preconditionPosition: Nat
  nextPosition: Nat
  xName: Name

/--
  Massage the next goal:
  - introduce the ∀ and hypothesis in the context
    (and use the name used in the specification)
  - split the ∧ in postcondition
  - update the context by appling monotonicity lemmas
  - clear old traces and old hypotheses (trace invariant etc)
-/

meta
def massageNextGoal
  (conf: EvalStepConfig)
  (goal: MVarId)
  : TacticM MVarId
  := do
    goal.withContext do
    withTraceNode `Step (fun _ => pure m!"Massage the next goal") do

    -- Introduce variables and hypothesis
    let (_trMidFv, goal) ← goal.intro1
    let (xFv, goal) ← goal.intro conf.xName
    -- we will not rely on the fvar above because
    -- `introAndMassagePostX` might trash them
    let goal ← introAndMassagePostX xFv goal

    let (trInvFv, goal) ← goal.intro1
    let (trGrowsFv, goal) ← goal.intro1
    goal.withContext do

    -- get old and mid trace FVarId
    -- how: unify ?tr_old ≤ ?tr_mid with the hypthesis we introduced
    let (trOldFv, trMidFv) ← do
      let oldTraceMVarId ← mkFreshExprMVar (← mkAppOptM ``DY.ProofTrace #[none, none])
      let midTraceMVarId ← mkFreshExprMVar (← mkAppOptM ``DY.ProofTrace #[none, none])
      let trLeToUnify ← mkAppOptM ``LE.le #[none, none, oldTraceMVarId, midTraceMVarId]
      trace[Step] "finding old trace fvarid by unifying {trLeToUnify} and {(← trGrowsFv.getType)}"
      unless (← isDefEq trLeToUnify (← trGrowsFv.getType)) do
        throwError "cannot unify {trLeToUnify} and {(← trGrowsFv.getType)}"
      let oldTraceExpr ← instantiateMVars oldTraceMVarId
      unless oldTraceExpr.isFVar do
        throwError "old trace is not an fvar: {oldTraceExpr}"
      let midTraceExpr ← instantiateMVars midTraceMVarId
      unless midTraceExpr.isFVar do
        throwError "mid trace is not an fvar: {midTraceExpr}"
      pure (oldTraceExpr.fvarId!, midTraceExpr.fvarId!)
    trace[Step] "old trace is {mkFVar trOldFv}"
    trace[Step] "mid trace is {mkFVar trMidFv}"

    -- get trace invariant for old trace
    -- how: unify Trace.invariant tr_old with an assumption
    let trInvOldFv ← do
      let trInvOldType ← mkAppOptM ``DY.Trace.Invariant #[none, none, none, mkFVar trOldFv]
      let trInvOldMVarId ← mkFreshExprMVar trInvOldType
      trace[Step] "finding in assumptions {trInvOldType}"
      trInvOldMVarId.mvarId!.assumption
      let trInvExpr ← instantiateMVars trInvOldMVarId
      unless trInvExpr.isFVar do
        throwError "old trace invariant is not an fvar: {trInvExpr}"
      pure trInvExpr.fvarId!

    -- monotonize context
    let (goal, monotonizedFv, fvRename) ← monotonizeContext trOldFv trMidFv trInvOldFv trInvFv trGrowsFv goal

    -- Rename the new traces with the names of the old traces
    goal.withContext do
    let fvRename := fvRename.push (trMidFv, ← trOldFv.getUserName)
    let fvRename := fvRename.push (trInvFv, ← trInvOldFv.getUserName)
    goal.modifyLCtx (fun lctx =>
      fvRename.foldl (fun lctx (fv, name) =>
        lctx.setUserName fv name
      ) lctx
    )

    let oldTraceFv := #[
      trInvOldFv,
      trGrowsFv,
      trOldFv, -- cleared after hypothesis that depend on it
    ]

    -- Clear assumptions that were monotonized + old trace assumptions
    let mut goal := goal
    for fv in monotonizedFv ++ oldTraceFv do
      goal ← goal.clear fv

    pure goal

meta
def assignGhostParameterAux
  (args: StepArgs)
  (ghostMVarId: MVarId)
  : MetaM Unit
  := do
    let expectedGhostType ← ghostMVarId.getType
    let gotGhostType ← inferType args.xGhostTerm
    -- In addition to provide a nice error message,
    -- this check can also instantiate metavariables appearing in `gotGhostType`
    unless (← isDefEq expectedGhostType gotGhostType) do
      throwError "Ghost parameter has type {gotGhostType}, expected type {expectedGhostType}.\nHint: use `step ... with ⟨ ... ⟩`"
    ghostMVarId.safeAssign args.xGhostTerm

/--
  If no ghost parameter was provided,
  try to use a user-provided meta-program
  to obtain this ghost parameter
-/
meta
def assignGhostParameter
  (args: StepArgs)
  (tcMVarId: MVarId) (ghostMVarId: MVarId)
  : MetaM Unit
  :=
  withTraceNode `Step (fun _ => pure m!"Assign ghost parameter") do
    tcMVarId.assignTypeclassInstance
    trace[Step] "ghost expression is {args.xGhostTerm} and was {if args.xGhostTermProvided then "" else "not "}provided"
    if args.xGhostTermProvided then
      assignGhostParameterAux args ghostMVarId
    else
      -- tcType = @HasGhostArgumentType a x g
      let tcType ← (← tcMVarId.getType).sanitize
      let (_, tcArgs) := tcType.getAppFnArgs
      guard (tcArgs.size = 3)
      let u_1 ← mkFreshLevelMVar
      let u_2 ← mkFreshLevelMVar
      let tcMetaprogExprForall := Expr.const ``DY.HasIndirectGhostMetaprogram [u_1, u_2]
      let tcMetaprogTypeForall ← inferType tcMetaprogExprForall
      let (tcMetaprogMVars, _, _) ← forallMetaTelescope tcMetaprogTypeForall
      let tcMetaprogExpr := mkAppN tcMetaprogExprForall tcMetaprogMVars
      let tcMetaprogMVars := tcMetaprogMVars.map (·.mvarId!)
      guard (tcMetaprogMVars.size = 5)
      tcMetaprogMVars[0]!.safeAssign tcArgs[0]!
      tcMetaprogMVars[2]!.safeAssign tcArgs[1]!
      let metaTcType := tcMetaprogExpr
      trace[Step] "trying to synthetize typeclass {metaTcType}"
      match ← trySynthInstance metaTcType with
      | .some metaTcExpr =>
        trace[Step] "found {metaTcExpr}"
        let metaprog ← (Expr.mvar tcMetaprogMVars[3]!).sanitize
        let expr ← (Expr.mvar tcMetaprogMVars[4]!).sanitize
        trace[Step] "got {metaprog} and expression {expr}"
        let .const metaprogName _ := metaprog
          | throwError "Found ghost metaprogram {metaprog}, but it is not a top-level name"
        trace[Step] "name is {metaprogName}"
        let metaprog ← unsafe evalConstCheck GhostParameterFinder ``GhostParameterFinder metaprogName
        metaprog.findGhost ghostMVarId expr
        unless ← ghostMVarId.isAssigned do
          throwError "Ghost metaprogram {metaprogName} did not assign ghost parameter"
        trace[Step] "Ghost metaprogram obtained {Expr.mvar ghostMVarId}"
      | _ =>
        trace[Step] "did not find instance"
        assignGhostParameterAux args ghostMVarId

/--
  Apply a theorem about `preserves_invariant_on` on the goal.
  The function is commented with `bind_preserves_invariant_on` in mind,
  but works similarly for other similar theorems
  (as parametrized by `EvalStepConfig`)
-/
meta
def evalStepAux
  (args: StepArgs)
  (conf: EvalStepConfig)
  : TacticM Unit
  := do
    withMainContext do
    withTraceNode `Step (fun _ => pure m!"Apply step") do
      -- bindTheoremExprForall = bind_preserves_invariant_on
      let bindTheoremExprForall ← Term.mkConst conf.theoremName
      -- bindTheoremTypeForall = ∀ ghost x f ..., preserves_invariant_on (x >>= f) ...
      let bindTheoremTypeForall ← inferType bindTheoremExprForall
      -- bindTheoremType = preserves_invariant_on (x >>= f) ...
      let (bindMVars, _, bindTheoremType) ← forallMetaTelescope bindTheoremTypeForall
      -- bindTheoremExpr = bind_preserves_invariant_on ?ghost ?x ?f ?...
      let bindTheoremExpr := mkAppN bindTheoremExprForall bindMVars
      let bindMVars := bindMVars.map (·.mvarId!)

      -- step 1: assign the goal to bindTheoremExpr
      -- this will unify its type with the goal (thanks to safeAssign)
      -- hence will instantiate a bunch of metavariables of bindMVars
      trace[Step] "Step 1: unify goal with the step theorem"
      trace[Step] "step theorem before unification {bindTheoremType}"
      let goalMVarId ← getMainGoal
      goalMVarId.safeAssign bindTheoremExpr
      let bindTheoremType ← instantiateMVars bindTheoremType
      trace[Step] "step theorem after unification {bindTheoremType}"

      -- step 2: instantiate the ghost parameter
      trace[Step] "Step 2: assign ghost parameter {args.xGhostTerm}"
      assignGhostParameter args bindMVars[conf.hasGhostPosition]! bindMVars[conf.ghostPosition]!

      -- step 3: assign the specification for x via typeclass synthesis
      bindMVars[conf.xSpecTheoremPosition]!.assignTypeclassInstance
      -- sanity checks
      guard (← bindMVars[conf.xSpecTheoremPosition-2]!.isAssigned) -- pre_x
      guard (← bindMVars[conf.xSpecTheoremPosition-1]!.isAssigned) -- post_x
      guard (← bindMVars[conf.xSpecTheoremPosition]!.isAssigned) -- HoareTriple typeclass (we just assigned it)

      -- trace invariant is in the assumptions
      bindMVars[conf.trInvPosition]!.assumption --pf_tr_inv

      let pfPreXMVar := bindMVars[conf.preconditionPosition]!
      let pfNextMVar := bindMVars[conf.nextPosition]!

      -- step 4: solve precondition
      solvePrecondition args pfPreXMVar
      guard (← pfPreXMVar.isAssigned)

      -- step 5: massage the next goal
      let pfNextMVar ← massageNextGoal conf pfNextMVar

      -- sanity check that all of the metavariable were correctly assigned
      guard (bindMVars.size = conf.nbArgs) -- sanity check
      for i in [0:conf.nbUnifiedArgs] do
        guard (← bindMVars[i]!.isAssigned)

      -- step 6: update goal list
      let bindTheoremGoals := [pfNextMVar]
      let goals ← getUnsolvedGoals
      setGoals (bindTheoremGoals ++ goals)

meta
def evalStepBind
  (args: StepArgs)
  (xName: Name)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := ``DY.Traceful.bind_wp
      nbArgs := 18
      nbUnifiedArgs := 17
      ghostPosition := 6,
      hasGhostPosition := 13
      xSpecTheoremPosition := 14
      trInvPosition := 15
      preconditionPosition := 16
      nextPosition := 17
      xName
    }

meta
def evalStepFinal
  (args: StepArgs)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := ``DY.Traceful.finish_wp
      nbArgs := 16
      nbUnifiedArgs := 15
      ghostPosition := 5
      hasGhostPosition := 11
      xSpecTheoremPosition := 12
      trInvPosition := 13
      preconditionPosition := 14
      nextPosition := 15
      xName := `x
    }

meta
def applyLetTheorem (args: StepArgs) (goal: MVarId) (letFv: FVarId): TacticM Unit :=
  goal.withContext do
  withTraceNode `Step (fun _ => pure m!"Apply let theorem") do
    -- applyTheoremExprForall = apply_hoare_triple_pure
    let applyTheoremExprForall ← Term.mkConst ``DY.apply_hoare_triple_pure
    -- applyTheoremTypeForall = ∀ ghost x ..., post x tr
    let applyTheoremTypeForall ← inferType applyTheoremExprForall
    -- applyTheoremType = post x tr
    let (applyMVars, _, applyTheoremType) ← forallMetaTelescope applyTheoremTypeForall
    -- applyTheoremExpr = apply_hoare_triple_pure ?ghost ?x ?...
    let applyTheoremExpr := mkAppN applyTheoremExprForall applyMVars
    let applyMVars := applyMVars.map (·.mvarId!)

    -- x
    applyMVars[5]!.safeAssign (.fvar letFv)
    -- ghost things
    assignGhostParameter args applyMVars[8]! applyMVars[4]!
    -- HoareTriplePureGhost instance
    applyMVars[9]!.assignTypeclassInstance
    -- tr
    applyMVars[10]!.assumption -- "I am feeling lucky" (works if there is only one `ProofTrace` in the local context)

    let pfPreMVar := applyMVars[11]!
    solvePrecondition args pfPreMVar
    guard (← pfPreMVar.isAssigned)

    -- sanity check
    guard (applyMVars.size = 12);
    for i in [0:12] do
      guard (← applyMVars[i]!.isAssigned)

    trace[Step] "using theorem {applyTheoremExpr} of type {applyTheoremType}"

    let goal ← goal.assert .anonymous applyTheoremType applyTheoremExpr
    let goal ← introAndMassagePostX letFv goal

    let goals ← getUnsolvedGoals
    setGoals ([goal] ++ goals)

meta
def evalStepLet (args: StepArgs): TacticM Unit :=
  withTraceNode `Step (fun _ => pure m!"Apply step let") do
    let goal ← getMainGoal
    let (letFv, goal) ← stepIntro goal
    applyLetTheorem args goal letFv

meta partial
def evalStep (args: StepArgs): TacticM Unit := do
  withMainContext do -- useful to get the retrieve FVar names in the trace
  let goalType ← Tactic.getMainTarget
  trace[Step] "step on goal: {goalType}"
  match ← preservesInvariantTelescope goalType with
  | (_, .wp func post tr) =>
    trace[Step] "goal is `preserves_invariant_on` on function {func}"
    match ← specTypeTelescope func with
    | .let_binding x xName =>
      evalStepLet args
    | .bind x f xName =>
      trace[Step] "function is a bind, x={x}, x name={xName}, f={f}"
      evalStepBind args xName
    | .final x =>
      trace[Step] "function is a final operation"
      evalStepFinal args
  | (_, .hoareTriple func pre post) =>
    trace[Step] "goal is `preserves_invariant` on function {func}, unfolding and recursing"
    let goal ← getMainGoal
    let goal ← Lean.Meta.unfoldTarget goal ``DY.hoareTriple
    let (_trFv, goal) ← goal.intro1P
    let (preFv, goal) ← goal.intro1
    let goal ← clearFvIfTrue goal preFv
    let (_trInvFv, goal) ← goal.intro1
    replaceMainGoal [goal]
    evalStep args
  | (_, .hoareTripleTC) =>
    let goal ← getMainGoal
    let [goal] ← goal.apply (← Term.mkConst ``DY.HoareTriple.mk) {} | throwError "failed to apply DY.HoareTriple.mk"
    replaceMainGoal [goal]
    evalStep args
  | (_, .hoareTripleGhostTC) =>
    let goal ← getMainGoal
    let [goal] ← goal.apply (← Term.mkConst ``DY.HoareTripleGhost.mk) {} | throwError "failed to apply DY.HoareTripleGhost.mk"
    replaceMainGoal [goal]
    evalStep args

elab (name := step) "step" args:stepArgs: tactic => do
  evalStep (← parseStepArgs args)

elab (name := step_let) "step_let" letFvSyn:term args:stepArgs: tactic => do
  withMainContext do
  let letFvTerm ← Tactic.elabTerm letFvSyn none
  let letFv := letFvTerm.fvarId!
  applyLetTheorem (← parseStepArgs args) (← getMainGoal) letFv

end DY.Step
