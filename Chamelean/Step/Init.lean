import Lean
import Chamelean.Step.Trace
import Chamelean.Step.LetUtils
import Chamelean.Step.Utils
import Chamelean.Trace

open Lean Elab Term Meta Tactic

namespace Chamelean.Step

inductive StepSpecTheorem where
  | wp
    (func: Expr)
    (post: Expr)
    (tr: Expr)
  | hoareTriple
    (func: Expr)
    (pre: Expr)
    (post: Expr)
deriving Repr

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
    if fName = ``Chamelean.hoareTriple then
      guard (args.size = 6)
      pure (xs_and_bi, StepSpecTheorem.hoareTriple args[3]! args[4]! args[5]!)
    else if fName = ``Chamelean.wp then
      guard (args.size = 6)
      pure (xs_and_bi, StepSpecTheorem.wp args[3]! args[4]! args[5]!)
    else
      throwError "not a constant"

inductive SpecType where
  | let_binding (x:Expr) (xName:Name)
  | bind (x:Expr) (f:Expr) (xName:Name)
  | final (x:Expr)

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

syntax stepArgs := ("with" " ⟨ " term,* " ⟩")? ("by" tacticSeq)?

structure StepArgs where
  xGhostTerm : Expr
  preTactic: Option Syntax

def parseStepArgs (args: TSyntax ``Chamelean.Step.stepArgs): TacticM StepArgs
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
      preTactic := disch
    }
  | _ => throwUnsupportedSyntax

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
      setGoals currentGoals
    | none =>
      let _ ← grind pre {} false #[] (pure ())
      pure ()

def monotonizeOneHypothesis
  (goal: MVarId)
  (hypFv: FVarId)
  (oldTraceFv: FVarId)
  (newTraceFv: FVarId)
  : TacticM (Expr × Expr)
  := goal.withContext do
    let oldHypType ← hypFv.getType
    let newHypType := oldHypType.replaceFVarId oldTraceFv (mkFVar newTraceFv)
    let newHypExpr ← mkFreshExprMVar newHypType
    let newHypMVarId := newHypExpr.mvarId!

    -- prove with grind using (scoped) monotonicity theorems
    withOpenIn `Chamelean.Trace.MonotoneLemmas do
      try
        let _ ← grind newHypMVarId {} false #[] (pure ())
      catch _ =>
        throwError
          "cannot monotonize `{oldHypType}`\n\
          TODO give hints on how to solve the issue"

    pure (newHypExpr, newHypType)

def isAnd (e : Expr) : Bool :=
  let (name, args) := e.getAppFnArgs
  name = `And ∧ args.size = 2

partial
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

def introAndMassagePostX
  (xName: Name)
  (goal: MVarId)
  : TacticM MVarId
  := do
    let (postXFv, goal) ← goal.intro1
    -- TODO: run a pass of simplification on post_x (e.g. iota reduction etc)
    let goal ← splitAndAt goal postXFv (prepend "h_" xName)
    pure goal

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

def massageNextGoal
  (conf: EvalStepConfig)
  (goal: MVarId)
  : TacticM MVarId
  := do
    goal.withContext do
    withTraceNode `Step (fun _ => pure m!"Massage the next goal") do

    -- Introduce variables and hypothesis
    let (_trMidFv, goal) ← goal.intro1
    let (_xFv, goal) ← goal.intro conf.xName
    -- we will not rely on the fvar above because
    -- `introAndMassagePostX` might trash them
    let goal ← introAndMassagePostX conf.xName goal
    let (_trInvFv, goal) ← goal.intro1
    let (trGrowsFv, goal) ← goal.intro1
    goal.withContext do

    -- get old and mid trace FVarId
    -- how: unify ?tr_old ≤ ?tr_mid with the hypthesis we introduced
    let (trOldFv, trMidFv) ← do
      let oldTraceMVarId ← mkFreshExprMVar (mkConst `Chamelean.ProofTrace)
      let midTraceMVarId ← mkFreshExprMVar (mkConst `Chamelean.ProofTrace)
      let trLeToUnify ← mkAppOptM `LE.le #[none, none, oldTraceMVarId, midTraceMVarId]
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
      let trInvOldType ← mkAppOptM `Chamelean.Trace.invariant #[mkFVar trOldFv]
      let trInvOldMVarId ← mkFreshExprMVar trInvOldType
      trace[Step] "finding in assumptions {trInvOldType}"
      trInvOldMVarId.mvarId!.assumption
      let trInvExpr ← instantiateMVars trInvOldMVarId
      unless trInvExpr.isFVar do
        throwError "old trace invariant is not an fvar: {trInvExpr}"
      pure trInvExpr.fvarId!

    -- Apply monotonicity lemmas on the context,
    -- while preserving the order assumptions appear in.
    -- We could do this with Lean.MVarId.replace,
    -- however this function may trash fvar ids
    -- (because it reverts and re-introduces assumptions),
    -- hence give a map from old to new fvar ids,
    -- which is a bit cumbersome,
    -- especially because we want to replace many of the assumptions.
    -- Instead, we do something similar to Lean.MVarId.replace ourselves:
    -- revert all assumptions (except the core ones about traces such as trace invariant etc)
    -- and re-introduce them one by one, applying monotonicity lemmas if needed.

    -- Revert all assumptions (except the core ones)
    let goal ← goal.revertAllExcept (fun fvar => do
      let ty ← fvar.getType
      let ty ← ty.sanitize
      let (name, _) := ty.getAppFnArgs
      pure (
        name = `Chamelean.ProofTrace ∨
        name = `Chamelean.Trace.invariant ∨
        name = `LE.le
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
      guard (lctx.contains trGrowsFv)

    -- Introduce each assumption one by one,
    -- and register old assumptions that were monotonized
    -- to clear them afterward.
    -- We don't clear them on the fly,
    -- as a old assumption (e.g. bytes_invariant)
    -- might be useful to monotonize other assumptions (e.g. involving get_label).
    let mut goal := goal
    let mut monotonizedFv := #[]
    for _ in [0:(getIntrosSize (← goal.getType))] do
      let (hypFv, newGoal) ← goal.intro1P
      goal := newGoal
      -- need goal.withContext here because of localDeclDependsOn
      let (newGoal, toClear) ← goal.withContext do
        trace[Step] "introduced: {← hypFv.getUserName}: {← hypFv.getType}"
        let dependsOnOldTrace: Bool ←
          localDeclDependsOn (← hypFv.getDecl) trOldFv
        if dependsOnOldTrace then
          -- Some assumptions depend on the trace but shouldn't me monotonized
          -- e.g. trace invariant, etc
          -- However, note they were not reverted,
          -- hence everything we introduce needs monotonizing.
          trace[Step] "depends on trace, monotonizing"
          let (newHypProof, newHyp) ← monotonizeOneHypothesis goal hypFv trOldFv trMidFv
          let goal ← goal.assert (← hypFv.getUserName) newHyp newHypProof
          let (_, goal) ← goal.intro1P
          pure (goal, some hypFv)
        else
          pure (goal, none)
      goal := newGoal
      if let some fv := toClear then
        monotonizedFv := monotonizedFv.push fv

    -- Rename the new traces with the names of the old traces
    let trName ← trOldFv.getUserName
    goal.modifyLCtx (fun lctx =>
      lctx.setUserName trMidFv trName
    )

    let oldTraceFv := #[
      trInvOldFv,
      trGrowsFv,
      trOldFv, -- cleared after hypothesis that depend on it
    ]

    -- Clear assumptions that were monotonized + old trace assumptions
    for fv in monotonizedFv ++ oldTraceFv do
      goal ← goal.clear fv

    -- Cleanup random garbage
    -- e.g. True hypothesis, or useless x: Unit
    -- TODO: it may be a bit brutal?
    goal ← goal.cleanup

    pure goal

/--
  Apply a theorem about `preserves_invariant_on` on the goal.
  The function is commented with `bind_preserves_invariant_on` in mind,
  but works similarly for other similar theorems
  (as parametrized by `EvalStepConfig`)
-/
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
      bindMVars[conf.hasGhostPosition]!.assignTypeclassInstance
      let expectedGhostType ← bindMVars[conf.ghostPosition]!.getType
      let gotGhostType ← inferType args.xGhostTerm
      unless (← isDefEq expectedGhostType gotGhostType) do
        throwError "Ghost parameter has type {gotGhostType}, expected type {expectedGhostType}.\nHint: use `step ... with ⟨ ... ⟩`"
      bindMVars[conf.ghostPosition]!.safeAssign args.xGhostTerm

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

def evalStepBind
  (args: StepArgs)
  (xName: Name)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := ``Chamelean.Traceful.bind_wp
      nbArgs := 15
      nbUnifiedArgs := 14
      ghostPosition := 3,
      hasGhostPosition := 10
      xSpecTheoremPosition := 11
      trInvPosition := 12
      preconditionPosition := 13
      nextPosition := 14
      xName
    }

def evalStepFinal
  (args: StepArgs)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := ``Chamelean.Traceful.finish_wp
      nbArgs := 13
      nbUnifiedArgs := 12
      ghostPosition := 2
      hasGhostPosition := 8
      xSpecTheoremPosition := 9
      trInvPosition := 10
      preconditionPosition := 11
      nextPosition := 12
      xName := `x
    }

def applyLetTheorem (args: StepArgs) (goal: MVarId) (letFv: FVarId): TacticM Unit :=
  do
  goal.withContext do
    let letValue := (← letFv.getDecl).value
    let letName := (← letFv.getDecl).userName

    -- applyTheoremExprForall = apply_hoare_triple_pure
    let applyTheoremExprForall ← Term.mkConst ``Chamelean.apply_hoare_triple_pure
    -- applyTheoremTypeForall = ∀ ghost x ..., post x tr
    let applyTheoremTypeForall ← inferType applyTheoremExprForall
    -- applyTheoremType = post x tr
    let (applyMVars, _, applyTheoremType) ← forallMetaTelescope applyTheoremTypeForall
    -- applyTheoremExpr = apply_hoare_triple_pure ?ghost ?x ?...
    let applyTheoremExpr := mkAppN applyTheoremExprForall applyMVars
    let applyMVars := applyMVars.map (·.mvarId!)

    -- x
    applyMVars[3]!.safeAssign (.fvar letFv)
    -- HasGhostArgumentType
    applyMVars[6]!.assignTypeclassInstance
    let expectedGhostType ← applyMVars[2]!.getType
    let gotGhostType ← inferType args.xGhostTerm
    unless (← isDefEq expectedGhostType gotGhostType) do
      -- TODO: could be a `step_let` (bad error message)
      throwError "Ghost parameter has type {gotGhostType}, expected type {expectedGhostType}.\nHint: use `step ... with ⟨ ... ⟩`"
    -- ghost
    applyMVars[2]!.safeAssign args.xGhostTerm
    -- HoareTriplePureGhost instance
    applyMVars[7]!.assignTypeclassInstance
    -- tr
    applyMVars[8]!.assumption -- "I am feeling lucky" (works if there is only one `ProofTrace` in the local context)

    let pfPreMVar := applyMVars[9]!
    solvePrecondition args pfPreMVar
    guard (← pfPreMVar.isAssigned)

    -- sanity check
    guard (applyMVars.size = 10);
    for i in [0:10] do
      guard (← applyMVars[i]!.isAssigned)

    let goal ← goal.assert .anonymous applyTheoremType applyTheoremExpr
    let goal ← introAndMassagePostX letName goal

    let goals ← getUnsolvedGoals
    setGoals ([goal] ++ goals)

def evalStepLet (args: StepArgs): TacticM Unit :=
  withTraceNode `Step (fun _ => pure m!"Apply step let") do
    let goal ← getMainGoal
    let (letFv, goal) ← stepIntro goal
    applyLetTheorem args goal letFv

partial
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
    let goal ← Lean.Meta.unfoldTarget goal ``Chamelean.hoareTriple
    let (_trFv, goal) ← goal.intro1P
    let (_preFv, goal) ← goal.intro1
    let (_trInvFv, goal) ← goal.intro1
    replaceMainGoal [goal]
    evalStep args

elab (name := step) "step" args:stepArgs: tactic => do
  evalStep (← parseStepArgs args)

elab (name := step_let) "step_let" letFvSyn:term args:stepArgs: tactic => do
  withMainContext do
  let letFvTerm ← Tactic.elabTerm letFvSyn none
  let letFv := letFvTerm.fvarId!
  applyLetTheorem (← parseStepArgs args) (← getMainGoal) letFv

end Chamelean.Step
