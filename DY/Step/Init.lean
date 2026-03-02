import Lean
import DY.Step.Trace
import DY.Step.LetUtils
import DY.Step.Utils
import DY.Trace

open Lean Elab Term Meta Tactic

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
    if fName = ``DY.hoareTriple then
      guard (args.size = 7)
      pure (xs_and_bi, StepSpecTheorem.hoareTriple args[4]! args[5]! args[6]!)
    else if fName = ``DY.wp then
      guard (args.size = 7)
      pure (xs_and_bi, StepSpecTheorem.wp args[4]! args[5]! args[6]!)
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
  xGhostTermProvided: Bool
  preTactic: Option Syntax

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
      let _ ← grind pre {} false #[] none
      pure ()

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
    withOpenIn `DY.Trace.MonotoneLemmas do
      try
        let _ ← grind newHypMVarId {} false #[] none
      catch _ =>
        throwError
          "cannot monotonize `{oldHypType}`\n\
          TODO give hints on how to solve the issue"

    pure (newHypExpr, newHypType)

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
-/

def monotonizeContext
  (trOldFv trMidFv: FVarId)
  (goal: MVarId)
  : TacticM (MVarId × Array FVarId)
:= do
  withTraceNode `Step (fun _ => pure m!"Monotonize the next goal") do

  -- Revert all assumptions (except the core ones)
  let goal ← goal.revertAllExcept (fun fvar => do
    let ty ← fvar.getType
    let ty ← ty.sanitize
    let (name, _) := ty.getAppFnArgs
    -- hack: for typeclasses such as BytesCtors
    let isTcInstance := (← fvar.getBinderInfo).isInstImplicit
    pure (
      isTcInstance ∨
      name = ``DY.ProofTrace ∨
      name = ``DY.Trace.invariant ∨
      name = ``LE.le
    )
  )
  trace[Step] "reverted goal: {← goal.getType}"

  -- Sanity check: we didn't trash the fvars we obtained earlier
  trace[Step] "checking fvars are still in local context"
  do
    let lctx ← goal.withContext getLCtx
    guard (lctx.contains trOldFv)
    guard (lctx.contains trMidFv)

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

  return (goal, monotonizedFv)

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
      let oldTraceMVarId ← mkFreshExprMVar (← mkAppOptM ``DY.ProofTrace #[none])
      let midTraceMVarId ← mkFreshExprMVar (← mkAppOptM ``DY.ProofTrace #[none])
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
      let trInvOldType ← mkAppOptM ``DY.Trace.invariant #[none, mkFVar trOldFv]
      let trInvOldMVarId ← mkFreshExprMVar trInvOldType
      trace[Step] "finding in assumptions {trInvOldType}"
      trInvOldMVarId.mvarId!.assumption
      let trInvExpr ← instantiateMVars trInvOldMVarId
      unless trInvExpr.isFVar do
        throwError "old trace invariant is not an fvar: {trInvExpr}"
      pure trInvExpr.fvarId!

    -- monotonize context
    let (goal, monotonizedFv) ← monotonizeContext trOldFv trMidFv goal

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
    let mut goal := goal
    for fv in monotonizedFv ++ oldTraceFv do
      goal ← goal.clear fv

    -- Cleanup random garbage
    -- e.g. True hypothesis, or useless x: Unit
    -- TODO: it may be a bit brutal?
    goal ← goal.cleanup

    pure goal

def assignGhostParameterAux
  (args: StepArgs)
  (ghostMVarId: MVarId)
  : MetaM Unit
  := do
    let expectedGhostType ← ghostMVarId.getType
    let gotGhostType ← inferType args.xGhostTerm
    unless (← isDefEq expectedGhostType gotGhostType) do
      throwError "Ghost parameter has type {gotGhostType}, expected type {expectedGhostType}.\nHint: use `step ... with ⟨ ... ⟩`"
    ghostMVarId.safeAssign args.xGhostTerm

/--
  If no ghost parameter was provided,
  try to use a user-provided meta-program
  to obtain this ghost parameter
-/
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

def evalStepBind
  (args: StepArgs)
  (xName: Name)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := ``DY.Traceful.bind_wp
      nbArgs := 16
      nbUnifiedArgs := 15
      ghostPosition := 4,
      hasGhostPosition := 11
      xSpecTheoremPosition := 12
      trInvPosition := 13
      preconditionPosition := 14
      nextPosition := 15
      xName
    }

def evalStepFinal
  (args: StepArgs)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := ``DY.Traceful.finish_wp
      nbArgs := 14
      nbUnifiedArgs := 13
      ghostPosition := 3
      hasGhostPosition := 9
      xSpecTheoremPosition := 10
      trInvPosition := 11
      preconditionPosition := 12
      nextPosition := 13
      xName := `x
    }

def applyLetTheorem (args: StepArgs) (goal: MVarId) (letFv: FVarId): TacticM Unit :=
  goal.withContext do
  withTraceNode `Step (fun _ => pure m!"Apply let theorem") do
    let letValue := (← letFv.getDecl).value
    let letName := (← letFv.getDecl).userName

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
    applyMVars[4]!.safeAssign (.fvar letFv)
    -- ghost things
    assignGhostParameter args applyMVars[7]! applyMVars[3]!
    -- HoareTriplePureGhost instance
    applyMVars[8]!.assignTypeclassInstance
    -- tr
    applyMVars[9]!.assumption -- "I am feeling lucky" (works if there is only one `ProofTrace` in the local context)

    let pfPreMVar := applyMVars[10]!
    solvePrecondition args pfPreMVar
    guard (← pfPreMVar.isAssigned)

    -- sanity check
    guard (applyMVars.size = 11);
    for i in [0:11] do
      guard (← applyMVars[i]!.isAssigned)

    trace[Step] "using theorem {applyTheoremExpr} of type {applyTheoremType}"

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
    let goal ← Lean.Meta.unfoldTarget goal ``DY.hoareTriple
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

end DY.Step
