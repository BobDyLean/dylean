import Lean
import Chamelean.Step.Trace
import Chamelean.Step.Utils
import Chamelean.Trace

open Lean Elab Term Meta Tactic

namespace Chamelean.Step

structure Rules where
  rules: DiscrTree Name
deriving Inhabited

def Rules.empty : Rules := {
  rules := DiscrTree.empty,
}

def Rules.insert (r : Rules) (kv : Array DiscrTree.Key × Name) : Rules := {
  rules := r.rules.insertCore kv.fst kv.snd,
}

def Extension := SimpleScopedEnvExtension (Array DiscrTree.Key × Name) Rules
deriving Inhabited

structure StepSpecAttr where
  attr: AttributeImpl
  ext: Extension
deriving Inhabited

inductive StepSpecTheorem where
  | preserves_invariant_on
    (func: Expr)
    (post: Expr)
    (tr_exec: Expr)
    (tr_proof: Expr)
  | preserves_invariant
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
    if fName = ``Chamelean.Trace.preserves_invariant then
      guard (args.size = 4)
      pure (xs_and_bi, StepSpecTheorem.preserves_invariant args[1]! args[2]! args[3]!)
    else if fName = ``Chamelean.Trace.preserves_invariant_on then
      guard (args.size = 5)
      pure (xs_and_bi, StepSpecTheorem.preserves_invariant_on args[1]! args[2]! args[3]! args[4]!)
    else
      throwError "not a constant"

private def saveStepSpecFromThm (ext : Extension) (attrKind : AttributeKind) (theoremName : Name) :
  AttrM Unit := do
  -- Lookup the theorem
  let env ← getEnv
  trace[Step] "Registering `step` theorem for {theoremName}"
  let some thDecl := env.findAsync? theoremName
    | throwError "Could not find theorem {theoremName}"
  let type := thDecl.sig.get.type
  let key ← MetaM.run' (do
    match ← preservesInvariantTelescope type with
    | (_, StepSpecTheorem.preserves_invariant func _ _) =>
      trace[Step] "Registering spec theorem ({theoremName}) for expr: {func}"
      -- -- Convert the function expression to a discrimination tree key
      DiscrTree.mkPath func
    | (_, _) =>
      throwError "can only register theorems on `preserves_invariant`"
  )
  -- Save the entry
  ScopedEnvExtension.add ext (key, theoremName) attrKind
  trace[Step] "Saved the entry"
  pure ()

initialize stepAttr : StepSpecAttr ← do
  let ext ←
    registerSimpleScopedEnvExtension {
      name        := `stepMap,
      initial     := Rules.empty,
      addEntry    := Rules.insert,
    }
  let attrImpl : AttributeImpl := {
    name := `step
    descr := "Adds theorems to the `step` database"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      saveStepSpecFromThm ext attrKind thName
    erase := fun thName => do
      throwError "step erase: not implemented"
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def StepSpecAttr.find? (s : StepSpecAttr) (e : Expr) : MetaM (Array Name) := do
  let state := s.ext.getState (← getEnv)
  let rules ← state.rules.getMatch e
  pure rules

inductive SpecType where
  | bind (x:Expr) (f:Expr) (xName:Name)
  | final (x:Expr)

def specTypeTelescope
  (type: Expr)
  : MetaM SpecType
  := do
    withTraceNode `Step (fun _ => pure m!"Analyze the function to prove") do
    let type ← type.sanitize
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

syntax stepArgs := ("with" " ⟨ " term,* " ⟩")?

structure StepArgs where
  xGhostTerms : Array Expr

def parseStepArgs (args: TSyntax ``Chamelean.Step.stepArgs): TacticM StepArgs
  :=
  withMainContext do
  trace[Step] "Step arguments: {args.raw}"
  match args with
  | `(stepArgs| $[with ⟨ $xGhosts,* ⟩ ]? ) =>
    let xGhostTerms ←
      match xGhosts with
      | none => pure #[]
      | some xGhosts =>
        xGhosts.getElems.mapM (fun xGhost =>
          Tactic.elabTerm xGhost none
        )
    pure {
      xGhostTerms := xGhostTerms
    }
  | _ => throwUnsupportedSyntax

structure EvalStepConfig where
  theoremName: Name
  nbArgs: Nat
  nbUnifiedArgs: Nat
  xPosition: Nat
  xSpecTheoremPosition: Nat
  trInvPosition: Nat
  trRelPosition: Nat
  preconditionPosition: Nat
  nextPosition: Nat
  xName: Name

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
    withOpenIn `Chamelean.Trace.Monotone do
      try
        let _ ← grind newHypMVarId {} false #[] (pure ())
      catch _ =>
        throwError
          "cannot monotonize `{oldHypType}`\n\
          TODO give hints on how to solve the issue"

    pure (newHypExpr, newHypType)

/--
  Massage the next goal:
  - introduce the ∀ and hypothesis in the context
    (and use the name used in the specification)
  - split the ∧ in precondition (TODO)
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
    let (trExecMidFv, goal) ← goal.intro1
    let (trProofMidFv, goal) ← goal.intro1
    let (_xFv, goal) ← goal.intro conf.xName
    let (_postXFv, goal) ← goal.intro1
    let (_trInvFv, goal) ← goal.intro1
    let (_trRelFv, goal) ← goal.intro1
    let (trGrowsFv, goal) ← goal.intro1
    goal.withContext do

    -- get old trace_proof FVarId
    -- how: unify ?trace_proof_old ≤ trace_proof_new with the hypthesis we introduced
    let trProofOldFv ← do
      let oldTraceMVarId ← mkFreshExprMVar (mkConst `Chamelean.Trace.ProofTrace)
      let trRelToUnify ← mkAppOptM `LE.le #[none, none, oldTraceMVarId, mkFVar trProofMidFv]
      trace[Step] "finding old trace fvarid by unifying {trRelToUnify} and {(← trGrowsFv.getType)}"
      unless (← isDefEq trRelToUnify (← trGrowsFv.getType)) do
        throwError "cannot unify {trRelToUnify} and {(← trGrowsFv.getType)}"
      let oldTraceExpr ← instantiateMVars oldTraceMVarId
      unless oldTraceExpr.isFVar do
        throwError "old trace is not an fvar: {oldTraceExpr}"
      pure oldTraceExpr.fvarId!
    trace[Step] "old proof trace is {mkFVar trProofOldFv}"

    -- get old execution trace FVarId
    -- how: unify trace_rel ?trace_exec_old trace_proof_old with an assumption
    let (trExecOldFv, trRelOldFv) ← do
      let oldTraceMVarId ← mkFreshExprMVar (mkConst `Chamelean.Trace.ExecutionTrace)
      let trRelToUnifyType ← mkAppOptM `Chamelean.Trace.trace_rel #[oldTraceMVarId, mkFVar trProofOldFv]
      let trRelToUnifyMVarId ← mkFreshExprMVar trRelToUnifyType
      trace[Step] "finding in assumptions {trRelToUnifyType}"
      trRelToUnifyMVarId.mvarId!.assumption
      let oldTraceExpr ← instantiateMVars oldTraceMVarId
      let oldTraceRelExpr ← instantiateMVars trRelToUnifyMVarId
      unless oldTraceExpr.isFVar do
        throwError "old trace is not an fvar: {oldTraceExpr}"
      unless oldTraceRelExpr.isFVar do
        throwError "old trace rel is not an fvar: {oldTraceRelExpr}"
      pure (oldTraceExpr.fvarId!, oldTraceRelExpr.fvarId!)
    trace[Step] "old execution trace is {mkFVar trExecOldFv}"
    trace[Step] "old execution trace relation is {mkFVar trRelOldFv}"

    -- get trace invariant for old trace
    -- how: unify trace_invariant trace_proof_old with an assumption
    let trInvOldFv ← do
      let trInvOldType ← mkAppOptM `Chamelean.Trace.trace_invariant #[mkFVar trProofOldFv]
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
        name = `Chamelean.Trace.ExecutionTrace ∨
        name = `Chamelean.Trace.ProofTrace ∨
        name = `Chamelean.Trace.trace_invariant ∨
        name = `Chamelean.Trace.trace_rel ∨
        name = `LE.le
      )
    )
    trace[Step] "reverted goal: {← goal.getType}"

    -- Sanity check: we didn't trash the fvars we obtained earlier
    trace[Step] "checking fvars are still in local context"
    do
      let lctx ← goal.withContext getLCtx
      guard (lctx.contains trExecOldFv)
      guard (lctx.contains trProofOldFv)
      guard (lctx.contains trExecMidFv)
      guard (lctx.contains trProofMidFv)
      guard (lctx.contains trInvOldFv)
      guard (lctx.contains trRelOldFv)
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
          localDeclDependsOn (← hypFv.getDecl) trProofOldFv
        if dependsOnOldTrace then
          -- Some assumptions depend on the trace but shouldn't me monotonized
          -- e.g. trace invariant, etc
          -- However, note they were not reverted,
          -- hence everything we introduce needs monotonizing.
          trace[Step] "depends on trace, monotonizing"
          let (newHypProof, newHyp) ← monotonizeOneHypothesis goal hypFv trProofOldFv trProofMidFv
          let goal ← goal.assert (← hypFv.getUserName) newHyp newHypProof
          let (_, goal) ← goal.intro1P
          pure (goal, some hypFv)
        else
          pure (goal, none)
      goal := newGoal
      if let some fv := toClear then
        monotonizedFv := monotonizedFv.push fv

    -- Rename the new traces with the names of the old traces
    let trExecName ← trExecOldFv.getUserName
    let trProofName ← trProofOldFv.getUserName
    goal.modifyLCtx (fun lctx =>
      let lctx := lctx.setUserName trExecMidFv trExecName
      let lctx := lctx.setUserName trProofMidFv trProofName
      lctx
    )

    let oldTraceFv := #[
      trInvOldFv,
      trRelOldFv,
      trGrowsFv,
      trProofOldFv,
      trExecOldFv,
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
      -- bindTheoremTypeForall = ∀ x f ..., preserves_invariant_on (x >>= f) ...
      let bindTheoremTypeForall ← inferType bindTheoremExprForall
      -- bindTheoremType = preserves_invariant_on (x >>= f) ...
      let (bindMVars, _, bindTheoremType) ← forallMetaTelescope bindTheoremTypeForall
      -- bindTheoremExpr = bind_preserves_invariant_on ?x ?f ?...
      let bindTheoremExpr := mkAppN bindTheoremExprForall bindMVars
      let bindMVars := bindMVars.map (·.mvarId!)

      -- step 1: unify bindTheoremType with the goal.
      -- this will instantiate a bunch of metavariables of bindMVars
      trace[Step] "Step 1: unify goal with the step theorem"
      trace[Step] "step theorem before unification {bindTheoremType}"
      unless (← isDefEq bindTheoremType (← getMainTarget)) do
        throwError "step: cannot unify goal and bind_preserves_invariant_on"
      let bindTheoremType ← instantiateMVars bindTheoremType
      trace[Step] "step theorem after unification {bindTheoremType}"

      guard (bindMVars.size = conf.nbArgs) -- sanity check
      -- (sanity) check that some of the metavariable were correctly assigned
      for i in [0:conf.nbUnifiedArgs] do
        guard (← bindMVars[i]!.isAssigned)

      -- step 2: obtain the @[step] theorem to apply
      trace[Step] "Step 2: obtain the @[step] theorem to apply"
      let xTheoremName ← do
        let xMVar := bindMVars[conf.xPosition]!
        let xExpr ← instantiateMVars (.mvar xMVar)
        let theoremNames ← stepAttr.find? xExpr
        trace[Step] "got theorems {theoremNames}"
        if theoremNames.size = 0 then
          throwError "step: found no theorem"
        if theoremNames.size ≥ 2 then
          throwError "step: too many theorems? {theoremNames}"
        else
          pure theoremNames[0]!
      trace[Step] "got theorem {xTheoremName}"

      -- xTheoremExprForall = x_spec
      let xTheoremExprForall ← Term.mkConst xTheoremName
      -- xTheoremTypeForall = ∀ ..., preserves_invariant ...
      let xTheoremTypeForall ← inferType xTheoremExprForall
      -- xTheoremType = preserves_invariant ...
      let (xTheoremMVars, _, xTheoremType) ← forallMetaTelescope xTheoremTypeForall
      -- xTheoremExpr = x_spec ?...
      let xTheoremExpr := mkAppN xTheoremExprForall xTheoremMVars
      let xTheoremMVars := xTheoremMVars.map (·.mvarId!)

      -- step 3: unify the theorem for x with the one required by `bind_preserves_invariant_on`
      -- this will also unify the precondition and postcondition of x
      let pf_x_mvar := bindMVars[conf.xSpecTheoremPosition]!
      trace[Step] "Step 3: unify the theorem for x in step theorem with {xTheoremName}"
      trace[Step] "gonna unify {xTheoremType}"
      unless (← isDefEq xTheoremType (← pf_x_mvar.getType)) do
        throwError "step: cannot unify blah and bluh { xTheoremType }"
      trace[Step] "resulting in {← instantiateMVars xTheoremType}"
      pf_x_mvar.assign xTheoremExpr

      -- sanity checks
      guard (← bindMVars[conf.xSpecTheoremPosition-2]!.isAssigned) -- pre_x
      guard (← bindMVars[conf.xSpecTheoremPosition-1]!.isAssigned) -- post_x
      guard (← bindMVars[conf.xSpecTheoremPosition]!.isAssigned) -- pf_x (we just assigned it)

      -- trace invariant and trace relationships are in the assumptions
      bindMVars[conf.trInvPosition]!.assumption --pf_tr_inv
      bindMVars[conf.trRelPosition]!.assumption --pf_tr_rel

      let pfPreXMVar := bindMVars[conf.preconditionPosition]!
      let pfNextMVar := bindMVars[conf.nextPosition]!

      -- step 4: assign x theorem metavars
      -- We need to do it before massaging the next goal,
      -- because if the next goal has unassigned metavariables in its context,
      -- then we cannot clear any fvar in its context (hence monotonizing the context)
      -- because `Lean.localDeclDependsOn ldecl fvar`
      -- returns true on `ldecl` with unassigned metavariables
      -- because they might be later assigned to `fvar` in another goal
      let xTheoremGoals ← xTheoremMVars.filterM (fun x => not <$> (x.isAssigned))
      unless xTheoremGoals.size = args.xGhostTerms.size do
        let xTheoremGoalTypes ← xTheoremGoals.mapM (·.getType)
        throwError "step: expecting ghost arguments of type {xTheoremGoalTypes}, provide them using `step with ⟨ ..., ... ⟩`"

      for (mvar, val) in Array.zip xTheoremGoals args.xGhostTerms do
        mvar.safeAssign val

      -- step 5: massage the next goal
      let pfNextMVar ← massageNextGoal conf pfNextMVar

      -- step 6: close the current goal
      trace[Step] "Step 4: closing goal with {bindTheoremExpr}"
      let goalMVarId ← getMainGoal
      goalMVarId.assign bindTheoremExpr

      -- step 7: update goal list
      let bindTheoremGoals := [pfPreXMVar, pfNextMVar]
      let goals ← getUnsolvedGoals
      setGoals (xTheoremGoals.toList ++ bindTheoremGoals ++ goals)


def evalStepBind
  (args: StepArgs)
  (xName: Name)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := `Chamelean.Trace.bind_preserves_invariant_on
      nbArgs := 14
      nbUnifiedArgs := 7
      xPosition := 2
      xSpecTheoremPosition := 9
      trInvPosition := 10
      trRelPosition := 11
      preconditionPosition := 12
      nextPosition := 13
      xName
    }

def evalStepFinal
  (args: StepArgs)
  : TacticM Unit
  := do
    evalStepAux args {
      theoremName := `Chamelean.Trace.finish_preserves_invariant_on
      nbArgs := 12
      nbUnifiedArgs := 5
      xPosition := 1
      xSpecTheoremPosition := 7
      trInvPosition := 8
      trRelPosition := 9
      preconditionPosition := 10
      nextPosition := 11
      xName := `x
    }

partial
def evalStep (args: StepArgs): TacticM Unit := do
  withMainContext do -- useful to get the retrieve FVar names in the trace
  let goalType ← Tactic.getMainTarget
  trace[Step] "step on goal: {goalType}"
  match ← preservesInvariantTelescope goalType with
  | (_, .preserves_invariant_on func post tr_exec tr_proof) =>
    trace[Step] "goal is `preserves_invariant_on` on function {func}"
    match ← specTypeTelescope func with
    | .bind x f xName =>
      trace[Step] "function is a bind, x={x}, x name={xName}, f={f}"
      evalStepBind args xName
    | .final x =>
      trace[Step] "function is a final operation"
      evalStepFinal args
  | (_, .preserves_invariant func pre post) =>
    trace[Step] "goal is `preserves_invariant` on function {func}, unfolding and recursing"
    let goal ← getMainGoal
    let goal ← Lean.Meta.unfoldTarget goal `Chamelean.Trace.preserves_invariant
    let (_trExecFv, goal) ← goal.intro1P
    let (_trProofFv, goal) ← goal.intro1P
    let (_preFv, goal) ← goal.intro1
    let (_trInvFv, goal) ← goal.intro1
    let (_trRelFv, goal) ← goal.intro1
    replaceMainGoal [goal]
    evalStep args

elab (name := step) "step" args:stepArgs: tactic => do
  evalStep (← parseStepArgs args)

end Chamelean.Step
