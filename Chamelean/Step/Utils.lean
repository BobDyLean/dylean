import Lean

open Lean Elab Term Meta Tactic

/--
  Variant of Batteries' Lean.MVarId.assignIfDefEq,
  using MVarId.checkedAssign (even safer).
-/
def Lean.MVarId.safeAssign (mvarId : MVarId) (val : Expr) : MetaM Unit := do
  guard (← isDefEq (← mvarId.getType) (← inferType val))
  guard (← mvarId.checkedAssign val)

/--
  This function applies sanitization on expressions to avoid common footguns.
  There are (at least) two footguns while working with expressions:
  - uninstantiated metavariables
  - metadata
  These may cause functions such as `getAppFnArgs` to fail,
  although when printing the expressions, they should clearly succeed:
  indeed, the pretty-printer instantiate metavariables first,
  preventing the success from any debugging attempts.
  To improve the debugging experience, one may use the option
  > set_option pp.instantiateMVars false
  To avoid problems in the first place, one may use this function pervasively.
-/

def Lean.Expr.sanitize (val : Expr) : MetaM Expr := do
  pure ((← instantiateMVars val).consumeMData)

-- Revert every fvar except the one satisfying `p`
-- (adapted from Lean.MVarId.revertAll)
def Lean.MVarId.revertAllExcept (mvarId : MVarId) (p: FVarId → MetaM Bool): MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `revertAllThat
  let mut toRevert := #[]
  for fvarId in (← getLCtx).getFVarIds do
    unless (← p fvarId) ∨ (← fvarId.getDecl).isAuxDecl do
      toRevert := toRevert.push fvarId
  mvarId.setKind .natural
  let (_, mvarId) ← mvarId.revert toRevert
    (preserveOrder := true)
    (clearAuxDeclsInsteadOfRevert := true)
  return mvarId

/--
  Opens a namespace (similarly to `open ... in` in tactics).
  Useful to enable scoped lemmas (e.g. for `grind` or `simp`).
-/
def withOpenIn
  [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m]
  (namespaceName : Name) (k : m α): m α
  := do
    try
      pushScope
      activateScoped namespaceName
      k
    finally
      popScope
