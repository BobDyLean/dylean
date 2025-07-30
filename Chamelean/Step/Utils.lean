import Lean

open Lean Elab Term Meta Tactic

/--
  The documentation of Lean.MVarID.assign tells the following:
  > This is a low-level API, and it is safer to use `isDefEq (mkMVar mvarId) x`.
  This function does so.
-/
def _root_.Lean.MVarId.safeAssign (mvarId : MVarId) (val : Expr) : MetaM Unit := do
  guard (← isDefEq (mkMVar mvarId) val)

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

def _root_.Lean.Expr.sanitize (val : Expr) : MetaM Expr := do
  pure ((← instantiateMVars val).consumeMData)

