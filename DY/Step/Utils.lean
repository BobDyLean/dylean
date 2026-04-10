module

public import Lean

open Lean Elab Term Meta Tactic

public section

/--
  Variant of Batteries' Lean.MVarId.assignIfDefEq,
  using MVarId.checkedAssign (even safer).
-/
public
def Lean.MVarId.safeAssign (mvarId : MVarId) (val : Expr) : MetaM Unit := do
  unless ← isDefEq (← mvarId.getType) (← inferType val) do
    throwError "safeAssign: cannot unify types `{← mvarId.getType}` and `{← inferType val}`"
  unless ← mvarId.checkedAssign val do
    throwError "safeAssign: checkedAssign failed?"

public
def Lean.MVarId.assignTypeclassInstance (mvarId : MVarId): MetaM Unit := do
  mvarId.safeAssign (← synthInstance (← mvarId.getType))

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

public
def Lean.Expr.sanitize (val : Expr) : MetaM Expr := do
  pure ((← instantiateMVars val).consumeMData)

public
def prepend (s: String) (n: Name): Name :=
  let view := extractMacroScopes n
  ({ view with name := barePrepend s view.name }).review
where
  barePrepend (s: String) (n: Name): Name :=
    match n with
    | .anonymous => n
    | .str pre str =>
      .str pre (s ++ str)
    | .num pre i =>
      .num (barePrepend s pre) i

-- 0-element tuple: unit
-- 1-element tuple: this element
-- n-element tuple: actually make a tuple (i.e. nested pairs)
public
def makeTuple (arr: Array Expr): MetaM Expr := do
  match arr.size with
  | 0 => mkAppM ``Unit.unit #[]
  | 1 => pure arr[0]!
  | sz =>
    arr.foldrM (fun t acc => do
      let u1 ← mkFreshLevelMVar
      let u2 ← mkFreshLevelMVar
      let t1 ← inferType t
      let t2 ← inferType acc
      -- We use the `N` variant of mkApp, because the `M` variant does not allow t1 or t2 to contain metavariables
      -- These metavariables can be instantiated by unification later.
      pure (mkAppN (.const ``Prod.mk [u1, u2]) #[t1, t2, t, acc])
    ) (arr[sz-1]!) (start := sz-1)

end
