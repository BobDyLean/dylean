module

public meta import Lean

open Lean Elab Term Meta Tactic

elab "cleanup" : tactic => do
  let goal ← getMainGoal
  let goal ← goal.cleanup
  replaceMainGoal ([goal])
