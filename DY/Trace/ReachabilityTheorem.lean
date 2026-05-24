module

public import DY.Trace.Reachability
public import DY.Trace.Invariant
public import DY.Trace.Manipulation
import all DY.Trace.Reachability
import all DY.Trace.Invariant
public meta import DY.Meta.CombineMacro

namespace DY

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]

public
class ReachableImpliesInvariant (config: ReachabilityConfig) where
  pf:
    ∀ input,
      HoareTriple
        (config.step input).snd
        (fun tr => config.PreCond input tr.erase)
        (fun _ _ => True)

public
instance
  {α: Type}
  (configs: α → ReachabilityConfig)
  [insts: ∀ id, ReachableImpliesInvariant (configs id)]
  : ReachableImpliesInvariant (.combine configs)
where
  pf := fun ⟨ id, x ⟩ =>
    (insts id).pf x

public
theorem Trace.Reachable_implies_Invariant
  (config: ReachabilityConfig)
  [inst: ReachableImpliesInvariant config]
  (trExec: ExecTrace)
  : trExec.Reachable config →
    ∃ trProof: ProofTrace,
      trProof.erase = trExec ∧
      trProof.Invariant
:= by
  intro h_reach
  induction h_reach
  · exists Trace.nil
  rename_i input h_pre h_reach ih
  obtain ⟨ trProofMid, _, _ ⟩ := ih
  have h_wp := (inst.pf input).pf trProofMid (by simp_all) (by simp_all)
  dsimp only [wp] at h_wp
  obtain ⟨ trProofEnd, h_wp ⟩ := h_wp
  exists trProofEnd
  grind

public
theorem Trace.apply_Reachable_implies_Invariant
  {config: ReachabilityConfig}
  [inst: ReachableImpliesInvariant config]
  {p: ExecTrace → Prop}
  : (
      ∀ trProof: ProofTrace,
        trProof.Invariant →
        p trProof.erase
    ) → (
      ∀ trExec: ExecTrace,
        trExec.Reachable config →
        p trExec
    )
:= by
  intro h trExec h_reach
  grind [Trace.Reachable_implies_Invariant config trExec h_reach]

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $_options* ReachabilityTheorem $params* from $sources,*) => do
    let sources := sources.getElems

    let combined ← combineTypeclass params sources  <| .makeSimple {
      refereeName := `reachability
      combineName := ``DY.ReachabilityConfig.combine
      outTypeName := ``DY.ReachableImpliesInvariant
    }

    return Lean.mkNullNode (combined)

end Meta.CombineMacro

end DY
