module

public import DY.Trace.Manipulation
public meta import DY.Meta.CombineMacro

namespace DY

variable [ExecTraceTypes]

public
structure ReachabilityConfig where
  Input: Type
  PreCond: Input → ExecTrace → Prop
  step: Input → (Output: Type) × Traceful Output

public
abbrev ReachabilityConfig.make
  {α β: Type}
  (step: α → Traceful β)
  : ReachabilityConfig
where
  Input := α
  PreCond _ _ := True
  step x := ⟨ _, step x ⟩

@[expose]
public
def ReachabilityConfig.combine {α: Type} (configs: α → ReachabilityConfig): ReachabilityConfig where
  Input := (x: α) × (configs x).Input
  PreCond := fun ⟨ x, inp ⟩ tr => (configs x).PreCond inp tr
  step := fun ⟨ x, inp ⟩ => (configs x).step inp

public
class ReachabilityConfig.HasStep (config1: ReachabilityConfig) (config2: semiOutParam ReachabilityConfig) where
  inj: config1.Input → config2.Input
  pf_pre: ∀ input tr, config1.PreCond input tr = config2.PreCond (inj input) tr
  pf_step: ∀ input, config1.step input = config2.step (inj input)

public
class ReachabilityConfig.Has (config1 config2: ReachabilityConfig) where
  inj: config1.Input → config2.Input
  pf_pre: ∀ input tr, config1.PreCond input tr = config2.PreCond (inj input) tr
  pf_step (config1 config2): ∀ input, config1.step input = config2.step (inj input)

public
instance
  (config: ReachabilityConfig)
  : ReachabilityConfig.Has config config
where
  inj x := x
  pf_pre input tr := by simp
  pf_step input := by simp

public
instance
  (config1 config2 config3: ReachabilityConfig)
  [inst12: ReachabilityConfig.HasStep config1 config2]
  [inst23: ReachabilityConfig.Has config2 config3]
  : ReachabilityConfig.Has config1 config3
where
  inj x := inst23.inj (inst12.inj x)
  pf_pre input tr := by simp [inst23.pf_pre, inst12.pf_pre]
  pf_step input := by simp [inst23.pf_step, inst12.pf_step]

public
instance
  {α: Type}
  (configs: α → ReachabilityConfig)
  (id: α)
  : ReachabilityConfig.HasStep (configs id) (.combine configs)
where
  inj x := ⟨ id, x ⟩
  pf_pre input tr := by simp [ReachabilityConfig.combine]
  pf_step input := by simp [ReachabilityConfig.combine]

public
inductive Trace.ReachableFrom (config: ReachabilityConfig) (trIn: ExecTrace): ExecTrace → Prop where
  | Base:
    Trace.ReachableFrom config trIn trIn
  | Step:
    {trMid: ExecTrace} →
    (input: config.Input) →
    config.PreCond input trMid →
    Trace.ReachableFrom config trIn trMid →
    Trace.ReachableFrom config trIn (Traceful.run ((config.step input).snd) trMid).snd

public
theorem Trace.ReachableFrom_trans
  (config: ReachabilityConfig)
  (tr1 tr2 tr3: ExecTrace)
  : Trace.ReachableFrom config tr1 tr2 →
    Trace.ReachableFrom config tr2 tr3 →
    Trace.ReachableFrom config tr1 tr3
:= by
  intro h12 h23
  induction h23
  · exact h12
  · rename_i trIn trOut input h_input h_reach1 h_reach2
    apply Trace.ReachableFrom.Step input <;> grind

public
def Trace.Reachable (config: ReachabilityConfig) (tr: ExecTrace): Prop :=
  Trace.ReachableFrom config Trace.nil tr

public
def Traceful.PreservesReachabilityFrom {a: Type} (config: ReachabilityConfig) (f: Traceful a) (tr: ExecTrace): Prop :=
    Trace.ReachableFrom config tr (Traceful.run f tr).snd

public
def Traceful.PreservesReachability {a: Type} (config: ReachabilityConfig) (f: Traceful a): Prop :=
  ∀ tr,
    tr.Reachable config →
    Trace.ReachableFrom config tr (Traceful.run f tr).snd

public
theorem Traceful.PreservesReachabilityFrom_bind
  {a b: Type}
  (config: ReachabilityConfig)
  (x: Traceful a) (f: a → Traceful b)
  (tr: ExecTrace)
  : tr.Reachable config →
    x.PreservesReachabilityFrom config tr →
    (∀ x' trMid,
      trMid.Reachable config →
      tr ≤ trMid →
      (f x').PreservesReachabilityFrom config trMid
    ) →
    (x >>= f).PreservesReachabilityFrom config tr
:= by
  intro h_tr h_x h_next
  simp_all only [Traceful.PreservesReachabilityFrom, Traceful.run_bind]
  cases h: (x.run tr).fst
  · simp_all
  · refine Trace.ReachableFrom_trans _ _ (x.run tr).snd _ ?_ ?_
    · grind
    · rename_i val
      refine h_next val (x.run tr).snd ?_ ?_
      · grind [Trace.Reachable, Trace.ReachableFrom_trans]
      · exact (x.run tr).snd.property

public
theorem Traceful.PreservesReachabilityFrom_base
  (subConfig config: ReachabilityConfig)
  [ReachabilityConfig.Has subConfig config]
  (input: subConfig.Input)
  (tr: ExecTrace)
  : subConfig.PreCond input tr →
    (subConfig.step input).snd.PreservesReachabilityFrom config tr
:= by
  intro h_input
  dsimp only [Traceful.PreservesReachabilityFrom]
  rewrite [ReachabilityConfig.Has.pf_step subConfig config]
  apply Trace.ReachableFrom.Step (ReachabilityConfig.Has.inj input)
  · grind [ReachabilityConfig.Has.pf_pre]
  · apply Trace.ReachableFrom.Base

public
theorem Traceful.PreservesReachabilityFrom_pure
  {α: Type}
  (config: ReachabilityConfig)
  (x: α)
  (tr: ExecTrace)
  : (pure x: Traceful α).PreservesReachabilityFrom config tr
:= by
  simp only [Traceful.PreservesReachabilityFrom, Traceful.run_pure]
  apply Trace.ReachableFrom.Base

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $_options* ReachabilityConfig $params* from $sources,*) => do
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `reachability
      combineName := ``DY.ReachabilityConfig.combine
      internalOutTypeStx := fun _ _ => `(term| ReachabilityConfig)
      outTypeStx := fun _ => `(term| ReachabilityConfig)
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `reachability
      combineName := ``DY.ReachabilityConfig.combine
      hasStepName := ``DY.ReachabilityConfig.HasStep
    }

    return Lean.mkNullNode (combined ++ hasStep)

end Meta.CombineMacro

end DY
