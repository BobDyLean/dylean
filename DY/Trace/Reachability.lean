module

public import DY.Trace.Monad
public meta import DY.Meta.CombineMacro

namespace DY

variable [ExecTrace.Def]

public
structure TransitionSystem where
  Input: Type
  PreCond: Input → ExecTrace → Prop
  step: Input → (Output: Type) × Traceful Output

public
abbrev TransitionSystem.make
  {α β: Type}
  (step: α → Traceful β)
  : TransitionSystem
where
  Input := α
  PreCond _ _ := True
  step x := ⟨ _, step x ⟩

@[expose]
public
def TransitionSystem.combine {α: Type} (configs: α → TransitionSystem): TransitionSystem where
  Input := (x: α) × (configs x).Input
  PreCond := fun ⟨ x, inp ⟩ tr => (configs x).PreCond inp tr
  step := fun ⟨ x, inp ⟩ => (configs x).step inp

public
class TransitionSystem.HasStep (config1: TransitionSystem) (config2: semiOutParam TransitionSystem) where
  inj: config1.Input → config2.Input
  pf_pre: ∀ input tr, config1.PreCond input tr = config2.PreCond (inj input) tr
  pf_step: ∀ input, config1.step input = config2.step (inj input)

public
class TransitionSystem.Has (config1 config2: TransitionSystem) where
  inj: config1.Input → config2.Input
  pf_pre: ∀ input tr, config1.PreCond input tr = config2.PreCond (inj input) tr
  pf_step (config1 config2): ∀ input, config1.step input = config2.step (inj input)

public
instance instTransitionSystemHasItself
  (config: TransitionSystem)
  : TransitionSystem.Has config config
where
  inj x := x
  pf_pre input tr := by simp
  pf_step input := by simp

public
instance instTransitionSystemHasStep
  (config1 config2 config3: TransitionSystem)
  [inst12: TransitionSystem.HasStep config1 config2]
  [inst23: TransitionSystem.Has config2 config3]
  : TransitionSystem.Has config1 config3
where
  inj x := inst23.inj (inst12.inj x)
  pf_pre input tr := by simp [inst23.pf_pre, inst12.pf_pre]
  pf_step input := by simp [inst23.pf_step, inst12.pf_step]

public
instance instTransitionSystemCombineHasStep
  {n: Nat}
  (configs: Fin n → TransitionSystem)
  (id: Fin n)
  : TransitionSystem.HasStep (configs id) (.combine configs)
where
  inj x := ⟨ id, x ⟩
  pf_pre input tr := by simp [TransitionSystem.combine]
  pf_step input := by simp [TransitionSystem.combine]

public
inductive Trace.Reachable (config: TransitionSystem): ExecTrace → Prop where
  | Base:
    Trace.Reachable config Trace.empty
  | Step:
    {tr: ExecTrace} →
    (input: config.Input) →
    config.PreCond input tr →
    Trace.Reachable config tr →
    Trace.Reachable config (((config.step input).snd).run tr).snd

-- Weakest Precondition
@[expose]
public
def Traceful.PreservesReachabilityFrom
  {a: Type}
  (config: TransitionSystem)
  (f: Traceful a)
  (post: a → ExecTrace → Prop)
  (tr: ExecTrace): Prop
:=
  let (optRes, trOut) := Traceful.run f tr
  Trace.Reachable config trOut ∧
  match optRes with
  | none => True
  | some res => post res trOut

-- Hoare Triple
@[expose]
public
def Traceful.PreservesReachability
  {a: Type}
  (config: TransitionSystem)
  (f: Traceful a)
  (pre: ExecTrace → Prop)
  (post: a → ExecTrace → Prop)
  : Prop
:=
  ∀ tr,
    tr.Reachable config →
    pre tr →
    f.PreservesReachabilityFrom config post tr

public
theorem Traceful.PreservesReachabilityFrom_bind
  {a b: Type}
  (config: TransitionSystem)
  (x: Traceful a) (f: a → Traceful b)
  (postF: b → ExecTrace → Prop)
  (preX: ExecTrace → Prop)
  (postX: a → ExecTrace → Prop)
  (tr: ExecTrace)
  (h_x: x.PreservesReachability config preX postX)
  (h_tr_reachable: tr.Reachable config)
  (h_pre_x: preX tr)
  (h_f: ∀ x':a, ∀ trMid: ExecTrace,
      postX x' trMid →
      trMid.Reachable config →
      tr ≤ trMid →
      (f x').PreservesReachabilityFrom config postF trMid
  )
  : (x >>= f).PreservesReachabilityFrom config postF tr
:= by
  simp_all only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, Traceful.run_bind]
  grind

public
theorem Traceful.PreservesReachability_base
  (subConfig config: TransitionSystem)
  [TransitionSystem.Has subConfig config]
  (input: subConfig.Input)
  : (subConfig.step input).snd.PreservesReachability config (subConfig.PreCond input) (fun _ _ => True)
:= by
  dsimp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom]
  intro tr h_reach h_pre
  apply And.intro
  · rewrite [TransitionSystem.Has.pf_step subConfig config]
    apply Trace.Reachable.Step (TransitionSystem.Has.inj input) <;>
    grind [TransitionSystem.Has.pf_pre]
  · grind

public
theorem Traceful.PreservesReachabilityFrom_pure
  {α: Type}
  (config: TransitionSystem)
  (x: α)
  (tr: ExecTrace)
  (post: α → ExecTrace → Prop)
  : tr.Reachable config →
    post x tr →
    (pure x: Traceful α).PreservesReachabilityFrom config post tr
:= by
  simp only [Traceful.PreservesReachabilityFrom, Traceful.run_pure]
  grind

public
theorem Traceful.PreservesReachability_to_Reachable
  {a: Type}
  {config: TransitionSystem}
  {f: Traceful a}
  {pre: ExecTrace → Prop}
  {post: a → ExecTrace → Prop}
  (h: f.PreservesReachability config pre post)
  : pre Trace.empty →
    (f.run Trace.empty).snd.val.Reachable config
:= by
  simp_all [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom]
  have := h Trace.empty (.Base)
  grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $_options* TransitionSystem $params* from $sources,*) => do
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `transitionSystem
      combineName := ``DY.TransitionSystem.combine
      internalOutTypeStx := fun _ _ => `(term| TransitionSystem)
      outTypeStx := fun _ => `(term| TransitionSystem)
      isTheorem := false
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `transitionSystem
      combineName := ``DY.TransitionSystem.combine
      hasStepName := ``DY.TransitionSystem.HasStep
    }

    return Lean.mkNullNode (combined ++ hasStep)

end Meta.CombineMacro

end DY
