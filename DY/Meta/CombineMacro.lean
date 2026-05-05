/-
  DyLean comes with several mechanisms to allow for modular specifications and proofs.
  These mechanisms share a similar structure,
  where a list of Xs can be combined together using X.combine,
  and the fact that a local X is part of a global X
  is proved via a combo of typeclasses HasStep / Has.

  When using these modular mechanisms,
  DyLean users may have to write by hand substantial amount boilerplate code.

  To relieve DyLean users from this burden,
  we provide in this module a macro `#combine` that automates this work.
  When we define a new modular mechanism that follows the paradigm combine / HasStep,
  we can plug into the `#combine` macro by defining a new macro rule for `#combine_one`,
  and can rely on the following helper functions:
  - `combineExplicit` for explicit calls to X.combine
  - `combineTypeclass` for implicit combination through a typeclass
  - `mkHasStep` to derive X.HasStep instances
  - `mkHasCombine` to derive a top-level X.Has instance
-/
module

import Lean

open Lean Syntax

namespace DY.Meta.CombineMacro

public meta
def explicitNameOfBracketedBinder (stx: TSyntax `Lean.Parser.Term.bracketedBinder): TSyntaxArray `ident :=
  match stx with
  | `(bracketedBinder|($ids* $[: $ty?]? $(_annot?)?)) =>
    (ids.map (fun x =>
      -- assume there is no hole
      -- (this will raise an error message somewhere later, but maybe we can fail more nicely?)
      (⟨ x.raw ⟩: TSyntax `ident)
    ))
  | _  => #[]

declare_syntax_cat combine_from
syntax ident term:arg*: combine_from

declare_syntax_cat combine_into
syntax ident bracketedBinder*: combine_into

declare_syntax_cat combine_option
syntax "+toplevel ": combine_option

syntax "#combine_one " combine_option* combine_into " from " combine_from,*,? : command

syntax "#combine " combine_option* bracketedBinder* " into " combine_into,*,? " from " combine_from,*,? : command

public meta
structure CombineExplicitConfig where
  name: Name
  combineName: Name
  -- e.g. Foo (Bar.internal $args* $id)
  internalOutTypeStx: (args: TSyntaxArray `term) → (id: TSyntax `term) → MacroM (TSyntax `term)
  -- e.g. Foo (Bar $args*)
  outTypeStx: (args: TSyntaxArray `term) → MacroM (TSyntax `term)

public meta
structure CombineExplicitSimpleConfig where
  name: Name
  refereeName: Name
  combineName: Name
  outTypeName: Name

public meta
def CombineExplicitConfig.makeSimple (config: CombineExplicitSimpleConfig): CombineExplicitConfig :=
  let refStx := Lean.mkIdent config.refereeName
  let refInternalStx := Lean.mkIdent (config.refereeName ++ `internal)
  let outTypeStx := Lean.mkIdent config.outTypeName
  {
    name := config.name
    combineName := config.combineName
    internalOutTypeStx := fun args id =>
      `(term| $outTypeStx ($refInternalStx $args* $id))
    outTypeStx := fun args =>
      `(term| $outTypeStx ($refStx $args*))
  }

public meta
def combineExplicit (params: TSyntaxArray `Lean.Parser.Term.bracketedBinder) (sources: TSyntaxArray `combine_from) (config: CombineExplicitConfig): MacroM (TSyntaxArray `command) := do
  let argsTarget := params.flatMap explicitNameOfBracketedBinder

  let mut arms := #[]
  for i in [:sources.size] do
    let `(combine_from| $nameSource:ident $argsSource* ) := sources[i]! | panic! "??"
    let fullIdSource := mkIdentFrom nameSource <| nameSource.getId.modifyBase (. ++ config.name)
    let arm ← `(Parser.Term.matchAltExpr| | $(quote i) => $fullIdSource $argsSource*)
    arms := arms.push arm

  let nSourcesStx: TSyntax `term := quote sources.size
  let internalNameStx := mkIdent (config.name ++ `internal)
  let internalOutTypeStx ← config.internalOutTypeStx argsTarget (← `(ident| id))
  let defInternalStx ← `(command|
    @[expose]
    public
    def $internalNameStx $params*: (id: Fin $nSourcesStx) → $internalOutTypeStx := fun $arms:matchAlt*
  )

  let nameStx := mkIdent config.name
  let combineStx := mkIdent config.combineName
  let outTypeStx ← config.outTypeStx argsTarget
  let defStx ← `(command|
    @[expose, implicit_reducible]
    public
    def $nameStx $params*: $outTypeStx := $combineStx ($internalNameStx $argsTarget*)
  )

  return #[defInternalStx, defStx]

public meta
structure CombineTypeclassConfig where
  -- e.g. Tc (Foo.internal $args* $id)
  internalIdStx: (args: TSyntaxArray `term) → (id: TSyntax `term) → MacroM (TSyntax `term)
  -- e.g. Tc ($name.Foo $args*)
  internalStx: (name: TSyntax `ident) → (args: TSyntaxArray `term) → MacroM (TSyntax `term)
  -- e.g. Tc (FooFoo.combine (Foo.internal $args*))
  combineStx: (args: TSyntaxArray `term) → MacroM (TSyntax `term)
  -- e.g. Tc (Foo $args*)
  finalStx: (args: TSyntaxArray `term) → MacroM (TSyntax `term)
  useInferInstanceAs: Bool := true

public meta
structure CombineTypeclassSimpleConfig where
  -- e.g. Foo
  refereeName: Name
  -- e.g. Foo.internal
  refereeInternalName: Name := refereeName ++ `internal
  -- e.g. FooFoo.combine
  combineName: Name
  -- e.g. Tc
  outTypeName: Name
  useInferInstanceAs: Bool := true

public meta
def CombineTypeclassConfig.makeSimple (config: CombineTypeclassSimpleConfig): CombineTypeclassConfig :=
  let refStx := Lean.mkIdent config.refereeName
  let refInternalStx := Lean.mkIdent config.refereeInternalName
  let combineStx := Lean.mkIdent config.combineName
  let outTypeStx := Lean.mkIdent config.outTypeName
  {
    internalIdStx args id := `(term| $outTypeStx ($refInternalStx $args* $id))
    internalStx name args := do
      let internalFooStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ config.refereeName)
      `(term| $outTypeStx ($internalFooStx $args*))
    combineStx args := `(term| $outTypeStx ($combineStx ($refInternalStx $args*)))
    finalStx args := `(term| $outTypeStx ($refStx $args*))
    useInferInstanceAs := config.useInferInstanceAs
  }

public meta
def combineTypeclass (params: TSyntaxArray `Lean.Parser.Term.bracketedBinder) (sources: TSyntaxArray `combine_from) (config: CombineTypeclassConfig): MacroM (TSyntaxArray `command) := do
  let argsTarget := params.flatMap explicitNameOfBracketedBinder

  let mut arms := #[]
  for i in [:sources.size] do
    let `(combine_from| $nameSource:ident $argsSource* ) := sources[i]! | panic! "??"
    let internalStx ← config.internalStx nameSource argsSource
    let armStxAux ←
      if config.useInferInstanceAs then
        `(term| inferInstanceAs ($internalStx))
      else
        -- option to work around issue in SubBaseAttackerKnowledgeTheorem
        `(term| (inferInstance: ($internalStx)))
    let arm ← `(Parser.Term.matchAltExpr| | $(quote i) => $armStxAux)
    arms := arms.push arm

  let freshInstanceInternalName ← withFreshMacroScope `(declId| wfInstInternal)
  let outTypeInternalStx ← config.internalIdStx argsTarget (← `(ident| id))
  let wfStxInternal ← `(command|
    @[expose, implicit_reducible, instance]
    public
    def $freshInstanceInternalName $params*: ∀ id, $outTypeInternalStx
      $arms:matchAlt*
  )

  let freshInstanceName ← withFreshMacroScope `(declId| wfInst)
  let outTypeStx ← config.finalStx argsTarget
  let combineTypeStx ← config.combineStx argsTarget
  let wfStxAux ←
    if config.useInferInstanceAs then
      `(term| inferInstanceAs ($combineTypeStx))
    else
      -- option to work around issue in SubBaseAttackerKnowledgeTheorem
      `(term| (inferInstance: ($combineTypeStx)))
  let wfStx ← `(command|
    @[expose, implicit_reducible, instance]
    public
    def $freshInstanceName $params*: $outTypeStx :=
      $wfStxAux
  )

  return #[wfStxInternal, wfStx]

public meta
structure HasStepConfig where
  -- e.g. HasStep (Foo.internal $args* $id) (FooFoo.combine (Foo.internal $args*))
  sourceInstanceStx: (args: TSyntaxArray `term) → (id: TSyntax `term) → MacroM (TSyntax `term)
  -- e.g. HasStep ($name.Foo $argsSource*) (Foo $argsTarget)
  targetInstanceStx: (name: TSyntax `ident) → (argsSource argsTarget: TSyntaxArray `term) → MacroM (TSyntax `term)

public meta
structure HasStepSimpleConfig where
  name: Name
  internalName: Name := name ++ `internal
  combineName: Name
  hasStepName: Name

public meta
def HasStepConfig.makeSimple (config: HasStepSimpleConfig): HasStepConfig :=
  let fooInternalStx := Lean.mkIdent config.internalName
  let fooStx := Lean.mkIdent config.name
  let combineStx := Lean.mkIdent config.combineName
  let hasStepStx := Lean.mkIdent config.hasStepName
  {
    sourceInstanceStx args id := `(term| $hasStepStx ($fooInternalStx $args* $id) ($combineStx ($fooInternalStx $args*)))
    targetInstanceStx name argsSource argsTarget :=
      let sourceFooStx := Lean.mkIdentFrom name <| name.getId.modifyBase (. ++ config.name)
      `(term| $hasStepStx ($sourceFooStx $argsSource*) ($fooStx $argsTarget*))
  }

public meta
def mkHasStep (params: TSyntaxArray `Lean.Parser.Term.bracketedBinder) (sources: TSyntaxArray `combine_from) (config: HasStepConfig): MacroM (TSyntaxArray `command) := do
  let argsTarget := params.flatMap explicitNameOfBracketedBinder

  let mut cmds := #[]
  for i in [:sources.size] do
    let `(combine_from| $nameSource:ident $argsSource* ) := sources[i]! | panic! "??"
    let freshInstanceName ← withFreshMacroScope `(declId| inst)
    let hasStepSourceStx ← config.sourceInstanceStx argsTarget (quote i)
    let hasStepTargetStx ← config.targetInstanceStx nameSource argsSource argsTarget
    let inst ← `(command|
      @[expose, implicit_reducible, instance]
      public
      def $freshInstanceName $params* : $hasStepTargetStx :=
        inferInstanceAs ($hasStepSourceStx)
    )
    cmds := cmds.push inst

  return cmds

public meta
structure HasCombineConfig where
  -- e.g. `Has (FooFoo.combine (Foo.internal $args*))`
  hasCombineStx: (args: TSyntaxArray `term) → MacroM (TSyntax `term)
  -- e.g. `Has (Foo $args*)`
  hasStx: (args: TSyntaxArray `term) → MacroM (TSyntax `term)

/-
  This macro allows to derive `Has (Foo.internal id)` from `Has Foo`.
  It is useful in the context of lean4#13571.
  Since this issue only appears when defining top-level instances,
  we only use it in this scenario.
  We currently don't need it when relying on local instances,
  but this is an unintended behavior of Lean that might change in the future.
-/
public meta
def mkHasCombine (params: TSyntaxArray `Lean.Parser.Term.bracketedBinder) (config: HasCombineConfig): MacroM (TSyntaxArray `command) := do
  let argsTarget := params.flatMap explicitNameOfBracketedBinder

  let freshInstanceName ← withFreshMacroScope `(declId| inst)
  let hasCombineStx ← config.hasCombineStx argsTarget
  let hasStx ← config.hasStx argsTarget
  let hasCombineInstStx ← `(command|
      @[expose, implicit_reducible, instance]
      public
      def $freshInstanceName $params* [$hasStx]: $hasCombineStx :=
        inferInstanceAs ($hasStx)
  )
  return #[hasCombineInstStx]


macro_rules
  | `(command| #combine $options:combine_option* $globalParams:bracketedBinder* into $targets,* from $sources,*) => do
    let targets := targets.getElems
    let mut cmds: Array (TSyntax `command) := #[]
    for target in targets do
      let `(combine_into| $id:ident $localParams*) := target
        | panic! "??"
      let params := globalParams ++ localParams
      let combineOneStx ← `(command| #combine_one $options* $id:ident $params* from $sources,*)
      cmds := cmds.push combineOneStx
    return mkNullNode cmds

public meta
structure Options where
  toplevel: Bool := false

public meta
def parseOptions (options: TSyntaxArray `combine_option): Options := Id.run do
  let mut result: Options := {}
  for option in options do
    match option with
    | `(combine_option| +toplevel) =>
      result := { result with toplevel := true }
    | _ => ()
  return result

end DY.Meta.CombineMacro
