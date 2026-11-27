module

public meta import Lean.Elab.Term

open Lean Elab Term

/-!
# `has%` elaborator

DyLean pervasively uses modular definitions.
To express the fact that a definition `D` contains a part `P`,
we use typeclasses of the form `[D.Has P.xxx]`,
where `xxx` is a standard location for parts related to `D`,
that must live in the namespace `P`.
For example:
- `[Bytes.Has Literal.BytesPart.Functor]
- `[ExecTrace.Has Network.TracePart.Exec]

Because we consistently use the same location `xxx` for a given definition `D`,
this module defines the `has%` elaborator,
that allows to instead write:
- `[Bytes has% Literal]
- `[ExecTrace has% Network]

To register the convention for the location `xxx` where live parts of definitions `D`,
this module defines the attribute `@[has_suffix xxx]`.
For example:
```
@[has_suffix BytesPart.Functor]
class Bytes.Has ...
```
-/

namespace DY.Meta.HasElaborator

/--
  `@[has_suffix xxx]` on a typeclass `D.Has` declares that
  `D has% P` can be expanded to `D.Has P.xxx`.
-/
syntax (name := has_suffix) "has_suffix " ident : attr

public meta
initialize hasSuffixAttr: ParametricAttribute Name ←
  registerParametricAttribute {
    name := `has_suffix
    descr := "naming convention for the argument of a `D.Has` typeclass, used by `D has% X`"
    getParam := fun _ stx =>
      match stx with
      | `(attr| has_suffix $suffix:ident) => pure suffix.getId
      | _ => throwError "invalid `has_suffix` attribute, expected `has_suffix suffix`"
  }

/--
  `D has% P arg1 ... argn` is expands to `D.Has (P.xxx arg1 ... argn)`,
  where `xxx` was registered with the attribute `@[has_suffix xxx]`
  on the definition of `D.Has`.
-/
syntax:lead (name := hasElaborator) term:max " has% " ident (ppSpace colGt term:arg)* : term

@[term_elab hasElaborator]
public meta
def elabHas: TermElab := adaptExpander fun stx => do
  let `($d:ident has% $x:ident $args*) := stx
    | throwError "expected `D has% P`, where `D` is the name of a modular definition"
  let clsName ← resolveGlobalConstNoOverload (mkIdentFrom d (d.getId ++ `Has))
  let some suffix := hasSuffixAttr.getParam? (← getEnv) clsName
    | throwErrorAt d "`{clsName}` has no registered convention: it must be tagged with `@[has_suffix ...]`"
  -- set `canonical` to `true`, so that hovering and go-to-definition on `D` points to `D.Has`, and on `P` points to `P.xxx`
  let cls := mkCIdentFrom d clsName (canonical := true)
  let part := mkIdentFrom x (x.getId ++ suffix) (canonical := true)
  `($cls $(Syntax.mkApp part args))

end DY.Meta.HasElaborator
