module

import DY.Actions.LongTermKeys

namespace DY.Tests.HasElaborator

-- simple test of `has%`: expansion is what we expect
example [Bytes.Def]: Bytes has% Random = Bytes.Has Random.BytesPart.Functor := by with_reducible rfl
example [ExecTrace.Def]: ExecTrace has% Random = ExecTrace.Has Random.TracePart.Exec := by with_reducible rfl

-- same tests with explicit namespace `DY`
example [Bytes.Def]: DY.Bytes has% Random = Bytes.Has Random.BytesPart.Functor := by with_reducible rfl
example [ExecTrace.Def]: DY.ExecTrace has% Random = ExecTrace.Has Random.TracePart.Exec := by with_reducible rfl

-- test modules with parameters
example [Bytes.Def] [ExecTrace.Def] (name: String): ExecTrace has% LongTermKeys name = ExecTrace.Has (LongTermKeys.TracePart.Exec name) := by with_reducible rfl

-- unspaced modulo on identifiers is unaffected
example (n m: Nat): n%m = n % m := rfl

/-- error: `DY.Bytes.Function.Has` has no registered convention: it must be tagged with `@[has_suffix ...]` -/
#guard_msgs in
example [Bytes.Def] [Bytes.Function has% Random]: True := True.intro

/-- error: Unknown constant `Byte.Has` -/
#guard_msgs in
example [Bytes.Def] [Byte has% Random]: True := True.intro

-- the convention can be declared for new typeclasses
@[has_suffix MyPart]
class My.Has (n: Nat) where

def Foo.MyPart: Nat := 0

example: My has% Foo = My.Has Foo.MyPart := by with_reducible rfl

end DY.Tests.HasElaborator
