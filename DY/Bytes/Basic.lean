/-
  This module defines the type for symbolic bytes,
  and allows doing so modularly (or "à la carte").
  It is mostly a thin wrapper around `DY.ALaCarte.ContainerFor`, but more opinionated.
  In particular, we require symbolic bytes to have `DecidableEq` and to have an order.
  Furthermore, at any point in a Lean file,
  it never makes sense to work with two different types for symbolic bytes.
  We capture this with the argumentless typeclass `Bytes.Def`
  that captures *the* set of constructors in the symbolic bytes term
  we are currently working with in this context.
-/

module

public import DY.ALaCarte.Basic
public import DY.ALaCarte.DecidableEq
public import DY.ALaCarte.Ordering
public meta import DY.Meta.CombineMacro
-- transitively import to check its proofs,
-- not as a real dependency
import DY.Bytes.NormalizationMetaTheory

namespace DY

public
class Bytes.Part (SubF: Type → Type) where
  [sizeOf: ALaCarte.FunctorSizeOf SubF]
  [repr: ALaCarte.Representable SubF]
  [deq: ALaCarte.RepresentableDecidableEq SubF]
  [ord: ALaCarte.RepresentableOrd SubF]

public instance (SubF: Type → Type) [inst: Bytes.Part SubF]: ALaCarte.FunctorSizeOf SubF := inst.sizeOf
public instance (SubF: Type → Type) [inst: Bytes.Part SubF]: ALaCarte.Representable SubF := inst.repr
public instance (SubF: Type → Type) [inst: Bytes.Part SubF]: ALaCarte.RepresentableDecidableEq SubF := inst.deq
public instance (SubF: Type → Type) [inst: Bytes.Part SubF]: ALaCarte.RepresentableOrd SubF := inst.ord

public
class Bytes.Def where
  whole: Type → Type
  [part: Bytes.Part whole]

/-- The global functor of symbolic bytes. -/
public
abbrev Bytes.Functor [Bytes.Def]: Type → Type := Bytes.Def.whole

public instance [inst: Bytes.Def]: Bytes.Part Bytes.Functor := inst.part

-- Sanity checks

example [inst: Bytes.Def]: ALaCarte.FunctorSizeOf Bytes.Functor := inferInstance
example [inst: Bytes.Def]: ALaCarte.Representable Bytes.Functor := inferInstance
example [inst: Bytes.Def]: ALaCarte.RepresentableDecidableEq Bytes.Functor := inferInstance
example [inst: Bytes.Def]: ALaCarte.RepresentableOrd Bytes.Functor := inferInstance

variable [Bytes.Def]

-- We want to prevent DefEq abuse with Bytes,
-- but on the other hand we cannot box it into a `structure`
-- because we need defeq when dealing with `SubF Bytes`.
-- Furthermore, we need to expose definition because of compiler stuff,
-- hence this defeq abuse leaks to downstream modules.
-- As a middle ground, we mark it irreducible.
@[irreducible, expose]
public
def Bytes := ALaCarte.ContainerFor Bytes.Functor

-- In this file, we need to "defeq abuse" the definition of Bytes.
-- However, outside this file, it should not be needed.
attribute [local semireducible] Bytes

public
noncomputable
instance: SizeOf Bytes := inferInstanceAs (SizeOf (ALaCarte.ContainerFor Bytes.Functor))

public instance: DecidableEq Bytes := inferInstanceAs (DecidableEq (ALaCarte.ContainerFor Bytes.Functor))

public instance: Ord Bytes := inferInstanceAs (Ord (ALaCarte.ContainerFor Bytes.Functor))
public instance: Std.ReflOrd Bytes := inferInstanceAs (Std.ReflOrd (ALaCarte.ContainerFor Bytes.Functor))
public instance: Std.LawfulEqOrd Bytes := inferInstanceAs (Std.LawfulEqOrd (ALaCarte.ContainerFor Bytes.Functor))
public instance: Std.OrientedOrd Bytes := inferInstanceAs (Std.OrientedOrd (ALaCarte.ContainerFor Bytes.Functor))
public instance: Std.TransOrd Bytes := inferInstanceAs (Std.TransOrd (ALaCarte.ContainerFor Bytes.Functor))

public instance: LE Bytes := LE.ofOrd Bytes
public instance: Std.IsLinearOrder Bytes := Std.IsLinearOrder.of_ord

public
class Bytes.HasStep (SubF1: Type → Type) (SubF2: semiOutParam (Type → Type)) [Bytes.Part SubF1] [semiOutParam (Bytes.Part SubF2)] extends ALaCarte.SubFunctor SubF1 SubF2

public
class Bytes.Has (SubF: Type → Type) [Bytes.Part SubF] extends ALaCarte.SubFunctorTC SubF Bytes.Functor

-- To avoid instance name clashing with other files
namespace Bytes.Def

public instance: Bytes.Has Bytes.Functor where
public instance
  (SubF1 SubF2: Type → Type)
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  [Bytes.Has SubF2]
  : Bytes.Has SubF1
where

end Bytes.Def

public
abbrev Bytes.combine {n: Nat} (SubFs: Fin n → Type → Type): Type → Type :=
  ALaCarte.FunctorUnion SubFs

public instance {n: Nat} (SubFs: Fin n → Type → Type) [∀ id, Bytes.Part (SubFs id)]: Bytes.Part (Bytes.combine SubFs) where

public instance
  {n: Nat}
  (SubFs: Fin n → Type → Type) [∀ id, Bytes.Part (SubFs id)]
  (id: Fin n)
  : Bytes.HasStep (SubFs id) (Bytes.combine SubFs)
where

public
abbrev BytesView (SubF: Type → Type) := SubF Bytes

public
def Bytes.view? (b: Bytes) (SubF: Type → Type) [Bytes.Part SubF] [Bytes.Has SubF] : Option (BytesView SubF) :=
  ALaCarte.Container.view SubF b

public
def BytesView.pack
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  (b: BytesView SubF)
  : Bytes
:=
  ALaCarte.Container.pack SubF b

public
theorem Bytes.pack_view?
  (SubF: Type → Type) [Bytes.Part SubF] [Bytes.Has SubF]
  (b: Bytes)
  :
  match b.view? SubF with
  | some bview => bview.pack = b
  | none => True
:= by
  have := ALaCarte.Container.pack_view SubF b
  simp only [BytesView.pack, Bytes.view?]
  split <;> simp_all

grind_pattern Bytes.pack_view? => b.view? SubF

public
theorem BytesView.view_pack
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  (b: BytesView SubF)
  : (b.pack).view? SubF = some b
:= by
  exact ALaCarte.Container.view_pack SubF b

grind_pattern BytesView.view_pack => b.pack

public
theorem Bytes.sizeOf_view
  (SubF: Type → Type) [Bytes.Part SubF] [Bytes.Has SubF]
  (b: Bytes)
  :
  match b.view? SubF with
  | some bview => DY.ALaCarte.FunctorSizeOf.sizeOf bview ≤ sizeOf b
  | none => True
:= by
  simp only [Bytes.view?]
  split
  · have := ALaCarte.Container.sizeOf_view SubF b
    simp only [*] at this
    exact this
  · grind

grind_pattern Bytes.sizeOf_view => b.view? SubF

-- Unfolding of `ALaCarte.Container.PartialFun SubF Bytes.Functor a` that use the type `Bytes` instead of `ContainerFor Bytes.Functor`,
-- and with an autoParam to prove well-founded recursion automatically.
public
abbrev Bytes.Function.Part (SubF: Type → Type) [Bytes.Part SubF] (a: Type) :=
  ∀ x: SubF Bytes, (∀ y: Bytes, (h: sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x := by simp_all +arith [DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind) → a) → a

public
abbrev Bytes.Function (a: Type) := Bytes.Function.Part Bytes.Functor a

public
def Bytes.rec {a: Type} (f: Bytes.Function a) (x: Bytes) : a :=
  ALaCarte.Container.rec f x

public
class Bytes.Function.HasStep
  {SubF1 SubF2: Type → Type} {a: Type}
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  (partialFun1: Bytes.Function.Part SubF1 a)
  (partialFun2: semiOutParam (Bytes.Function.Part SubF2 a))
where
  [toALaCarte: ALaCarte.SubPartialFun partialFun1 partialFun2]

attribute [local instance] Bytes.Function.HasStep.toALaCarte

public
class Bytes.Function.Has
  {SubF: Type → Type}
  [Bytes.Part SubF] [Bytes.Has SubF]
  {a: Type}
  (partialFun: Bytes.Function.Part SubF a)
  (totalFun: Bytes.Function a)
where
  [toALaCarte: ALaCarte.SubPartialFunTC partialFun totalFun]

attribute [local instance] Bytes.Function.Has.toALaCarte

public
instance
  {a: Type}
  (totalFun: Bytes.Function a)
  : Bytes.Function.Has totalFun totalFun
where
  toALaCarte := DY.ALaCarte.instSubPartialFunTC_refl _

public
instance
  {SubF1 SubF2: Type → Type}
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  [Bytes.Has SubF2]
  {a: Type}
  (partialFun1: Bytes.Function.Part SubF1 a)
  (partialFun2: Bytes.Function.Part SubF2 a)
  (totalFun: Bytes.Function a)
  [Bytes.Function.HasStep partialFun1 partialFun2]
  [Bytes.Function.Has partialFun2 totalFun]
  : Bytes.Function.Has partialFun1 totalFun
where
  toALaCarte := DY.ALaCarte.instSubPartialFunTC_trans _ partialFun2 _

public
def Bytes.Function.combine
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  {a: Type}
  (funs: (id: Fin n) → Bytes.Function.Part (SubFs id) a)
  : Bytes.Function.Part (Bytes.combine SubFs) a
:=
  ALaCarte.Container.PartialFun.combine funs

public
instance
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  {a: Type}
  (funs: (id: Fin n) → Bytes.Function.Part (SubFs id) a)
  (id: Fin n)
  : Bytes.Function.HasStep (funs id) (Bytes.Function.combine funs)
where
  toALaCarte := DY.ALaCarte.instSubPartialFun_combine _ _

public
theorem Bytes.rec_eq
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  {a: Type}
  (partialFun: Bytes.Function.Part SubF a)
  (totalFun: Bytes.Function a)
  [Bytes.Function.Has partialFun totalFun]
  (x: BytesView SubF)
  : x.pack.rec totalFun = partialFun x (fun y _ => y.rec totalFun)
:=
  ALaCarte.Container.rec_eq partialFun totalFun x

-- Unfolding of `ALaCarte.Container.PartialProof1 fn rec p` that use the type `Bytes` instead of `ContainerFor Bytes.Functor`
@[expose]
public
def Bytes.Proof1.Part {SubF: Type → Type} [Bytes.Part SubF] {a: Type} (fn: Bytes.Function.Part SubF a) (rec: Bytes → a) (p: a → Prop) :=
  ∀ x: SubF Bytes, (∀ y: Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → p (rec y)) → p (fn x (fun y _ => rec y))

@[expose]
public
def Bytes.Proof1 {a: Type} (fn: Bytes.Function a) (p: a → Prop) := Bytes.Proof1.Part fn (Bytes.rec fn) p

public
theorem Bytes.Proof1.prove
  {a: Type}
  {fn: Bytes.Function a}
  {p: a → Prop}
  (pf: Bytes.Proof1 fn p)
  (x: Bytes)
  : p (x.rec fn)
:=
  ALaCarte.Container.rec (ALaCarte.Container.PartialProof1.into pf) x

public
theorem Bytes.Proof1.combine
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  {a: Type}
  {funs: (id: Fin n) → Bytes.Function.Part (SubFs id) a}
  {rec: Bytes → a} {p: a → Prop}
  (pfs: (id: Fin n) → Bytes.Proof1.Part (funs id) rec p)
  : Bytes.Proof1.Part (Bytes.Function.combine funs) rec p
:=
  ALaCarte.Container.PartialProof1.combine pfs

-- Unfolding of `ALaCarte.Container.PartialProof2 fn1 fn2 rec1 rec2 p` that use the type `Bytes` instead of `ContainerFor Bytes.Functor`
@[expose]
public
def Bytes.Proof2.Part {SubF: Type → Type} [Bytes.Part SubF] {a b: Type} (fn1: Bytes.Function.Part SubF a) (fn2: Bytes.Function.Part SubF b) (rec1: Bytes → a) (rec2: Bytes → b) (p: a × b → Prop) :=
  ∀ x: SubF Bytes, (∀ y: Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → p (rec1 y, rec2 y)) → p (fn1 x (fun y _ => rec1 y), fn2 x (fun y _ => rec2 y))

@[expose]
public
def Bytes.Proof2 {a b: Type} (fn1: Bytes.Function a) (fn2: Bytes.Function b) (p: a × b → Prop) := Bytes.Proof2.Part fn1 fn2 (Bytes.rec fn1) (Bytes.rec fn2) p

public
theorem Bytes.Proof2.prove
  {a b: Type}
  {fn1: Bytes.Function a}
  {fn2: Bytes.Function b}
  {p: a × b → Prop}
  (pf: Bytes.Proof2 fn1 fn2 p)
  (x: Bytes)
  : p (x.rec fn1, x.rec fn2)
:=
  ALaCarte.Container.rec (ALaCarte.Container.PartialProof2.into pf) x

public
theorem Bytes.Proof2.combine
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  {a: Type} {b: Type}
  {funs1: (id: Fin n) → Bytes.Function.Part (SubFs id) a}
  {funs2: (id: Fin n) → Bytes.Function.Part (SubFs id) b}
  {rec1: Bytes → a} {rec2: Bytes → b} {p: a × b → Prop}
  (pfs: (id: Fin n) → Bytes.Proof2.Part (funs1 id) (funs2 id) rec1 rec2 p)
  : Bytes.Proof2.Part (Bytes.Function.combine funs1) (Bytes.Function.combine funs2) rec1 rec2 p
:=
  ALaCarte.Container.PartialProof2.combine pfs

public
class Bytes.length.Def where
  whole: Bytes.Function Nat

public
def Bytes.length [Bytes.length.Def] (b: Bytes): Nat :=
  Bytes.rec Bytes.length.Def.whole b

public
abbrev Bytes.length.Part [Bytes.Def] (SubF: Type → Type) [Bytes.Part SubF] := Bytes.Function.Part SubF Nat

public
class Bytes.length.HasStep
  {SubF1 SubF2: Type → Type}
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  (partialLength1: outParam (Bytes.length.Part SubF1))
  (partialLength2: Bytes.length.Part SubF2)
  extends Bytes.Function.HasStep partialLength1 partialLength2

public
class Bytes.length.Has
  [Bytes.length.Def]
  {SubF: Type → Type}
  [Bytes.Part SubF]
  [Bytes.Has SubF]
  (binv: outParam (Bytes.length.Part SubF))
  extends Bytes.Function.Has binv Bytes.length.Def.whole

public
abbrev Bytes.length.combine
  {n: Nat}
  {SubFs: Fin n → Type → Type} [∀ id, Bytes.Part (SubFs id)]
  (lens: ∀ id, Bytes.length.Part (SubFs id))
  : Bytes.length.Part (Bytes.combine SubFs)
:=
  Bytes.Function.combine lens

namespace Bytes.length.Def

public
instance [Bytes.length.Def]: Bytes.length.Has (Bytes.length.Def.whole) where

public
instance
  [Bytes.length.Def]
  {SubF1 SubF2: Type → Type}
  [Bytes.Part SubF1] [Bytes.Part SubF2]
  [Bytes.HasStep SubF1 SubF2]
  [Bytes.Has SubF2]
  (partialLen1: Bytes.length.Part SubF1)
  (partialLen2: Bytes.length.Part SubF2)
  [inst1: Bytes.length.HasStep partialLen1 partialLen2]
  [inst2: Bytes.length.Has partialLen2]
  : Bytes.length.Has partialLen1
where

public
instance
  {n: Nat}
  (SubFs: Fin n → Type → Type) [∀ id, Bytes.Part (SubFs id)]
  (invs: ∀ id, Bytes.length.Part (SubFs id))
  (id: Fin n)
  : Bytes.length.HasStep (invs id) (Bytes.length.combine invs)
where

end Bytes.length.Def

@[simp]
public
theorem Bytes.length.eq
  {SubF: Type → Type} [Bytes.Part SubF] [Bytes.Has SubF]
  [Bytes.length.Def]
  {subLength: Bytes.length.Part SubF}
  [Bytes.length.Has subLength]
  (b: BytesView SubF)
  : b.pack.length = subLength b (fun y _ => y.length)
:= by
  apply Bytes.rec_eq

grind_pattern Bytes.length.eq => b.pack.length

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* Bytes $params* from $sources,*) => do
    let options := parseOptions options
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `BytesPart.Functor
      combineName := ``DY.Bytes.combine
      internalOutTypeStx := fun _ _ => `(term| Type → Type)
      outTypeStx := fun _ => `(term| Type → Type)
      isTheorem := false
    }

    let typeclass ← combineTypeclass params sources <| .makeSimple {
      refereeName := `BytesPart.Functor
      combineName := ``DY.Bytes.combine
      outTypeName := ``DY.Bytes.Part
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `BytesPart.Functor
      combineName := ``DY.Bytes.combine
      hasStepName := ``DY.Bytes.HasStep
    }

    let subfStx := Lean.mkIdent `BytesPart.Functor
    let topLevelInst ← `(command| public instance: DY.Bytes.Def where whole := $subfStx)
    let topLevelHas ← `(command| public instance: DY.Bytes.Has $subfStx := inferInstanceAs (DY.Bytes.Has DY.Bytes.Functor))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ typeclass ++ hasStep ++ topLevel)

macro_rules
  | `(command| #combine_one $options* Bytes.length $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.Bytes.Def]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources  <| .makeSimple {
      name := `BytesPart.length
      refereeName := `BytesPart.Functor
      combineName := ``DY.Bytes.length.combine
      outTypeName := `DY.Bytes.length.Part
      isTheorem := false
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `BytesPart.length
      combineName := ``DY.Bytes.length.combine
      hasStepName := ``DY.Bytes.length.HasStep
    }

    let lengthStx := Lean.mkIdent `BytesPart.length
    let topLevelInst ← `(command| public instance: DY.Bytes.length.Def where whole := $lengthStx)
    let topLevelHas ← `(command| public instance: DY.Bytes.length.Has $lengthStx := inferInstanceAs (DY.Bytes.length.Has DY.Bytes.length.Def.whole))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel)

end Meta.CombineMacro

end DY
