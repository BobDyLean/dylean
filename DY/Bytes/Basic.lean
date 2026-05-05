/-
  This module defines the type for symbolic bytes,
  and allows doing so modularly (or "à la carte").
  It is mostly a thin wrapper around `DY.ALaCarte.ContainerFor`, but more opinionated.
  In particular, we require symbolic bytes to have `DecidableEq` and to have an order.
  Furthermore, at any point in a Lean file,
  it never makes sense to work with two different types for symbolic bytes.
  We capture this with the argumentless typeclass `BytesFunctor`
  that captures *the* set of constructors in the symbolic bytes term
  we are currently working with in this context.
-/

module

public import DY.ALaCarte.Basic
public import DY.ALaCarte.DecidableEq
public import DY.ALaCarte.Ordering
public meta import DY.Meta.CombineMacro

namespace DY

public
class SubBytesFunctor (SubF: Type → Type) where
  [sizeOf: ALaCarte.FunctorSizeOf SubF]
  [repr: ALaCarte.Representable SubF]
  [deq: ALaCarte.RepresentableDecidableEq SubF]
  [ord: ALaCarte.RepresentableOrd SubF]

public instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.FunctorSizeOf SubF := inst.sizeOf
public instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.Representable SubF := inst.repr
public instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.RepresentableDecidableEq SubF := inst.deq
public instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.RepresentableOrd SubF := inst.ord

public
class BytesFunctor where
  BytesF: Type → Type
  [inst: SubBytesFunctor BytesF]
export BytesFunctor (BytesF)

public instance [inst: BytesFunctor]: SubBytesFunctor BytesF := inst.inst

-- Sanity checks

example [inst: BytesFunctor]: ALaCarte.FunctorSizeOf BytesF := inferInstance
example [inst: BytesFunctor]: ALaCarte.Representable BytesF := inferInstance
example [inst: BytesFunctor]: ALaCarte.RepresentableDecidableEq BytesF := inferInstance
example [inst: BytesFunctor]: ALaCarte.RepresentableOrd BytesF := inferInstance

variable [BytesFunctor]

-- We want to prevent DefEq abuse with Bytes,
-- but on the other hand we cannot box it into a `structure`
-- because we need defeq when dealing with `SubF Bytes`.
-- As a middle ground, we mark it irreducible.
@[irreducible, expose]
public
def Bytes := ALaCarte.ContainerFor BytesF

-- In this file, we need to "defeq abuse" the definition of Bytes.
-- However, outside this file, it should not be needed.
unseal Bytes

public
noncomputable
instance: SizeOf Bytes := inferInstanceAs (SizeOf (ALaCarte.ContainerFor BytesF))

public instance: DecidableEq Bytes := inferInstanceAs (DecidableEq (ALaCarte.ContainerFor BytesF))

public instance: Ord Bytes := inferInstanceAs (Ord (ALaCarte.ContainerFor BytesF))
public instance: Std.ReflOrd Bytes := inferInstanceAs (Std.ReflOrd (ALaCarte.ContainerFor BytesF))
public instance: Std.LawfulEqOrd Bytes := inferInstanceAs (Std.LawfulEqOrd (ALaCarte.ContainerFor BytesF))
public instance: Std.OrientedOrd Bytes := inferInstanceAs (Std.OrientedOrd (ALaCarte.ContainerFor BytesF))
public instance: Std.TransOrd Bytes := inferInstanceAs (Std.TransOrd (ALaCarte.ContainerFor BytesF))

public instance: LE Bytes := LE.ofOrd Bytes
public instance: Std.IsLinearOrder Bytes := Std.IsLinearOrder.of_ord

public
class BytesFunctor.HasStep (SubF1: Type → Type) (SubF2: semiOutParam (Type → Type)) [SubBytesFunctor SubF1] [semiOutParam (SubBytesFunctor SubF2)] extends ALaCarte.SubFunctor SubF1 SubF2

public
class BytesFunctor.Has (SubF: Type → Type) [SubBytesFunctor SubF] extends ALaCarte.SubFunctorTC SubF BytesF

-- To avoid instance name clashing with other files
namespace BytesFunctor

public instance: BytesFunctor.Has BytesF where
public instance
  (SubF1 SubF2: Type → Type)
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  [BytesFunctor.Has SubF2]
  : BytesFunctor.Has SubF1
where

end BytesFunctor

public
abbrev BytesFunctor.combine {a: Type} (SubFs: a → Type → Type): Type → Type :=
  ALaCarte.FunctorUnion SubFs

public instance {a: Type} [DecidableEq a] [Ord a] [Std.LawfulEqOrd a] [Std.TransOrd a] (SubFs: a → Type → Type) [∀ id, SubBytesFunctor (SubFs id)]: SubBytesFunctor (BytesFunctor.combine SubFs) where

public instance
  {a: Type} [DecidableEq a] [Ord a] [Std.LawfulEqOrd a] [Std.TransOrd a]
  (SubFs: a → Type → Type) [∀ id, SubBytesFunctor (SubFs id)]
  (id: a)
  : BytesFunctor.HasStep (SubFs id) (BytesFunctor.combine SubFs)
where

@[expose]
public
def BytesView (SubF: Type → Type) := SubF Bytes

public
def Bytes.view? (b: Bytes) (SubF: Type → Type) [SubBytesFunctor SubF] [BytesFunctor.Has SubF] : Option (BytesView SubF) :=
  ALaCarte.Container.view SubF b

public
def BytesView.pack
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  (b: BytesView SubF)
  : Bytes
:=
  ALaCarte.Container.pack SubF b

public
theorem Bytes.pack_view?
  (SubF: Type → Type) [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  (b: Bytes)
  :
  match b.view? SubF with
  | some bview => bview.pack = b
  | none => True
:= by
  simp only [BytesView.pack, Bytes.view?]
  grind [ALaCarte.Container.pack_view]

grind_pattern Bytes.pack_view? => b.view? SubF

public
theorem BytesView.view_pack
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  (b: BytesView SubF)
  : (b.pack).view? SubF = some b
:= by
  simp only [BytesView.pack, Bytes.view?, ALaCarte.Container.view_pack]
  rfl

grind_pattern BytesView.view_pack => b.pack

public
theorem Bytes.sizeOf_view
  (SubF: Type → Type) [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
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
  · trivial

grind_pattern Bytes.sizeOf_view => b.view? SubF

-- Unfolding of `ALaCarte.Container.PartialFun SubF BytesF a` that use the type `Bytes` instead of `ContainerFor BytesF`,
-- and with an autoParam to prove well-founded recursion automatically.
@[expose]
public
def Bytes.PartialFunction (SubF: Type → Type) [SubBytesFunctor SubF] (a: Type) :=
  ∀ x: SubF Bytes, (∀ y: Bytes, (h: sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x := by simp_all +arith [DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind) → a) → a

@[expose]
public
def Bytes.Function (a: Type) := Bytes.PartialFunction BytesF a

public
def Bytes.rec {a: Type} (f: Bytes.Function a) (x: Bytes) : a :=
  ALaCarte.Container.rec f x

public
class Bytes.SubFunctionStep
  {SubF1 SubF2: Type → Type} {a: Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  (partialFun1: Bytes.PartialFunction SubF1 a)
  (partialFun2: semiOutParam (Bytes.PartialFunction SubF2 a))
  extends ALaCarte.SubPartialFun partialFun1 partialFun2

public
class Bytes.SubFunction
  {SubF: Type → Type}
  [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  {a: Type}
  (partialFun: Bytes.PartialFunction SubF a)
  (totalFun: Bytes.Function a)
  extends ALaCarte.SubPartialFunTC partialFun totalFun

public
instance
  {a: Type}
  (totalFun: Bytes.Function a)
  : Bytes.SubFunction totalFun totalFun
where

public
instance
  {SubF1 SubF2: Type → Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  [BytesFunctor.Has SubF2]
  {a: Type}
  (partialFun1: Bytes.PartialFunction SubF1 a)
  (partialFun2: Bytes.PartialFunction SubF2 a)
  (totalFun: Bytes.Function a)
  [Bytes.SubFunctionStep partialFun1 partialFun2]
  [Bytes.SubFunction partialFun2 totalFun]
  : Bytes.SubFunction partialFun1 totalFun
where

public
def Bytes.PartialFunction.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type}
  (funs: (id: t) → Bytes.PartialFunction (SubFs id) a)
  : Bytes.PartialFunction (BytesFunctor.combine SubFs) a
:=
  ALaCarte.Container.PartialFun.combine funs

public
instance
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type}
  (funs: (id: t) → Bytes.PartialFunction (SubFs id) a)
  (id: t)
  : Bytes.SubFunctionStep (funs id) (Bytes.PartialFunction.combine funs)
:= by
  unfold Bytes.PartialFunction.combine
  exact {}

public
theorem Bytes.rec_eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  {a: Type}
  (partialFun: Bytes.PartialFunction SubF a)
  (totalFun: Bytes.Function a)
  [Bytes.SubFunction partialFun totalFun]
  (x: BytesView SubF)
  : x.pack.rec totalFun = partialFun x (fun y _ => y.rec totalFun)
:=
  ALaCarte.Container.rec_eq partialFun totalFun x

-- Unfolding of `ALaCarte.Container.PartialProof1 fn rec p` that use the type `Bytes` instead of `ContainerFor BytesF`
@[expose]
public
def Bytes.PartialProof1 {SubF: Type → Type} [SubBytesFunctor SubF] {a: Type} (fn: Bytes.PartialFunction SubF a) (rec: Bytes → a) (p: a → Prop) :=
  ∀ x: SubF Bytes, (∀ y: Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → p (rec y)) → p (fn x (fun y _ => rec y))

@[expose]
public
def Bytes.Proof1 {a: Type} (fn: Bytes.Function a) (p: a → Prop) := Bytes.PartialProof1 fn (Bytes.rec fn) p

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
def Bytes.PartialProof1.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type}
  {funs: (id: t) → Bytes.PartialFunction (SubFs id) a}
  {rec: Bytes → a} {p: a → Prop}
  (pfs: (id: t) → Bytes.PartialProof1 (funs id) rec p)
  : Bytes.PartialProof1 (Bytes.PartialFunction.combine funs) rec p
:=
  ALaCarte.Container.PartialProof1.combine pfs

-- Unfolding of `ALaCarte.Container.PartialProof2 fn1 fn2 rec1 rec2 p` that use the type `Bytes` instead of `ContainerFor BytesF`
@[expose]
public
def Bytes.PartialProof2 {SubF: Type → Type} [SubBytesFunctor SubF] {a b: Type} (fn1: Bytes.PartialFunction SubF a) (fn2: Bytes.PartialFunction SubF b) (rec1: Bytes → a) (rec2: Bytes → b) (p: a × b → Prop) :=
  ∀ x: SubF Bytes, (∀ y: Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → p (rec1 y, rec2 y)) → p (fn1 x (fun y _ => rec1 y), fn2 x (fun y _ => rec2 y))

@[expose]
public
def Bytes.Proof2 {a b: Type} (fn1: Bytes.Function a) (fn2: Bytes.Function b) (p: a × b → Prop) := Bytes.PartialProof2 fn1 fn2 (Bytes.rec fn1) (Bytes.rec fn2) p

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
def Bytes.PartialProof2.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type} {b: Type}
  {funs1: (id: t) → Bytes.PartialFunction (SubFs id) a}
  {funs2: (id: t) → Bytes.PartialFunction (SubFs id) b}
  {rec1: Bytes → a} {rec2: Bytes → b} {p: a × b → Prop}
  (pfs: (id: t) → Bytes.PartialProof2 (funs1 id) (funs2 id) rec1 rec2 p)
  : Bytes.PartialProof2 (Bytes.PartialFunction.combine funs1) (Bytes.PartialFunction.combine funs2) rec1 rec2 p
:=
  ALaCarte.Container.PartialProof2.combine pfs

public
class BytesLength where
  funs: Bytes.Function Nat

public
def Bytes.length [BytesLength] (b: Bytes): Nat :=
  Bytes.rec BytesLength.funs b

@[expose]
public
def Bytes.PartialLength [BytesFunctor] (SubF: Type → Type) [SubBytesFunctor SubF] := (Bytes.PartialFunction SubF Nat)

public
class BytesLength.HasStep
  {SubF1 SubF2: Type → Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  (partialLength1: outParam (Bytes.PartialLength SubF1))
  (partialLength2: Bytes.PartialLength SubF2)
  extends Bytes.SubFunctionStep partialLength1 partialLength2

public
class BytesLength.Has
  [BytesLength]
  {SubF: Type → Type}
  [SubBytesFunctor SubF]
  [BytesFunctor.Has SubF]
  (binv: outParam (Bytes.PartialLength SubF))
  extends Bytes.SubFunction binv BytesLength.funs

public
abbrev Bytes.PartialLength.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  (lens: ∀ id, Bytes.PartialLength (SubFs id))
  : Bytes.PartialLength (BytesFunctor.combine SubFs)
:=
  Bytes.PartialFunction.combine lens

namespace BytesLength

public
instance [BytesLength]: BytesLength.Has (BytesLength.funs) where

public
instance
  [BytesLength]
  {SubF1 SubF2: Type → Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  [BytesFunctor.Has SubF2]
  (partialLen1: Bytes.PartialLength SubF1)
  (partialLen2: Bytes.PartialLength SubF2)
  [inst1: BytesLength.HasStep partialLen1 partialLen2]
  [inst2: BytesLength.Has partialLen2]
  : BytesLength.Has partialLen1
where

public
instance
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  (SubFs: t → Type → Type) [∀ id, SubBytesFunctor (SubFs id)]
  (invs: ∀ id, Bytes.PartialLength (SubFs id))
  (id: t)
  : BytesLength.HasStep (invs id) (Bytes.PartialLength.combine invs)
where

end BytesLength

@[simp]
public
theorem Bytes.length.eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  [BytesLength]
  {subLength: Bytes.PartialLength SubF}
  [tc: BytesLength.Has subLength]
  (b: BytesView SubF)
  : b.pack.length = subLength b (fun y _ => y.length)
:= by
  have := tc.pf
  apply Bytes.rec_eq

grind_pattern Bytes.length.eq => b.pack.length

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* BytesFunctor $params* from $sources,*) => do
    let options := parseOptions options
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `SubF
      combineName := ``DY.BytesFunctor.combine
      internalOutTypeStx := fun _ _ => `(term| Type → Type)
      outTypeStx := fun _ => `(term| Type → Type)
    }

    let typeclass ← combineTypeclass params sources <| .makeSimple {
      refereeName := `SubF
      combineName := ``DY.BytesFunctor.combine
      outTypeName := ``DY.SubBytesFunctor
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `SubF
      combineName := ``DY.BytesFunctor.combine
      hasStepName := ``DY.BytesFunctor.HasStep
    }

    let subfStx := Lean.mkIdent `SubF
    let topLevelInst ← `(command| public instance: DY.BytesFunctor where BytesF := $subfStx)
    let topLevelHas ← `(command| public instance: DY.BytesFunctor.Has $subfStx := inferInstanceAs (DY.BytesFunctor.Has DY.BytesFunctor.BytesF))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ typeclass ++ hasStep ++ topLevel)

macro_rules
  | `(command| #combine_one $options* BytesLength $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor]))]
    let params := if options.toplevel then params else baseParams ++ params
    let sources := sources.getElems

    let combined ← combineExplicit params sources  <| .makeSimple {
      name := `SubF.length
      refereeName := `SubF
      combineName := ``DY.Bytes.PartialLength.combine
      outTypeName := `DY.Bytes.PartialLength
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `SubF.length
      combineName := ``DY.Bytes.PartialLength.combine
      hasStepName := ``DY.BytesLength.HasStep
    }

    let lengthStx := Lean.mkIdent `SubF.length
    let topLevelInst ← `(command| public instance: DY.BytesLength where funs := $lengthStx)
    let topLevelHas ← `(command| public instance: DY.BytesLength.Has $lengthStx := inferInstanceAs (DY.BytesLength.Has DY.BytesLength.funs))
    let topLevel := if options.toplevel then #[topLevelInst, topLevelHas] else #[]

    return Lean.mkNullNode (combined ++ hasStep ++ topLevel)

end Meta.CombineMacro

end DY
