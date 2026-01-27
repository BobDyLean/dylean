import DY.ALaCarte.Basic
import DY.ALaCarte.DecidableEq
import DY.ALaCarte.Ordering

namespace DY

class SubBytesFunctor (SubF: Type → Type) where
  [sizeOf: ALaCarte.FunctorSizeOf SubF]
  [repr: ALaCarte.Representable SubF]
  [deq: ALaCarte.RepresentableDecidableEq SubF]
  [ord: ALaCarte.RepresentableOrd SubF]

instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.FunctorSizeOf SubF := inst.sizeOf
instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.Representable SubF := inst.repr
instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.RepresentableDecidableEq SubF := inst.deq
instance (SubF: Type → Type) [inst: SubBytesFunctor SubF]: ALaCarte.RepresentableOrd SubF := inst.ord

class BytesFunctor where
  BytesF: Type → Type
  [inst: SubBytesFunctor BytesF]
export BytesFunctor (BytesF)

instance [inst: BytesFunctor]: SubBytesFunctor BytesF := inst.inst

-- Sanity checks

example [inst: BytesFunctor]: ALaCarte.FunctorSizeOf BytesF := inferInstance
example [inst: BytesFunctor]: ALaCarte.Representable BytesF := inferInstance
example [inst: BytesFunctor]: ALaCarte.RepresentableDecidableEq BytesF := inferInstance
example [inst: BytesFunctor]: ALaCarte.RepresentableOrd BytesF := inferInstance

variable [BytesFunctor]
-- TODO: Bytes or SymbolicBytes?
def Bytes := ALaCarte.ContainerFor BytesF

instance: DecidableEq Bytes := inferInstanceAs (DecidableEq (ALaCarte.ContainerFor BytesF))

instance: Ord Bytes := inferInstanceAs (Ord (ALaCarte.ContainerFor BytesF))
instance: Std.ReflOrd Bytes := inferInstanceAs (Std.ReflOrd (ALaCarte.ContainerFor BytesF))
instance: Std.LawfulEqOrd Bytes := inferInstanceAs (Std.LawfulEqOrd (ALaCarte.ContainerFor BytesF))
instance: Std.OrientedOrd Bytes := inferInstanceAs (Std.OrientedOrd (ALaCarte.ContainerFor BytesF))
instance: Std.TransOrd Bytes := inferInstanceAs (Std.TransOrd (ALaCarte.ContainerFor BytesF))

class BytesFunctor.HasStep (SubF1: Type → Type) (SubF2: semiOutParam (Type → Type)) [SubBytesFunctor SubF1] [semiOutParam (SubBytesFunctor SubF2)] extends ALaCarte.SubFunctor SubF1 SubF2
class BytesFunctor.Has (SubF: Type → Type) [SubBytesFunctor SubF] extends ALaCarte.SubFunctorTC SubF BytesF

-- To avoid instance name clashing with other files
namespace BytesFunctor

instance: BytesFunctor.Has BytesF where
instance
  (SubF1 SubF2: Type → Type)
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  [BytesFunctor.Has SubF2]
  : BytesFunctor.Has SubF1
  where

end BytesFunctor

abbrev BytesFunctor.combine {a: Type} (SubFs: a → Type → Type): Type → Type :=
  ALaCarte.FunctorUnion SubFs

instance {a: Type} [DecidableEq a] [Ord a] [Std.LawfulEqOrd a] [Std.TransOrd a] (SubFs: a → Type → Type) [∀ id, SubBytesFunctor (SubFs id)]: SubBytesFunctor (BytesFunctor.combine SubFs) where
  sizeOf := inferInstance
  repr := inferInstance
  deq := inferInstance
  ord := inferInstance

instance
  {a: Type} [DecidableEq a] [Ord a] [Std.LawfulEqOrd a] [Std.TransOrd a]
  (SubFs: a → Type → Type) [∀ id, SubBytesFunctor (SubFs id)]
  (id: a)
  : BytesFunctor.HasStep (SubFs id) (BytesFunctor.combine SubFs)
  where

def BytesView (SubF: Type → Type) := SubF Bytes

def Bytes.view? (b: Bytes) (SubF: Type → Type) [SubBytesFunctor SubF] [BytesFunctor.Has SubF] : Option (BytesView SubF) :=
  ALaCarte.Container.view SubF b

def BytesView.pack
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  (b: BytesView SubF)
  : Bytes
  :=
  ALaCarte.Container.pack SubF b

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

theorem BytesView.view_pack
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  (b: BytesView SubF)
  : (b.pack).view? SubF = some b
  := by
    simp only [BytesView.pack, Bytes.view?]
    grind [ALaCarte.Container.view_pack]

grind_pattern BytesView.view_pack => b.pack

def Bytes.PartialFunction (SubF: Type → Type) [SubBytesFunctor SubF] (a: Type) := ALaCarte.Container.PartialFun SubF BytesF a
def Bytes.Function (a: Type) := Bytes.PartialFunction BytesF a

def Bytes.rec {a: Type} (f: Bytes.Function a) (x: Bytes) : a :=
  ALaCarte.Container.rec f x

class Bytes.SubFunctionStep
  {SubF1 SubF2: Type → Type} {a: Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.HasStep SubF1 SubF2]
  (partialFun1: Bytes.PartialFunction SubF1 a)
  (partialFun2: semiOutParam (Bytes.PartialFunction SubF2 a))
  extends ALaCarte.SubPartialFun partialFun1 partialFun2

class Bytes.SubFunction
  {SubF: Type → Type}
  [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  {a: Type}
  (partialFun: Bytes.PartialFunction SubF a)
  (totalFun: Bytes.Function a)
  extends ALaCarte.SubPartialFunTC partialFun totalFun

instance
  {a: Type}
  (totalFun: Bytes.Function a)
  : Bytes.SubFunction totalFun totalFun
  where

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

def Bytes.PartialFunction.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type}
  (funs: (id: t) → Bytes.PartialFunction (SubFs id) a)
  : Bytes.PartialFunction (BytesFunctor.combine SubFs) a
  := ALaCarte.Container.PartialFun.combine funs

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

theorem Bytes.rec_eq
  {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
  {a: Type}
  (partialFun: Bytes.PartialFunction SubF a)
  (totalFun: Bytes.Function a)
  [Bytes.SubFunction partialFun totalFun]
  (x: BytesView SubF)
  : x.pack.rec totalFun = partialFun x (fun y _ => y.rec totalFun)
  := ALaCarte.Container.rec_eq partialFun totalFun x

def Bytes.PartialProof1 {SubF: Type → Type} [SubBytesFunctor SubF] {a: Type} (fn: Bytes.PartialFunction SubF a) (rec: Bytes → a) (p: a → Prop) := ALaCarte.Container.PartialProof1 fn rec p

def Bytes.Proof1 {a: Type} (fn: Bytes.Function a) (p: a → Prop) := Bytes.PartialProof1 fn (Bytes.rec fn) p

theorem Bytes.Proof1.prove
  {a: Type}
  {fn: Bytes.Function a}
  {p: a → Prop}
  (pf: Bytes.Proof1 fn p)
  (x: Bytes)
  : p (x.rec fn)
  := ALaCarte.Container.rec (ALaCarte.Container.PartialProof1.into pf) x

def Bytes.PartialProof1.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type}
  {funs: (id: t) → Bytes.PartialFunction (SubFs id) a}
  {rec: Bytes → a} {p: a → Prop}
  (pfs: (id: t) → Bytes.PartialProof1 (funs id) rec p)
  : Bytes.PartialProof1 (Bytes.PartialFunction.combine funs) rec p
  := ALaCarte.Container.PartialProof1.combine pfs

def Bytes.PartialProof2 {SubF: Type → Type} [SubBytesFunctor SubF] {a b: Type} (fn1: Bytes.PartialFunction SubF a) (fn2: Bytes.PartialFunction SubF b) (rec1: Bytes → a) (rec2: Bytes → b) (p: a × b → Prop) := ALaCarte.Container.PartialProof2 fn1 fn2 rec1 rec2 p

def Bytes.Proof2 {a b: Type} (fn1: Bytes.Function a) (fn2: Bytes.Function b) (p: a × b → Prop) := Bytes.PartialProof2 fn1 fn2 (Bytes.rec fn1) (Bytes.rec fn2) p

theorem Bytes.Proof2.prove
  {a b: Type}
  {fn1: Bytes.Function a}
  {fn2: Bytes.Function b}
  {p: a × b → Prop}
  (pf: Bytes.Proof2 fn1 fn2 p)
  (x: Bytes)
  : p (x.rec fn1, x.rec fn2)
  := ALaCarte.Container.rec (ALaCarte.Container.PartialProof2.into pf) x

def Bytes.PartialProof2.combine
  {t: Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
  {SubFs: t → Type → Type} [∀ id, SubBytesFunctor (SubFs id)]
  {a: Type} {b: Type}
  {funs1: (id: t) → Bytes.PartialFunction (SubFs id) a}
  {funs2: (id: t) → Bytes.PartialFunction (SubFs id) b}
  {rec1: Bytes → a} {rec2: Bytes → b} {p: a × b → Prop}
  (pfs: (id: t) → Bytes.PartialProof2 (funs1 id) (funs2 id) rec1 rec2 p)
  : Bytes.PartialProof2 (Bytes.PartialFunction.combine funs1) (Bytes.PartialFunction.combine funs2) rec1 rec2 p
  := ALaCarte.Container.PartialProof2.combine pfs

end DY
