/-
  This module implements "Data types à la carte" (Wouter Swierstra, Journal of Functional Programming, 2008) in Lean.
  This allows to define inductive types modularly, as well as functions and proofs over them.

  # Context

  This is useful in the context of symbolic bytes: in DY*, the symbolic bytes is a fixed inductive

    inductive Bytes where
      | Concat: Bytes → Bytes → Bytes
      | Hash: Bytes → Bytes
      | AeadEncrypt: Bytes → Bytes → Bytes → Bytes → Bytes
      ...

  Then, in DY* we define an invariant recursively on the structure of `Bytes`
  and need to consider exhaustively each constructor:

    def Bytes.Invariant (b: Bytes) (tr: Trace): Prop :=
      match b with
      | Concat lhs rhs => ...
      | Hash input => ...
      | AeadEncrypt key nonce msg ad => ...

  Then, in DY*, we want to prove a property on this invariant,
  for example that it is preserved by the trace growing:

    theorem Bytes.Invariant_later
      (b: Bytes) (tr1 tr2: Trace)
      : tr1 ≤ tr2 → b.Invariant tr1 → b.Invariant tr2
      := ...

  In DyLean, we want three things that cannot be done with this monolithic approach,
  and that this module allows to achieve.

  1. We want users to be able to add new equational theories.
     Indeed, users may want to analyze a protocol that rely on a cryptographic primitive
     that we (DyLean developers) did not anticipate.
     Therefore, we need our type `Bytes` to be modular:
     users should be able to construct it with the cryptographic primitives they need,
     without needing to fork DyLean and modify its core.
  2. We want users to choose the security assumptions they require in their analysis.
     For example, they may want to consider an attacker that can compute a discrete logarithm
     (and therefore recover private keys from public keys)
     after the attacker obtain access to a quantum computer,
     to model Harvest-Now-Decrypt-Later attacks.
     The choice of security assumption for a primitive
     will in turn change how we write its invariant.
     Because the invariant in DY* is fixed,
     it means that DY* decides on a security assumption
     and users cannot choose another one.
  3. For better aesthetics (therefore this point is more minor),
     we would like to transpose the definition of `Bytes`, `Bytes.Invariant` etc.
     Instead of saying "here are all the constructors of `Bytes`",
     then "here are all the invariants for each constructor of `Bytes`", etc,
     we would like to have a file saying
     "here is the constructor `Concat` and here is its invariant",
     then another file saying
     "here is the constructor `Hash` and here is its invariant",
     etc.

  # Implementing "Data types à la carte" in Lean

  Let's first briefly explain the approach of "Data types à la carte".
  Consider the following inductive, that we want to define modularly:

    inductive MyInductive where
      | foo: MyInductive → MyInductive → MyInductive
      | bar: Nat → MyInductive
      | baz: String → MyInductive → MyInductive

  The insight in Section 2. "Fixing the expression problem" is that
  we can also write this inductive like this:

    inductive Functor (α: Type) where
      | foo: α → α → Functor α
      | bar: Nat → Functor α
      | baz: String → α → Functor α

    inductive MyInductive where
      | mk: Functor MyInductive → MyInductive

  The next insight is that we can make `Functor` an argument of `MyInductive`:

    inductive MyInductive (Functor: Type → Type) where
      | mk: Functor (MyInductive Functor) → MyInductive Functor

  Here, `Functor` describes the shape of the inductive we want to define,
  and `MyInductive Functor` is this inductive.
  Unfortunately, we cannot do this in Lean (and in proof assistants in general)
  because of the positivity checker
  (see https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=mutual-inductive-types-positivity )

  To circumvent this problem,
  we design a typeclass for functors called `Representable`,
  and for such functors provide a type isomorphic to `MyInductive Functor`.
  That is, given `[Representable Functor]`, the type `ContainerFor Functor`
  can be converted back and forth from `Functor (ContainerFor Functor)`,
  and furthermore the type `ContainerFor` passes the positivity checker.

  So far, we have seen how to create an inductive from a functor.
  To define the inductive type modularly,
  we will then define this functor modularly.

  Similarly to Section 4. "Automating injections",
  we define a typeclass for sub-functors,
  such that when F is a sub-functor of G,
  we have the functions

    inj: ∀ a, F a → G a
    proj: ∀ a, G a → Option (F a)

  For example, `FunctorFoo` is a sub-functor of `Functor`

    inductive FunctorFoo (α: Type) where
      | foo: α → α → FunctorFoo α

  This allows to convert `FunctorFoo (ContainerFor Functor)`
  to `Functor (ContainerFor Functor)`
  and then to `ContainerFor Functor`,
  thereby effectively constructing an `MyInductive.foo`.

  Suppose we also define

    inductive FunctorBar (α: Type) where
      | bar: Nat → FunctorBar α

    inductive FunctorBaz (α: Type) where
      | baz: String → α → FunctorBaz α

  then `Functor` is isomorphic to

    def Functor (α: Type) :=
      Sigma (fun (id: Fin 3) =>
        match id with
        | 0 => FunctorFoo α
        | 1 => FunctorBar α
        | 2 => FunctorBaz α
      )

  This is how we define functors modularly,
  and therefore how we define inductive types modularly.

  # What else

  In this module, we also allow to modularly write functions (or predicates) on modular inductives,
  as well as modularly write proofs involving modular inductive.

  We take a different approach from Section 3. "Evaluation",
  and instead allow for well-founded recursion using Lean's built-in `sizeOf`.
-/

module

import DY.Misc.Array

namespace DY.ALaCarte

/--
  Compute the sum of `sizeOf` on the `t` contained by `Functor`.
  This is needed to prove `Representable.sizeOf_eq`.
-/
public
class FunctorSizeOf (f: Type → Type) where
  sizeOf {t: Type} [SizeOf t]: f t → Nat

-- The combo SubFunctor / SubFunctorTC is inspired by Coe / CoeTC
public
class SubFunctor (f: Type → Type) (g: semiOutParam (Type → Type)) [FunctorSizeOf f] [semiOutParam (FunctorSizeOf g)] where
  inj: {a: Type} → f a → g a
  proj: {a: Type} → g a → Option (f a)
  proj_inj {a: Type}:
    ∀ x: f a, proj (inj x) = some x
  inj_proj {a: Type}:
    ∀ x: g a,
    match proj x with
    | some y => inj y = x
    | none => True
  sizeOf_inj {a: Type} [SizeOf a] (x: f a):
    FunctorSizeOf.sizeOf (inj x) = FunctorSizeOf.sizeOf x

-- Transitive Closure for SubFunctor
-- Inspired by Coe / CoeTC
public
class SubFunctorTC (f g: Type → Type) [FunctorSizeOf f] [FunctorSizeOf g] where
  inj: {a: Type} → f a → g a
  proj: {a: Type} → g a → Option (f a)
  proj_inj {a: Type}:
    ∀ x: f a, proj (inj x) = some x
  inj_proj {a: Type}:
    ∀ x: g a,
    match proj x with
    | some y => inj y = x
    | none => True
  sizeOf_inj {a: Type} [SizeOf a] (x: f a):
    FunctorSizeOf.sizeOf (inj x) = FunctorSizeOf.sizeOf x

public
instance (f: Type → Type) [FunctorSizeOf f]: SubFunctorTC f f where
  inj x := x
  proj x := x
  proj_inj x := rfl
  inj_proj x := by simp
  sizeOf_inj x := by simp

public
instance {f g h: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [FunctorSizeOf h] [SubFunctor f g] [SubFunctorTC g h]: SubFunctorTC f h where
  inj x := SubFunctorTC.inj (SubFunctor.inj (g := g) x)
  proj x :=
    match SubFunctorTC.proj (f := g) x with
    | none => none
    | some x' => SubFunctor.proj x'
  proj_inj x := by grind [SubFunctorTC.proj_inj, SubFunctor.proj_inj]
  inj_proj x := by grind [SubFunctorTC.inj_proj, SubFunctor.inj_proj]
  sizeOf_inj x := by simp [SubFunctorTC.sizeOf_inj, SubFunctor.sizeOf_inj]

/--
  A constructor of a functor / an inductive
  is characterized by the fixed types it contains, and the number of time it recurses.
  For example, the constructor

    | foo: Nat → String → α → α → MyFunctor α

  of a functor, or equivalently the constructor

    | foo: Nat → String → MyInductive → MyInductive → MyInductive

  of an inductive is described by the `Ctor`

    {
      Data := Nat × String
      nRec := 2
    }
-/
public
structure Ctor where
  Data: Type
  nRec: Nat

@[expose]
public
def Ctors (CtorId: Type) := CtorId -> Ctor

public
structure FunctorRepr {CtorId} (ctors: Ctors CtorId) (a: Type) where
  id: CtorId
  data: (ctors id).Data
  as: Vector a ((ctors id).nRec)

public
noncomputable
instance {CtorId} (ctors: Ctors CtorId): FunctorSizeOf (FunctorRepr ctors) where
  sizeOf | {id := _, data := _, as} => (as.map sizeOf).sum

/--
  A functor is "representable" when there exists a set of `Ctor`
  such that the functor is isomorphic to `FunctorRepr` with this set of `Ctor`.
-/
public
class Representable (f: Type → Type) [FunctorSizeOf f] where
  CtorId: Type
  ctors: Ctors CtorId
  toRepr: {a: Type} → f a → FunctorRepr ctors a
  fromRepr: {a: Type} → FunctorRepr ctors a → f a
  from_to: {a: Type} → ∀ x: f a, fromRepr (toRepr x) = x
  to_from: {a: Type} → ∀ x: FunctorRepr ctors a, toRepr (fromRepr x) = x
  sizeOf_eq {a: Type} [SizeOf a]: ∀ x: f a, FunctorSizeOf.sizeOf x = FunctorSizeOf.sizeOf (toRepr x)

public
structure BareContainer {CtorId} (ctors: Ctors CtorId) where
  id: CtorId
  data: (ctors id).Data
  as: Array (BareContainer ctors)

public
def BareContainer.wf {CtorId} {ctors: Ctors CtorId} (x: BareContainer ctors): Prop :=
  x.as.size = (ctors x.id).nRec ∧
  ∀ y, y ∈ x.as → y.wf
termination_by sizeOf x
decreasing_by
  have := Array.sizeOf_lt_of_mem (by assumption)
  cases x
  simp_all
  grind

/--
  `Container ctors` is a type that is, by construction, isomorphic to `FunctorRepr ctors (Container ctors)`.
-/
@[expose]
public
abbrev Container {CtorId} (ctors: Ctors CtorId): Type :=
  Subtype (BareContainer.wf (ctors := ctors))

/--
  When a functor is `Representable`, we can use `ContainerFor` as a shorthand for `Container`.
  It has the property that `ContainerFor f` is isomorphic to `f (ContainerFor f)`:

      ContainerFor f
    = Container ctors                       [by unfolding ContainerFor]
    ≅ FunctorRepr ctors (Container ctors)   [by property of Container]
    = FunctorRepr ctors (ContainerFor f)    [by refolding ContainerFor]
    ≅ f (ContainerFor f)                    [by f being Representable]
-/
public
abbrev ContainerFor (f: Type → Type) [FunctorSizeOf f] [Representable f] :=
  Container (Representable.ctors (f := f))

def Container.intoFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: Container ctors)
  : FunctorRepr ctors (Container ctors)
where
  id := x.val.id
  data := x.val.data
  as := Vector.mk (x.val.as.attachWith BareContainer.wf (by
    grind [BareContainer.wf]
  )) (by
    grind [BareContainer.wf, Array.size_attachWith]
  )

def Container.fromFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: FunctorRepr ctors (Container ctors))
  : Container ctors
:=
  Subtype.mk {
    id := x.id
    data := x.data
    as := x.as.toArray.unattach
  } (by
    grind [BareContainer.wf, Array.size_unattach, Array.mem_unattach]
  )

def Container.intoFunctor_fromFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: FunctorRepr ctors (Container ctors))
  : Container.intoFunctor (Container.fromFunctor x) = x
:= by
  cases x; rename_i id data as
  rewrite [Container.fromFunctor, Container.intoFunctor]
  simp [Array.attachWith_unattach]

def Container.fromFunctor_intoFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: Container ctors)
  : Container.fromFunctor (Container.intoFunctor x) = x
:= by
  cases x; rename_i x h_x
  cases x; rename_i id data as
  rewrite [Container.fromFunctor, Container.intoFunctor]
  simp

theorem List.map_sizeOf_attachWith
  {α: Type} [SizeOf α]
  (l : List α) (P : α → Prop) (H : ∀ x ∈ l, P x)
  : (List.map sizeOf (l.attachWith P H)).sum ≤ sizeOf l
:= by
  induction l <;>
  simp_all

theorem Container.sizeOf_intoFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: Container ctors)
  : FunctorSizeOf.sizeOf (Container.intoFunctor x) < sizeOf x
:= by
  cases x; rename_i val property
  cases val; rename_i id data as
  cases as; rename_i l
  rewrite [Subtype.mk.sizeOf_spec]
  simp only [FunctorSizeOf.sizeOf, intoFunctor, List.attachWith_toArray, Vector.map_mk, List.map_toArray, Vector.sum_mk, List.sum_toArray, BareContainer.mk.sizeOf_spec, sizeOf_default, Nat.add_zero, Array.mk.sizeOf_spec]
  refine Nat.lt_add_left 1 ?_
  refine Nat.lt_add_left 1 ?_
  refine Nat.lt_one_add_iff.mpr ?_
  apply List.map_sizeOf_attachWith

/--
  When we have a collection of functors,
  we can create the union using `FunctorUnion`.
  Such an union is representable,
  and each functor will then be a sub-functor of this union.
-/
public
structure FunctorUnion {a: Type} (Functors: a → (Type → Type)) (t: Type) where
  id: a
  val: Functors id t

public
structure FunctorUnion.CtorId {a: Type} (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)] [∀ id, Representable (Functors id)] where
  idHead: a
  idTail: Representable.CtorId (Functors idHead)

public
instance {a: Type} (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)]: FunctorSizeOf (FunctorUnion Functors) where
  sizeOf x :=
    FunctorSizeOf.sizeOf x.val

public
instance {a: Type} (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)] [∀ id, Representable (Functors id)]: Representable (FunctorUnion Functors) where
  CtorId := FunctorUnion.CtorId Functors
  ctors id :=
    (Representable.ctors (f := Functors id.idHead)) id.idTail
  toRepr x :=
    let reprMid := Representable.toRepr (f := Functors x.id) x.val
    { reprMid with
      id := {
        idHead := x.id,
        idTail := reprMid.id
      }
    }
  fromRepr repr :=
    {
      id := repr.id.idHead
      val := Representable.fromRepr (f := Functors repr.id.idHead) { repr with id := repr.id.idTail }
    }
  from_to := by
    intro a x
    simp_all [Representable.from_to (f := Functors x.id) x.val]
  to_from := by
    intro a repr
    have := Representable.to_from (f := Functors repr.id.idHead) { repr with id := repr.id.idTail }
    cases repr
    simp_all
    grind
  sizeOf_eq x := by
    simp only [FunctorSizeOf.sizeOf]
    have := Representable.sizeOf_eq x.val
    revert this
    generalize (Representable.toRepr x.val) = y
    cases y
    simp [FunctorSizeOf.sizeOf]

public
instance {a: Type} [DecidableEq a] (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)] (id: a): SubFunctor (Functors id) (FunctorUnion Functors) where
  inj x := {
    id := id
    val := x
  }
  proj x :=
    if h: x.id = id then
      some (h ▸ x.val)
    else
      none
  proj_inj x := by grind
  inj_proj x := by cases x; grind
  sizeOf_inj x := by simp [FunctorSizeOf.sizeOf]

public
def Container.pack (f: Type → Type) {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [SubFunctorTC f g] [Representable g] (x: f (ContainerFor g)): (ContainerFor g) :=
  Container.fromFunctor (
    Representable.toRepr (
      SubFunctorTC.inj x
    )
  )

public
def Container.view (f: Type → Type) {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [SubFunctorTC f g] [Representable g] (x: ContainerFor g): Option (f (ContainerFor g)) :=
  SubFunctorTC.proj (
    Representable.fromRepr (
      Container.intoFunctor x
    )
  )

public
theorem Container.view_pack
  (f: Type → Type) {g: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g]
  [SubFunctorTC f g] [Representable g]
  (x: f (ContainerFor g))
  : view f (pack f x) = some x
:= by
  unfold view pack
  simp [Container.intoFunctor_fromFunctor, Representable.from_to, SubFunctorTC.proj_inj]

public
theorem Container.pack_view
  (f: Type → Type) {g: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g]
  [SubFunctorTC f g] [Representable g]
  (x: ContainerFor g)
  : match view f x with
    | none => True
    | some y => pack f y = x
:= by
  unfold view pack
  split
  · trivial
  · have := SubFunctorTC.inj_proj (f := f) (Representable.fromRepr x.intoFunctor)
    have := Representable.to_from x.intoFunctor
    have := Container.fromFunctor_intoFunctor x
    simp_all

public
theorem Container.sizeOf_pack
  (f: Type → Type) {g: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g]
  [SubFunctorTC f g]
  [Representable g]
  (x: f (ContainerFor g))
  : FunctorSizeOf.sizeOf x ≤ sizeOf (Container.pack f x)
:= by
  simp_all only [Container.pack]
  have := SubFunctorTC.sizeOf_inj (g := g) x
  have := Representable.sizeOf_eq (f := g) (SubFunctorTC.inj x)
  have := Container.sizeOf_intoFunctor (fromFunctor (Representable.toRepr (SubFunctorTC.inj x)))
  have := Container.intoFunctor_fromFunctor (Representable.toRepr (SubFunctorTC.inj x))
  grind

public
theorem Container.sizeOf_view
  (f: Type → Type) {g: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g]
  [SubFunctorTC f g]
  [Representable g]
  (x: ContainerFor g)
  : match x.view f with
    | none => True
    | some y => FunctorSizeOf.sizeOf y ≤ sizeOf x
:= by
  split
  · trivial
  rename_i y heq
  have: pack f y = x := by grind [Container.pack_view]
  grind [Container.sizeOf_pack]

@[expose]
public
def Container.PartialFunDep
  (f: Type → Type) {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [Representable g] [SubFunctorTC f g]
  (motive: ContainerFor g → Sort u)
:=
  (∀ x: f (ContainerFor g), (∀ y: ContainerFor g, sizeOf y ≤ FunctorSizeOf.sizeOf x → motive y) → motive (pack f x))

-- This one does not require the typeclass instance [SubFunctorTC f g]
@[expose]
public
def Container.PartialFun
  (f: Type → Type) (g: Type → Type) [FunctorSizeOf f] [FunctorSizeOf g] [Representable g]
  (a: Type)
:=
  ∀ x: f (ContainerFor g), (∀ y: ContainerFor g, sizeOf y ≤ FunctorSizeOf.sizeOf x → a) → a

/--
  Generic recursion principle on `Container`.
  This allows to define functions, predicates, and to do proofs.
-/
public
def Container.rec
  {f: Type → Type} [FunctorSizeOf f] [Representable f]
  {motive: ContainerFor f → Sort u}
  (pf: Container.PartialFunDep f motive)
  (x: ContainerFor f)
  : motive x
:= by
  have := pf (Representable.fromRepr (Container.intoFunctor x)) (fun y _ => Container.rec pf y)
  simp only [pack, SubFunctorTC.inj, Representable.to_from, Container.fromFunctor_intoFunctor] at this
  exact this
termination_by x
decreasing_by
  have := Representable.sizeOf_eq (Representable.fromRepr (Container.intoFunctor x))
  have := Representable.to_from (Container.intoFunctor x)
  have := Container.sizeOf_intoFunctor x
  grind

public
class SubPartialFun
  {f g h: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g] [FunctorSizeOf h]
  [Representable h]
  [SubFunctor f g]
  {a: Type}
  (f1: Container.PartialFun f h a)
  (f2: semiOutParam (Container.PartialFun g h a))
where
  pf (f1 f2): ∀ x rec, f1 x rec = f2 (SubFunctor.inj x) (fun y h => rec y (by simp_all [SubFunctor.sizeOf_inj x]))

public
class SubPartialFunTC
  {f g h: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g] [FunctorSizeOf h]
  [Representable h]
  [SubFunctorTC f g]
  {a: Type}
  (f1: Container.PartialFun f h a)
  (f2: Container.PartialFun g h a)
where
  pf (f1 f2): ∀ x rec, f1 x rec = f2 (SubFunctorTC.inj x) (fun y h => rec y (by simp_all [SubFunctorTC.sizeOf_inj x]))

public
instance {f: Type → Type} [FunctorSizeOf f] [Representable f] {a: Type} (f: Container.PartialFun f f a): SubPartialFunTC f f where
  pf := by
    simp [SubFunctorTC.inj]

public
instance
  {f g h i: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g] [FunctorSizeOf h] [FunctorSizeOf i]
  [Representable i]
  [SubFunctor f g]
  [SubFunctorTC g h]
  {a: Type}
  (f1: Container.PartialFun f i a)
  (f2: Container.PartialFun g i a)
  (f3: Container.PartialFun h i a)
  [SubPartialFun f1 f2]
  [SubPartialFunTC f2 f3]
  : SubPartialFunTC f1 f3
where
  pf := by
    intro x rec
    simp [SubFunctorTC.inj]
    rewrite [← SubPartialFunTC.pf f2 f3 (SubFunctor.inj x) (fun y h => rec y (by grind [SubFunctor.sizeOf_inj]))]
    rewrite [← SubPartialFun.pf f1 f2 x (fun y h => rec y (by grind))]
    rfl

public
theorem Container.rec_eq
  {f: Type → Type} {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [SubFunctorTC f g] [Representable g]
  {a: Type}
  (partialFun: Container.PartialFun f g a)
  (totalFun: Container.PartialFun g g a)
  [SubPartialFunTC partialFun totalFun]
  (x: f (ContainerFor g))
  : (pack f x).rec totalFun = partialFun x (fun y _ => y.rec totalFun)
:= by
  conv => lhs; unfold Container.rec pack
  simp only [eq_mp_eq_cast, cast_eq]
  rewrite [Container.intoFunctor_fromFunctor]
  rewrite [Representable.from_to]
  rewrite [<- SubPartialFunTC.pf partialFun totalFun x (fun y h => rec totalFun y)]
  grind

public
def Container.PartialFun.combine
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  {a: Type}
  (funs: (id: t) → Container.PartialFun (functors id) g a)
  : Container.PartialFun (FunctorUnion functors) g a
:=
  fun {id, val} rec =>
    funs id val rec

public
def Container.PartialFunDep.combine
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  [SubFunctorTC (FunctorUnion functors) g]
  {motive: ContainerFor g → Sort u}
  (funs: (id: t) → Container.PartialFunDep (functors id) motive)
  : Container.PartialFunDep (FunctorUnion functors) motive
:=
  fun {id, val} rec =>
    funs id val rec

public
instance
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  {a: Type}
  (funs: (id: t) → Container.PartialFun (functors id) g a)
  (id: t)
  : SubPartialFun (funs id) (Container.PartialFun.combine funs)
where
  pf x rec := by
    simp [Container.PartialFun.combine]
    congr

/--
  Helper to write a modular proof on one modular function
-/
@[expose]
public
def Container.PartialProof1
  {f g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [Representable g]
  {a: Type}
  (fn: Container.PartialFun f g a)
  (rec: ContainerFor g → a)
  (p: a → Prop)
  : Prop
:=
  ∀ x: f (ContainerFor g), (∀ y: ContainerFor g, sizeOf y ≤ FunctorSizeOf.sizeOf x → p (rec y)) → p (fn x (fun y _ => rec y))

public
theorem Container.PartialProof1.into
  {f: Type → Type} [FunctorSizeOf f] [Representable f]
  {a: Type}
  {fn: Container.PartialFun f f a}
  {p: a → Prop}
  (pf: Container.PartialProof1 fn (Container.rec fn) p)
  : Container.PartialFunDep f (fun x => p (x.rec fn))
:= by
  unfold Container.PartialFunDep
  intro x rec
  unfold Container.rec pack
  simp only [SubFunctorTC.inj]
  rewrite [Container.intoFunctor_fromFunctor]
  rewrite [Representable.from_to]
  exact pf x rec

public
def Container.PartialProof1.combine
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  {a: Type}
  {rec: ContainerFor g → a}
  {p: a → Prop}
  {funs: (id: t) → Container.PartialFun (functors id) g a}
  (pfs: (id: t) → Container.PartialProof1 (funs id) rec p)
  : Container.PartialProof1 (Container.PartialFun.combine funs) rec p
:=
  fun {id, val} rec =>
    pfs id val rec

/--
  Helper to write a modular proof on two modular functions
-/
@[expose]
public
def Container.PartialProof2
  {f g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [Representable g]
  {a b: Type}
  (fn1: Container.PartialFun f g a)
  (fn2: Container.PartialFun f g b)
  (rec1: ContainerFor g → a)
  (rec2: ContainerFor g → b)
  (p: a × b → Prop)
  : Prop
:=
  ∀ x: f (ContainerFor g), (∀ y: ContainerFor g, sizeOf y ≤ FunctorSizeOf.sizeOf x → p (rec1 y, rec2 y)) → p (fn1 x (fun y _ => rec1 y), fn2 x (fun y _ => rec2 y))

public
theorem Container.PartialProof2.into
  {f: Type → Type} [FunctorSizeOf f] [Representable f]
  {a b: Type}
  {fn1: Container.PartialFun f f a}
  {fn2: Container.PartialFun f f b}
  {p: a × b → Prop}
  (pf: Container.PartialProof2 fn1 fn2 (Container.rec fn1) (Container.rec fn2) p)
  : Container.PartialFunDep f (fun x => p (x.rec fn1, x.rec fn2))
:= by
  unfold Container.PartialFunDep
  intro x rec
  unfold Container.rec pack
  simp only [SubFunctorTC.inj]
  rewrite [Container.intoFunctor_fromFunctor]
  rewrite [Representable.from_to]
  exact pf x rec

public
def Container.PartialProof2.combine
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  {a b: Type}
  {rec1: ContainerFor g → a}
  {rec2: ContainerFor g → b}
  {p: a × b → Prop}
  {funs1: (id: t) → Container.PartialFun (functors id) g a}
  {funs2: (id: t) → Container.PartialFun (functors id) g b}
  (pfs: (id: t) → Container.PartialProof2 (funs1 id) (funs2 id) rec1 rec2 p)
  : Container.PartialProof2 (Container.PartialFun.combine funs1) (Container.PartialFun.combine funs2) rec1 rec2 p
:=
  fun {id, val} rec =>
    pfs id val rec

end DY.ALaCarte
