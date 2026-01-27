namespace DY.ALaCarte
/--
  Compute the sum of `sizeOf` on the `t` contained by `Functor`.
  This is needed to prove `Representable.sizeOf_eq`.
-/
class FunctorSizeOf (f: Type → Type) where
  sizeOf {t: Type} [SizeOf t]: f t → Nat

-- SubFunctor / SubFunctorTC is inspired by Coe / CoeTC
-- Could be split in SubFunctor / LawfulSubFunctor to avoid dependency on FunctorSizeOf?
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

instance (f: Type → Type) [FunctorSizeOf f]: SubFunctorTC f f where
  inj x := x
  proj x := x
  proj_inj x := rfl
  inj_proj x := by simp
  sizeOf_inj x := by simp

instance {f g h: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [FunctorSizeOf h] [SubFunctor f g] [SubFunctorTC g h]: SubFunctorTC f h where
  inj x := SubFunctorTC.inj (SubFunctor.inj (g := g) x)
  proj x :=
    match SubFunctorTC.proj (f := g) x with
    | none => none
    | some x' => SubFunctor.proj x'
  proj_inj x := by grind [SubFunctorTC.proj_inj, SubFunctor.proj_inj]
  inj_proj x := by grind [SubFunctorTC.inj_proj, SubFunctor.inj_proj]
  sizeOf_inj x := by simp [SubFunctorTC.sizeOf_inj, SubFunctor.sizeOf_inj]

structure Ctor where
  Data: Type 0
  nRec: Nat

def Ctors (CtorId: Type) := CtorId -> Ctor

structure FunctorRepr {CtorId} (ctors: Ctors CtorId) (a: Type) where
  id: CtorId
  data: (ctors id).Data
  as: Vector a ((ctors id).nRec)

noncomputable
instance {CtorId} (ctors: Ctors CtorId): FunctorSizeOf (FunctorRepr ctors) where
  sizeOf | {id := _, data := _, as} => (as.map sizeOf).sum

-- Could be split in Representable / LawfulRepresentable to avoid dependency on FunctorSizeOf
class Representable (f: Type → Type) [FunctorSizeOf f] where
  CtorId: Type
  ctors: Ctors CtorId
  toRepr: {a: Type} → f a → FunctorRepr ctors a
  fromRepr: {a: Type} → FunctorRepr ctors a → f a
  from_to: {a: Type} → ∀ x: f a, fromRepr (toRepr x) = x
  to_from: {a: Type} → ∀ x: FunctorRepr ctors a, toRepr (fromRepr x) = x
  sizeOf_eq {a: Type} [SizeOf a]: ∀ x: f a, FunctorSizeOf.sizeOf x = FunctorSizeOf.sizeOf (toRepr x)

structure BareContainer {CtorId} (ctors: Ctors CtorId) where
  id: CtorId
  data: (ctors id).Data
  as: Array (BareContainer ctors)

theorem Array.sizeOf_mem
  {α: Type} [SizeOf α]
  (arr: Array α) (x: α)
  : x ∈ arr → sizeOf x < sizeOf arr
  := by
    cases arr
    rename_i l
    induction l
    · simp
    simp_all
    grind

def BareContainer.wf {CtorId} {ctors: Ctors CtorId} (x: BareContainer ctors): Prop :=
  x.as.size = (ctors x.id).nRec ∧
  ∀ y, y ∈ x.as → y.wf
termination_by sizeOf x
decreasing_by
  have := Array.sizeOf_mem x.as y (by assumption)
  cases x
  simp_all
  grind

def Container {CtorId} (ctors: Ctors CtorId): Type :=
  Subtype (BareContainer.wf (ctors := ctors))

noncomputable
instance {CtorId: Type} (ctors: Ctors CtorId) [SizeOf CtorId]: SizeOf (Container ctors) := inferInstanceAs (SizeOf (Subtype (BareContainer.wf (ctors := ctors))))

abbrev ContainerFor (f: Type → Type) [FunctorSizeOf f] [Representable f] :=
  Container (Representable.ctors (f := f))

theorem Array.unattach_p
  {a: Type u}
  {p: a → Prop}
  (arr: Array (Subtype p))
  : ∀ x, x ∈ arr.unattach → p x
  := by
    simp_all [Array.unattach, -Array.map_subtype]

theorem Array.attachWith_unattach
  {a: Type u}
  {p: a → Prop}
  (arr: Array (Subtype p)) (h: ∀ x, x ∈ (Array.unattach arr) → p x)
  : Array.attachWith (Array.unattach arr) p h = arr
  := by
    cases arr
    rename_i l
    simp only [Array.attachWith, Array.unattach]
    simp only [List.unattach_toArray, List.mem_toArray] at h
    induction l <;>
    simp_all

def Container.intoFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: Container ctors)
  : FunctorRepr ctors (Container ctors)
  where
    id := x.val.id
    data := x.val.data
    as := Vector.mk (x.val.as.attachWith BareContainer.wf (by
      have := x.property
      rewrite [BareContainer.wf] at this
      simp_all
    )) (by
      have := x.property
      rewrite [BareContainer.wf] at this
      rewrite [Array.size_attachWith]
      simp_all
    )

def Container.fromFunctor
  {CtorId: Type} {ctors: Ctors CtorId}
  (x: FunctorRepr ctors (Container ctors))
  : Container ctors
  := Subtype.mk {
    id := x.id
    data := x.data
    as := x.as.toArray.unattach
  } (by
    rewrite [BareContainer.wf]
    grind [Array.size_unattach, Array.unattach_p]
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

structure FunctorUnion {a: Type} (Functors: a → (Type → Type)) (t: Type) where
  id: a
  val: Functors id t

structure FunctorUnion.CtorId {a: Type} (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)] [∀ id, Representable (Functors id)] where
  idHead: a
  idTail: Representable.CtorId (Functors idHead)

instance {a: Type} (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)]: FunctorSizeOf (FunctorUnion Functors) where
  sizeOf x :=
    FunctorSizeOf.sizeOf x.val

instance {a: Type} (Functors: a → (Type → Type)) [∀ id, FunctorSizeOf (Functors id)] [∀ id, Representable (Functors id)]: Representable (FunctorUnion Functors)
  where
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

def Container.pack (f: Type → Type) {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [SubFunctorTC f g] [Representable g] (x: f (ContainerFor g)): (ContainerFor g) :=
  Container.fromFunctor (
    Representable.toRepr (
      SubFunctorTC.inj x
    )
  )

def Container.view (f: Type → Type) {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [SubFunctorTC f g] [Representable g] (x: ContainerFor g): Option (f (ContainerFor g)) :=
  SubFunctorTC.proj (
    Representable.fromRepr (
      Container.intoFunctor x
    )
  )

theorem Container.view_pack
  (f: Type → Type) {g: Type → Type}
  [FunctorSizeOf f] [FunctorSizeOf g]
  [SubFunctorTC f g] [Representable g]
  (x: f (ContainerFor g))
  : view f (pack f x) = some x
  := by
    unfold view pack
    simp [Container.intoFunctor_fromFunctor, Representable.from_to, SubFunctorTC.proj_inj]

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

def Container.PartialFunDep
  (f: Type → Type) {g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [Representable g] [SubFunctorTC f g]
  (motive: ContainerFor g → Sort u)
  :=
  (∀ x: f (ContainerFor g), (∀ y: ContainerFor g, (h: sizeOf y ≤ FunctorSizeOf.sizeOf x := by simp_all +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) → motive y) → motive (pack f x))

-- This one does not require the typeclass instance [SubFunctorTC f g]
def Container.PartialFun
  (f: Type → Type) (g: Type → Type) [FunctorSizeOf f] [FunctorSizeOf g] [Representable g]
  (a: Type)
  :=
  ∀ x: f (ContainerFor g), (∀ y: ContainerFor g, (h: sizeOf y ≤ FunctorSizeOf.sizeOf x := by simp_all +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) → a) → a

def Container.rec
  {f: Type → Type} [FunctorSizeOf f] [Representable f]
  {motive: ContainerFor f → Sort u}
  (pf: Container.PartialFunDep f motive)
  (x: ContainerFor f)
    : motive x := by
  have := pf (Representable.fromRepr (Container.intoFunctor x)) (fun y h => Container.rec pf y)
  simp only [pack, SubFunctorTC.inj, Representable.to_from, Container.fromFunctor_intoFunctor] at this
  exact this
termination_by x
decreasing_by
  have := Representable.sizeOf_eq (Representable.fromRepr (Container.intoFunctor x))
  have := Representable.to_from (Container.intoFunctor x)
  have := Container.sizeOf_intoFunctor x
  grind

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

instance {f: Type → Type} [FunctorSizeOf f] [Representable f] {a: Type} (f: Container.PartialFun f f a): SubPartialFunTC f f where
  pf := by
    simp [SubFunctorTC.inj]

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

def Container.PartialFun.combine
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  {a: Type}
  (funs: (id: t) → Container.PartialFun (functors id) g a)
  : Container.PartialFun (FunctorUnion functors) g a
  := fun {id, val} rec =>
    funs id val (fun y h => rec y h)

def Container.PartialFunDep.combine
  {t: Type} [DecidableEq t]
  {functors: t → Type → Type} [∀ id, FunctorSizeOf (functors id)]
  {g: Type → Type} [FunctorSizeOf g] [Representable g]
  [SubFunctorTC (FunctorUnion functors) g]
  {motive: ContainerFor g → Sort u}
  (funs: (id: t) → Container.PartialFunDep (functors id) motive)
  : Container.PartialFunDep (FunctorUnion functors) motive
  := fun {id, val} rec =>
    funs id val (fun y h => rec y h)

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

def Container.PartialProof1
  {f g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [Representable g]
  {a: Type}
  (fn: Container.PartialFun f g a)
  (rec: ContainerFor g → a)
  (p: a → Prop)
  : Prop
  := ∀ x: f (ContainerFor g), (∀ y: ContainerFor g, sizeOf y ≤ FunctorSizeOf.sizeOf x → p (rec y)) → p (fn x (fun y _ => rec y))

theorem Container.PartialProof1.into
  {f: Type → Type} [FunctorSizeOf f] [Representable f]
  {a: Type}
  {fn: Container.PartialFun f f a}
  {p: a → Prop}
  (pf: Container.PartialProof1 fn (Container.rec fn) p)
  : Container.PartialFunDep f (fun x => p (x.rec fn))
  := by
    unfold Container.PartialFunDep autoParam
    intro x rec
    unfold Container.rec pack
    simp only [SubFunctorTC.inj]
    rewrite [Container.intoFunctor_fromFunctor]
    rewrite [Representable.from_to]
    exact pf x rec

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
  := fun {id, val} rec =>
    pfs id val (fun y h => rec y h)

def Container.PartialProof2
  {f g: Type → Type} [FunctorSizeOf f] [FunctorSizeOf g] [Representable g]
  {a b: Type}
  (fn1: Container.PartialFun f g a)
  (fn2: Container.PartialFun f g b)
  (rec1: ContainerFor g → a)
  (rec2: ContainerFor g → b)
  (p: a × b → Prop)
  : Prop
  := ∀ x: f (ContainerFor g), (∀ y: ContainerFor g, sizeOf y ≤ FunctorSizeOf.sizeOf x → p (rec1 y, rec2 y)) → p (fn1 x (fun y _ => rec1 y), fn2 x (fun y _ => rec2 y))

theorem Container.PartialProof2.into
  {f: Type → Type} [FunctorSizeOf f] [Representable f]
  {a b: Type}
  {fn1: Container.PartialFun f f a}
  {fn2: Container.PartialFun f f b}
  {p: a × b → Prop}
  (pf: Container.PartialProof2 fn1 fn2 (Container.rec fn1) (Container.rec fn2) p)
  : Container.PartialFunDep f (fun x => p (x.rec fn1, x.rec fn2))
  := by
    unfold Container.PartialFunDep autoParam
    intro x rec
    unfold Container.rec pack
    simp only [SubFunctorTC.inj]
    rewrite [Container.intoFunctor_fromFunctor]
    rewrite [Representable.from_to]
    exact pf x rec

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
  := fun {id, val} rec =>
    pfs id val (fun y h => rec y h)

end DY.ALaCarte
