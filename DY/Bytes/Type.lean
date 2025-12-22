namespace DY

structure BytesCtor where
  data: Type 0
  nBytes: Nat
  -- TODO: we might want to move these outside BytesCtor(s) so that they only contain typing information
  [dataOrd: Ord data]
  [dataReflOrd: Std.ReflOrd data]
  [dataLawfulEqOrd: Std.LawfulEqOrd data]
  [dataOrientedOrd: Std.OrientedOrd data]
  [dataTransOrd: Std.TransOrd data]

-- TODO: if we want to compute bytes term, this Vect type is slow for performance
-- because it contains the length of each subvector (classic issue)
-- we cannot use list + subtype because Lean tries to unfold it into a big mutually recursive type
-- (see https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=nested-inductive-types )
-- possible solution: Use List or Vector (no length constraints),
-- but then subtype Bytes by the fact that each length is correct?
inductive Vect (a:Type u): Nat -> Type u where
  | nil: Vect a 0
  | cons: a -> Vect a n -> Vect a (n+1)

syntax "V[" withoutPosition(term,*,?) "]"  : term

macro_rules
  | `(V[ $elems,* ]) => do
    pure (← elems.getElems.foldrM (fun elem acc => ``(Vect.cons $elem $acc)) (← ``(Vect.nil)))

class BytesCtors where
  n: Nat
  ctors: Fin n -> BytesCtor

abbrev CtorId [BytesCtors] := Fin BytesCtors.n

structure Bytes [BytesCtors] where
  id: CtorId
  data: (BytesCtors.ctors id).data
  dataBytes: Vect (Bytes) ((BytesCtors.ctors id).nBytes)

mutual
def compareVectBytes [BytesCtors] {n: Nat} (v1 v2: Vect Bytes n): Ordering :=
  match v1, v2 with
  | .nil, .nil => .eq
  | .cons h1 t1, .cons h2 t2 =>
    match compareBytes h1 h2 with
    | .lt => .lt
    | .gt => .gt
    | .eq => compareVectBytes t1 t2
def compareBytes [BytesCtors] (b1 b2: Bytes): Ordering :=
  let {id := id1, data := data1, dataBytes := dataBytes1} := b1
  let {id := id2, data := data2, dataBytes := dataBytes2} := b2
  match h: compare id1 id2 with
  | .lt => .lt
  | .gt => .gt
  | .eq => by
    simp at h
    subst h
    generalize BytesCtors.ctors id1 = ctor at *
    exact (
      match ctor.dataOrd.compare data1 data2 with
      | .lt => .lt
      | .gt => .gt
      | .eq => (
        compareVectBytes dataBytes1 dataBytes2
      )
    )
end

instance [BytesCtors] {id: CtorId}: Ord ((BytesCtors.ctors id).data) := (BytesCtors.ctors id).dataOrd
instance [BytesCtors] {id: CtorId}: Std.ReflOrd ((BytesCtors.ctors id).data) := (BytesCtors.ctors id).dataReflOrd
instance [BytesCtors] {id: CtorId}: Std.LawfulEqOrd ((BytesCtors.ctors id).data) := (BytesCtors.ctors id).dataLawfulEqOrd
instance [BytesCtors] {id: CtorId}: Std.OrientedOrd ((BytesCtors.ctors id).data) := (BytesCtors.ctors id).dataOrientedOrd
instance [BytesCtors] {id: CtorId}: Std.TransOrd ((BytesCtors.ctors id).data) := (BytesCtors.ctors id).dataTransOrd

mutual
theorem compareVectBytes_Refl
  [BytesCtors] {n: Nat}
  (v: Vect Bytes n)
  : compareVectBytes v v = .eq
  := by
    cases v
    · rfl
    · rename_i h t
      unfold compareVectBytes
      simp [compareBytes_Refl h, compareVectBytes_Refl t]

theorem compareBytes_Refl
  [BytesCtors]
  (b: Bytes)
  : compareBytes b b = .eq
  := by
    let {id := id, data := data, dataBytes := dataBytes} := b
    simp only [compareBytes]
    have id_Refl : compare id id = .eq := by simp
    rewrite [id_Refl]
    dsimp only
    simp [compareVectBytes_Refl]
end

mutual
theorem compareVectBytes_LawfulEq
  [BytesCtors] {n: Nat}
  (v1 v2: Vect Bytes n)
  : compareVectBytes v1 v2 = .eq → v1 = v2
  := by
    cases v1 <;> cases v2
    · simp [compareVectBytes]
    · simp [compareVectBytes]
      split
      · simp
      · simp
      · rename_i heq
        have := compareBytes_LawfulEq _ _ heq
        intro heq
        have := compareVectBytes_LawfulEq _ _ heq
        simp_all

theorem compareBytes_LawfulEq
  [BytesCtors]
  (b1 b2: Bytes)
  : compareBytes b1 b2 = .eq → b1 = b2
  := by
    let {id := id1, data := data1, dataBytes := dataBytes1} := b1
    let {id := id2, data := data2, dataBytes := dataBytes2} := b2
    simp only [compareBytes, Bytes.mk.injEq]
    split
    · simp
    · simp
    rename_i heq
    have heq := Std.LawfulEqOrd.eq_of_compare heq
    subst heq
    dsimp only
    split
    · simp
    · simp
    rename_i heq
    have := Std.LawfulEqOrd.eq_of_compare heq
    intro heq
    have := compareVectBytes_LawfulEq _ _ heq
    grind
end

mutual
theorem compareVectBytes_Oriented
  [BytesCtors] {n: Nat}
  (v1 v2: Vect Bytes n)
  : compareVectBytes v1 v2 = (compareVectBytes v2 v1).swap
  := by
    cases v1 <;> cases v2
    · simp [compareVectBytes]
    · rename_i h1 t1 h2 t2
      simp only [compareVectBytes]
      have := compareBytes_Oriented h1 h2
      split
      · split <;> simp_all
      · split <;> simp_all
      have := compareVectBytes_Oriented t1 t2
      split <;> simp_all

theorem compareBytes_Oriented
  [BytesCtors]
  (b1 b2: Bytes)
  : compareBytes b1 b2 = (compareBytes b2 b1).swap
  := by
    let {id := id1, data := data1, dataBytes := dataBytes1} := b1
    let {id := id2, data := data2, dataBytes := dataBytes2} := b2
    simp only [compareBytes]
    have id_swap: compare id1 id2 = (compare id2 id1).swap := Std.OrientedOrd.eq_swap
    split
    · split <;> grind
    · split <;> grind
    rename_i heq
    have heq' := Std.LawfulEqOrd.eq_of_compare heq
    subst heq'
    dsimp only
    have data_swap: compare data1 data2 = (compare data2 data1).swap := Std.OrientedOrd.eq_swap
    split
    · split <;> grind
    · split <;> grind
    have dataBytes_swap := compareVectBytes_Oriented dataBytes1 dataBytes2
    split <;> grind
end

theorem mkTransitive
  {a: Type u}
  (r: a → a → Ordering)
  (hlawful: ∀ x y, (r x y) = .eq → x = y)
  (htranslt: ∀ x y z, (r x y) = .lt → (r y z) = .lt → (r x z) = .lt)
  : ∀ x y z, (r x y).isLE → (r y z).isLE → (r x z).isLE
  := by
    intros x y z
    simp only [Ordering.isLE]
    grind [cases Ordering]

mutual
theorem compareVectBytes_TransLt
  [BytesCtors] {n: Nat}
  (v1 v2 v3: Vect Bytes n)
  : (compareVectBytes v1 v2) = .lt → (compareVectBytes v2 v3) = .lt → (compareVectBytes v1 v3) = .lt
  := by
    cases v1 <;> cases v2 <;> cases v3
    · simp [compareVectBytes]
    · rename_i h1 t1 h2 t2 h3 t3
      simp only [compareVectBytes]
      intros h12 h23
      split at h12 <;> rename_i h_cmp12
      · split at h23 <;> rename_i h_cmp23
        · have := compareBytes_TransLt h1 h2 h3 h_cmp12 h_cmp23
          grind
        · contradiction
        · have h_eq23 := compareBytes_LawfulEq h2 h3 h_cmp23
          grind
      · contradiction
      · have h_eq12 := compareBytes_LawfulEq h1 h2 h_cmp12
        subst h_eq12
        split at h23 <;> rename_i h_cmp23
        · rfl
        · contradiction
        · exact compareVectBytes_TransLt t1 t2 t3 h12 h23

theorem compareBytes_TransLt
  [BytesCtors]
  (b1 b2 b3: Bytes)
  : (compareBytes b1 b2) = .lt → (compareBytes b2 b3) = .lt → (compareBytes b1 b3) = .lt
  := by
    let {id := id1, data := data1, dataBytes := dataBytes1} := b1
    let {id := id2, data := data2, dataBytes := dataBytes2} := b2
    let {id := id3, data := data3, dataBytes := dataBytes3} := b3
    simp only [compareBytes]
    intro h12 h23
    split at h12 <;> rename_i h_id12
    · split at h23 <;> rename_i h_id23
      · have := Std.TransCmp.lt_trans h_id12 h_id23
        grind
      · contradiction
      · grind
    · contradiction
    · split at h23 <;> rename_i h_id23
      · grind
      · contradiction
      · have h_id12_eq := Std.LawfulEqOrd.eq_of_compare h_id12
        have h_id23_eq := Std.LawfulEqOrd.eq_of_compare h_id23
        subst h_id12_eq
        subst h_id23_eq
        dsimp only at *
        rewrite [h_id12]
        dsimp only
        split at h12 <;> rename_i h_data12
        · split at h23 <;> rename_i h_data23
          · have := Std.TransCmp.lt_trans h_data12 h_data23
            grind
          · contradiction
          · grind
        · contradiction
        · split at h23 <;> rename_i h_data23
          · grind
          · contradiction
          · have h_data12_eq := Std.LawfulEqOrd.eq_of_compare h_data12
            have h_data23_eq := Std.LawfulEqOrd.eq_of_compare h_data23
            subst h_data12_eq
            subst h_data23_eq
            simp [compareVectBytes_TransLt dataBytes1 dataBytes2 dataBytes3 h12 h23]
end

theorem compareBytes_Trans
  [BytesCtors]
  (b1 b2 b3: Bytes)
  : (compareBytes b1 b2).isLE → (compareBytes b2 b3).isLE → (compareBytes b1 b3).isLE
  := mkTransitive compareBytes compareBytes_LawfulEq compareBytes_TransLt b1 b2 b3

instance [BytesCtors]: Ord Bytes where
  compare := compareBytes

instance [BytesCtors]: Std.ReflOrd Bytes where
  compare_self {b} := compareBytes_Refl b

instance [BytesCtors]: Std.LawfulEqOrd Bytes where
  eq_of_compare {a b} := compareBytes_LawfulEq a b

instance [BytesCtors]: Std.OrientedOrd Bytes where
  eq_swap {a b} := compareBytes_Oriented a b

instance [BytesCtors]: Std.TransOrd Bytes where
  isLE_trans {a b c} := compareBytes_Trans a b c

instance [BytesCtors]: DecidableEq Bytes :=
  fun b1 b2 =>
    if h: compare b1 b2 = .eq then
      .isTrue (Std.LawfulEqOrd.eq_of_compare h)
    else
      .isFalse (by
        intro h_eq
        subst h_eq
        exact (h Std.ReflOrd.compare_self)
      )

instance [BytesCtors]: LE Bytes := leOfOrd

class BytesCtor.HasCtorAt [BytesCtors] (id: CtorId) (ctor: outParam BytesCtor) where
  pf (id): BytesCtors.ctors id = ctor

class BytesCtor.HasCtor [BytesCtors] (ctor: BytesCtor) where
  id: CtorId
  pf: BytesCtors.ctors id = ctor

def BytesCtor.id [BytesCtors] (ctor: BytesCtor) [ctor.HasCtor]: CtorId :=
  BytesCtor.HasCtor.id ctor

instance [BytesCtors] {ctor: BytesCtor} [tc: ctor.HasCtor]: ctor.HasCtorAt ctor.id where
  pf := tc.pf

class Bytes.HasCtors [BytesCtors] (ctors: List BytesCtor) where
  tc: (id: Fin ctors.length) → ctors[id].HasCtor

structure BytesView [BytesCtors] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] where
  data: ctor.data
  dataBytes: Vect Bytes ctor.nBytes

def Bytes.view? [BytesCtors] (b: Bytes) (id: CtorId) {ctor: BytesCtor} [tc: ctor.HasCtorAt id] : Option (BytesView id) :=
  if h_id: b.id = id then
    some {
      data := tc.pf ▸ h_id ▸ b.data
      dataBytes := tc.pf ▸ h_id ▸ b.dataBytes,
    }
  else
    none

def BytesView.pack
  [BytesCtors]
  (id: CtorId) {ctor: BytesCtor} [tc: ctor.HasCtorAt id]
  (b: BytesView id)
  : Bytes
  :=
  {
    id := id,
    data := tc.pf ▸ b.data,
    dataBytes := tc.pf ▸ b.dataBytes,
  }

theorem Bytes.pack_view?
  [BytesCtors]
  (b: Bytes)
  (id: CtorId) {ctor: BytesCtor} [tc: ctor.HasCtorAt id]
  :
  match b.view? id with
  | some bview => bview.pack = b
  | none => True
  := by
    simp only [BytesView.pack, Bytes.view?]
    cases b
    grind

grind_pattern Bytes.pack_view? => b.view? id

theorem BytesView.view_pack
  [BytesCtors] {id: CtorId} {ctor: BytesCtor} [ctor.HasCtorAt id]
  (b: BytesView id)
  : (b.pack).view? id = some b
  := by
    simp only [BytesView.pack, Bytes.view?]
    cases b
    grind

grind_pattern BytesView.view_pack => b.pack

structure BytesFunCtor.Internal [BytesCtors] (ctor: BytesCtor) (a: Type u) where
  func: ctor.data → Vect Bytes ctor.nBytes → (Bytes → a) → a
  func_wf:
    ∀ data dataBytes rec1 rec2,
      (∀ b, sizeOf b < sizeOf dataBytes → rec1 b = rec2 b) →
      func data dataBytes rec1 = func data dataBytes rec2
    := by
      intro data dataBytes rec1 rec2
      -- The following is equivalent `let V[b1, b2, ...] := dataBytes`
      repeat (
        cases dataBytes
        rename_i b dataBytes
        -- if dataBytes was a Vect.nil, the following will fail
        obtain dataBytes: Vect _ _ := dataBytes
      )
      -- destruct the Vect.nil
      cases dataBytes
      simp_all +arith

def BytesFunCtor.ById [BytesCtors] (id: CtorId) (a: Type u) := BytesFunCtor.Internal (BytesCtors.ctors id) a
def BytesFunCtor [BytesCtors] (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id] (a: Type u) := BytesFunCtor.Internal ctor a

def BytesFunCtor.into
  [BytesCtors] {id: CtorId} {a: Type u} {ctor: BytesCtor} [ctor.HasCtorAt id]
  (f: BytesFunCtor id a)
  : BytesFunCtor.ById id a
  :=
  {
    func data dataBytes rec := f.func (BytesCtor.HasCtorAt.pf id ▸ data) (BytesCtor.HasCtorAt.pf id ▸ dataBytes) rec
    func_wf := BytesCtor.HasCtorAt.pf id ▸ f.func_wf
  }

def BytesFunCtors [BytesCtors] (a: Type u) :=
  (id: CtorId) → BytesFunCtor.ById id a

noncomputable
def Bytes.mkRec
  [BytesCtors]
  {a: Type u}
  (funs: BytesFunCtors a)
  (default: a)
  (b: Bytes)
  : a
  :=
    let {id, data, dataBytes} := b
    (funs id).func data dataBytes (fun bChild =>
      if sizeOf bChild < sizeOf dataBytes then
        mkRec funs default bChild
      else
        default
    )

theorem Bytes.mkRec.eq
  [BytesCtors]
  {a: Type u}
  (funs: BytesFunCtors a)
  (default: a)
  (b: Bytes)
  : Bytes.mkRec funs default b = (funs b.id).func b.data b.dataBytes (Bytes.mkRec funs default)
  := by
    unfold Bytes.mkRec
    cases b
    rename_i id data dataBytes
    apply (funs id).func_wf
    grind

theorem Bytes.mkRec.eqView
  [BytesCtors]
  (id: CtorId) {ctor: BytesCtor} [ctor.HasCtorAt id]
  {a: Type u}
  (funs: BytesFunCtors a)
  (default: a)
  (func: BytesFunCtor id a)
  (pf: funs id = func.into)
  (b: BytesView id)
  : Bytes.mkRec funs default (b.pack) = func.func b.data b.dataBytes (Bytes.mkRec funs default)
  := by
    rewrite [Bytes.mkRec.eq funs default b.pack]
    simp_all [BytesView.pack, BytesFunCtor.into]
    grind

def Bytes.Proof [BytesCtors] (p: Bytes → Prop) :=
  ∀ id data dataBytes,
    (∀ b, sizeOf b < sizeOf dataBytes → p b) →
    p ({id, data, dataBytes})

theorem Bytes.proveRec
  [BytesCtors]
  (p: Bytes → Prop)
  (pf: Bytes.Proof p)
  (b: Bytes)
  : p b
  :=
    let {id, data, dataBytes} := b
    pf id data dataBytes (fun b _ => Bytes.proveRec p pf b)

def BytesFunCtorProof1.Internal [BytesCtors] {ctor: BytesCtor} {a: Type u} (func: Bytes → a) (f: BytesFunCtor.Internal ctor a) (p: a → Prop) :=
  ∀ data dataBytes,
    (∀ b, sizeOf b < sizeOf dataBytes → p (func b)) →
    p (f.func data dataBytes func)

def BytesFunCtorProof1.ById [BytesCtors] {id: CtorId} {a: Type u} (func: Bytes → a) (f: BytesFunCtor.ById id a) (p: a → Prop) := BytesFunCtorProof1.Internal func f p

def BytesFunCtorProof1 [BytesCtors] {id: CtorId} {ctor: BytesCtor} [ctor.HasCtorAt id] {a: Type u} (func: Bytes → a) (f: BytesFunCtor id a) (p: a → Prop) := BytesFunCtorProof1.Internal func f p

def BytesFunCtorProof1.into
  [BytesCtors] {id: CtorId} {ctor: BytesCtor} [ctor.HasCtorAt id] {a: Type u}
  {func: Bytes → a} {f: BytesFunCtor id a} {p: a → Prop}
  (pf: BytesFunCtorProof1 func f p)
  : BytesFunCtorProof1.ById func f.into p
  := fun data dataBytes pfRec =>
    pf (BytesCtor.HasCtorAt.pf id ▸ data) (BytesCtor.HasCtorAt.pf id ▸ dataBytes) (BytesCtor.HasCtorAt.pf id ▸ pfRec)

def BytesFunCtorsProof1 [BytesCtors] {a: Type u} (f: BytesFunCtors a) (default: a) (p: a → Prop) :=
  (id: CtorId) → BytesFunCtorProof1.ById (Bytes.mkRec f default) (f id) p

def BytesFunCtorsProof1.prove
  [BytesCtors]
  {a: Type u}
  {funs: BytesFunCtors a} {default: a} {p: a → Prop}
  (pfuns: BytesFunCtorsProof1 funs default p)
  (b: Bytes)
  : p (Bytes.mkRec funs default b)
  := by
    apply Bytes.proveRec (fun b => p (Bytes.mkRec funs default b))
    intros id data dataBytes pfRec
    rewrite [Bytes.mkRec.eq funs default {id, data, dataBytes}]
    exact pfuns _ _ _ pfRec

def BytesFunCtorProof2.Internal [BytesCtors] {ctor: BytesCtor} {a: Type u} {b: Type v} (func1: Bytes → a) (func2: Bytes → b) (f1: BytesFunCtor.Internal ctor a) (f2: BytesFunCtor.Internal ctor b) (p: a × b → Prop) :=
  ∀ data dataBytes,
    (∀ b, sizeOf b < sizeOf dataBytes → p (func1 b, func2 b)) →
    p (f1.func data dataBytes func1, f2.func data dataBytes func2)

def BytesFunCtorProof2.ById [BytesCtors] {id: CtorId} {a: Type u} {b: Type v} (func1: Bytes → a) (func2: Bytes → b) (f1: BytesFunCtor.ById id a) (f2: BytesFunCtor.ById id b) (p: a × b → Prop) := BytesFunCtorProof2.Internal func1 func2 f1 f2 p

def BytesFunCtorProof2 [BytesCtors] {id: CtorId} {ctor: BytesCtor} [ctor.HasCtorAt id] {a: Type u} {b: Type v} (func1: Bytes → a) (func2: Bytes → b) (f1: BytesFunCtor id a) (f2: BytesFunCtor id b) (p: a × b → Prop) := BytesFunCtorProof2.Internal func1 func2 f1 f2 p

def BytesFunCtorProof2.into
  [BytesCtors] {id: CtorId} {ctor: BytesCtor} [ctor.HasCtorAt id] {a: Type u} {b: Type v}
  {func1: Bytes → a} {func2: Bytes → b} {f1: BytesFunCtor id a} {f2: BytesFunCtor id b} {p: a × b → Prop}
  (pf: BytesFunCtorProof2 func1 func2 f1 f2 p)
  : BytesFunCtorProof2.ById func1 func2 f1.into f2.into p
  := fun data dataBytes pfRec =>
    pf (BytesCtor.HasCtorAt.pf id ▸ data) (BytesCtor.HasCtorAt.pf id ▸ dataBytes) (BytesCtor.HasCtorAt.pf id ▸ pfRec)

def BytesFunCtorsProof2 [BytesCtors] {a: Type u} {b: Type v} (f1: BytesFunCtors a) (f2: BytesFunCtors b) (default1: a) (default2: b) (p: a × b → Prop) :=
  (id: CtorId) → BytesFunCtorProof2.ById (Bytes.mkRec f1 default1) (Bytes.mkRec f2 default2) (f1 id) (f2 id) p

def BytesFunCtorsProof2.prove
  [BytesCtors]
  {a: Type u} {b: Type v}
  {funs1: BytesFunCtors a} {funs2: BytesFunCtors b}
  {default1: a} {default2: b}
  {p: a × b → Prop}
  (pfuns: BytesFunCtorsProof2 funs1 funs2 default1 default2 p)
  (b: Bytes)
  : p (Bytes.mkRec funs1 default1 b, Bytes.mkRec funs2 default2 b)
  := by
    apply Bytes.proveRec (fun b => p (Bytes.mkRec funs1 default1 b, Bytes.mkRec funs2 default2 b))
    intros id data dataBytes pfRec
    rewrite [Bytes.mkRec.eq funs1 default1 {id, data, dataBytes}, Bytes.mkRec.eq funs2 default2 {id, data, dataBytes}]
    exact pfuns _ _ _ pfRec

end DY
