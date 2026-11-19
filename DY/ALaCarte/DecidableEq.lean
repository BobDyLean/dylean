/-
  This module allows deriving `DecidableEq`
  on inductive types defined modularly through the "à la carte" system.
-/

module

public import DY.ALaCarte.Basic
public import Std.Data.HashMap
public import Lean.Data.UnionFind

namespace DY.ALaCarte

theorem BareContainer.decideEquality.aux
  {α: Type} [SizeOf α]
  (l1 l2: Array α)
  (h1: ∀ x, x ∈ l1 → sizeOf x < max (sizeOf l1) (sizeOf l2))
  (h2: ∀ x, x ∈ l2 → sizeOf x < max (sizeOf l1) (sizeOf l2))
  : (l1.attachWith _ h1 = l2.attachWith _ h2) = (l1 = l2)
:= by
  grind [Array.unattach_attachWith]

def BareContainer.decideEquality
  {CtorId} {ctors: Ctors CtorId}
  [DecidableEq CtorId]
  [∀ id, DecidableEq (ctors id).Data]
  (x1 x2: BareContainer ctors)
  : Decidable (x1 = x2)
:= by
  let { id := id1, data := data1, as := as1 } := x1
  let { id := id2, data := data2, as := as2 } := x2
  simp only [BareContainer.mk.injEq]
  by_cases (decide (id1 = id2)) <;> rename_i h_id
  · simp only [decide_eq_true_eq] at h_id
    subst h_id
    simp only [heq_eq_eq, true_and]
    by_cases (decide (data1 = data2)) <;> rename_i h_data
    · simp only [decide_eq_true_eq] at h_data
      subst h_data
      simp only [true_and]
      rewrite [← BareContainer.decideEquality.aux]
      · refine @Array.instDecidableEq _ ?_ _ _
        intro ⟨x1, h_x1⟩ ⟨x2, h_x2⟩
        simp only [Subtype.mk.injEq]
        apply BareContainer.decideEquality
      all_goals
      intro x h_x
      have := Array.sizeOf_lt_of_mem h_x
      grind
    · apply Decidable.isFalse
      simp_all
  · apply Decidable.isFalse
    simp_all
termination_by max (sizeOf x1) (sizeOf x2)

public
def Container.decideEquality
  {CtorId} {ctors: Ctors CtorId}
  [DecidableEq CtorId]
  [∀ id, DecidableEq (ctors id).Data]
  (x1 x2: Container ctors)
  : Decidable (x1 = x2)
:= by
  cases x1
  cases x2
  rewrite [Subtype.mk.injEq]
  apply BareContainer.decideEquality

public
class RepresentableDecidableEq (f: Type → Type) [FunctorSizeOf f] [Representable f] where
  ctorid_deq: DecidableEq (Representable.CtorId f) := by
    simp only [DY.ALaCarte.Representable.CtorId]
    exact inferInstance
  ctor_data_deq: ∀ id, DecidableEq (Representable.ctors (f := f) id).Data := by
    intro id
    simp only [DY.ALaCarte.Representable.ctors]
    cases id <;>
    exact inferInstance

/-!
## Optimized runtime implementation of decidable equality for `BareContainer`

Although `BareContainer` represents a tree,
in practice, its runtime in-memory representation is a DAG:
two subtrees at different positions might share the same pointer.
However, the `DecidableEq` instance cannot exploit this sharing,
and always walks both trees in their entirety.
There are many ways to create `BareContainer`s that have a small DAG representation
but trick `DecidableEq` into exponential behavior
(see the corresponding benchmark file for some examples).
Such exponential behavior can happen in practice on real protocols:
for example, in MLS (RFC 9420), the term for epoch_secret_{n+1} contains the term for epoch_secret_{n} three times:
once via ratcheting, and twice via injection of the group context
(which contains the transcript hash, hence the confirmation tag, hence confirmation_key_{n}, hence epoch_secret_{n}).

Tricks to optimize the complexity:
- when comparing two subtrees, if they have the same pointer, shortcut and directly return `true`
- when two subtrees with different pointers have been compared and found equal,
  this is recorded in a union-find data structure,
  and looking up the equivalence classes of pointers is also used as a shortcut

Tricks to optimize for the constant factor:
- the code is written in a way to perform at most two `classOf` hashmap lookups per call to `BareContainer.beqNode`
- the code is written to exploit Lean's Functional-But-In-Place mechanism (e.g. by using `modifyGet`)
- memoization is skipped for small subtrees (those whose children are all leaves)
- memoization is skipped for the root
- when recording equality of two pointers,
  avoid creating two union-find nodes just before merging them:
  instead, create only one node for both pointers
- using tail recursion instead of `for` loops seems to be slightly faster

Tricks to optimize the constant factor that are not implemented:
- Skip memoization for nodes that have reference count = 1 (accessed via `isExclusiveUnsafe`).
  This is actually tricky to implement without corner case that lead to complexity loss,
  and this does not work in interpreted execution (e.g. `native_decide`, `#guard` or `#eval`).
  In native execution, however, this brings a ~10x performance gain.

The soundness of this implementation relies on the following:
- pointer equality implies logical equality
- the pointer for a subtree that was memoized is not used for something else during the comparison

Regarding the stability of pointers during the walk:
because the tree root stays live,
so do all of its subtrees.

Regarding pointer equality implying logical equality,
this is a bit tricky because `BareContainer` contains
types that are user-provided,
and although it holds in general for "normal" user-defined types,
there are a bunch of counterexamples,
see e.g. https://github.com/leanprover/lean4/issues/1502 .
In other words,
this optimization is sound for "normal" equational theories,
but could be broken by adversarial equational theories.

This tradeoff is worth it:
it unlocks an exponential speedup in some sanity checks (such as MLS),
it is sound for honest equational theories,
and its unsoundness regarding adversarial equational theories
only affects e.g. `native_decide`,
not the security theorems that are checked by Lean's kernel
and do not rely on `native_decide`.
-/

section Runtime

variable {CtorId} {ctors: Ctors CtorId} [DecidableEq CtorId] [∀ id, DecidableEq (ctors id).Data]

namespace BareContainer

@[inline]
unsafe def headEqUnsafe (x1 x2: @& BareContainer ctors): Bool :=
  if h: x1.id = x2.id then
    if ptrAddrUnsafe x1.data == ptrAddrUnsafe x2.data then true
    else decide (cast (congrArg (fun id => (ctors id).Data) h) x1.data = x2.data)
  else
    false

structure EqMemo where
  classOf: Std.HashMap USize Nat := {}
  classes: Lean.UnionFind := {}

@[inline]
def EqMemo.classOf? (addr: USize): StateM BareContainer.EqMemo (Option Nat) :=
  return (← get).classOf[addr]?

@[inline]
def EqMemo.knownEqual (classA? classB?: Option Nat): StateM BareContainer.EqMemo Bool :=
  match classA?, classB? with
  | some classA, some classB =>
    -- shortcut to avoid a union-find lookup
    if classA == classB then
      return true
    else
      modifyGet fun ⟨classOf, classes⟩ =>
        let (classes, eq) := classes.checkEquiv! classA classB
        (eq, ⟨classOf, classes⟩)
  | _, _ => return false

@[inline]
def EqMemo.recordEqual (addrA addrB: USize) (classA? classB?: Option Nat): StateM EqMemo Unit :=
  modify fun ⟨classOf, classes⟩ =>
    match classA?, classB? with
    | some classA, some classB => ⟨classOf, classes.union! classA classB⟩
    | some classA, none => ⟨classOf.insert addrB classA, classes⟩
    | none, some classB => ⟨classOf.insert addrA classB, classes⟩
    | none, none =>
      let (classes, fresh) := classes.push
      ⟨(classOf.insert addrA fresh).insert addrB fresh, classes⟩

@[inline]
def allLeaves (as: @& Array (BareContainer ctors)): Bool :=
  go 0
where
  go (i: Nat): Bool :=
    if h: i < as.size then as[i].as.size == 0 && go (i+1) else true
  termination_by as.size - i

@[inline]
def skipMemo (a: @& BareContainer ctors): Bool :=
  allLeaves a.as

/--
  The equality algorithm is structured as follows:
  - `beqNode` is in charge of shortcuts and memoization, and calls `structural` if no shortcut is possible
  - `structural` tests equality of the id and data, and recurses on the children
  - `children` is a loop (tail-recursive function) which calls `beqNode` on each child
-/
unsafe def beqNode (a b: @& BareContainer ctors): StateM EqMemo Bool := do
  -- shortcut if `a` and `b` have equal pointers
  if ptrEq a b then return true
  -- if memoization is not worth it, skip and call `structural`
  if skipMemo a then return ← structural a b
  -- otherwise, do memoization lookup / record
  let addrA := ptrAddrUnsafe a
  let addrB := ptrAddrUnsafe b
  let classA? ← EqMemo.classOf? addrA
  let classB? ← EqMemo.classOf? addrB
  -- memoization shortcut
  if ← EqMemo.knownEqual classA? classB? then return true
  -- if no shortcut was available, do structural comparison
  if !(← structural a b) then return false
  -- and record the result in the memoization if found equal
  EqMemo.recordEqual addrA addrB classA? classB?
  return true
where
  structural (a b: @& BareContainer ctors): StateM EqMemo Bool := do
    -- first compare arity (cheapest)
    if _: a.as.size != b.as.size then return false else
    -- then compare id (which is in practice a product of `Fin`) and data
    if !headEqUnsafe a b then return false
    -- then recurse on the children
    children a.as b.as 0 (by grind)
  children (as1 as2: @& Array (BareContainer ctors)) (i: Nat) (h: as1.size = as2.size): StateM EqMemo Bool := do
    if _: i < as1.size then
      if !(← beqNode as1[i] as2[i]) then return false
      children as1 as2 (i+1) h
    else return true

unsafe def beqUnsafe (x1 x2: @& BareContainer ctors): Bool :=
  -- don't memoize the root node (i.e. don't call `beqNode`);
  -- instead, do a simple pointer-equality shortcut + call `structural`
  if ptrEq x1 x2 then true
  else (beqNode.structural x1 x2).run' {}

@[implemented_by beqUnsafe]
public
def beq (x1 x2: @& BareContainer ctors): Bool :=
  @decide _ (BareContainer.decideEquality x1 x2)

public
theorem beq_iff (x1 x2: BareContainer ctors): BareContainer.beq x1 x2 = true ↔ x1 = x2 := by
  simp only [beq, decide_eq_true_iff]

end BareContainer

public
def Container.beq (x1 x2: Container ctors): Bool :=
  BareContainer.beq x1.val x2.val

public
theorem Container.beq_iff (x1 x2: Container ctors): Container.beq x1 x2 = true ↔ x1 = x2 := by
  simp only [Container.beq, BareContainer.beq_iff, Subtype.ext_iff]

end Runtime

public
instance (f: Type → Type) [FunctorSizeOf f] [Representable f] [RepresentableDecidableEq f]: DecidableEq (ContainerFor f) :=
  fun x1 x2 =>
    have := RepresentableDecidableEq.ctorid_deq (f := f)
    have := RepresentableDecidableEq.ctor_data_deq (f := f)
    decidable_of_iff (Container.beq x1 x2 = true) (Container.beq_iff x1 x2)

public
instance {a: Type} [DecidableEq a] (fs: a → Type → Type) [∀ id, FunctorSizeOf (fs id)] [∀ id, Representable (fs id)] [∀ id, RepresentableDecidableEq (fs id)]: RepresentableDecidableEq (FunctorUnion fs) where
  ctorid_deq := by
    intro { idHead := idHead1, idTail := idTail1 } { idHead := idHead2, idTail := idTail2 }
    by_cases decide (idHead1 = idHead2) <;> rename_i h_idHead
    · simp only [decide_eq_true_eq] at h_idHead
      subst h_idHead
      have := RepresentableDecidableEq.ctorid_deq (f := fs idHead1)
      by_cases (decide (idTail1 = idTail2))
      · apply Decidable.isTrue
        grind
      · apply Decidable.isFalse
        grind
    · apply Decidable.isFalse
      grind
  ctor_data_deq id := (RepresentableDecidableEq.ctor_data_deq (f := fs id.idHead)) id.idTail

end DY.ALaCarte
