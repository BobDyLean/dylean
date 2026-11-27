module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Hash
public import DY.Actions.Network
public meta import DY.Trace.Monad
public meta import DY.EquationalTheory.Literal
public meta import DY.EquationalTheory.Concat
public meta import DY.EquationalTheory.Hash
public meta import DY.Actions.Network

namespace DY.Benchmark.BytesRuntime

#combine +toplevel into Bytes, Bytes.length from
  Literal,
  Concat,
  Hash

export Concat (concat)
export Hash (hash)

def leaf (b: UInt8): Bytes := Literal.literalToBytes (ByteArray.mk #[b])

local instance: Inhabited Bytes := ⟨leaf 0⟩

/--
  Using distinct values of `n` forces computing `f x` twice;
  otherwise, the compiler is smart
  and will coalesce two distinct `f x` calls.
-/
def force {α β: Type} (n: Nat) (f: α → β) (x: α): β :=
  if n = 0 then f x
  else force (n-1) f x

/-! ## Large `Bytes` with no sharing -/

def mkTree (n: Nat) (seed: Nat): Bytes :=
  if n = 0 then leaf (seed % 251).toUInt8
  else concat (mkTree (n-1) (2*seed)) (mkTree (n-1) (2*seed+1))

/--
  Compares two equal large `Bytes` with no sharing.
-/
def tree (n: Nat): Bool :=
  let x1 := force 1 (mkTree n) 0
  let x2 := force 2 (mkTree n) 0
  x1 = x2

-- set_option trace.profiler true in
#guard tree 16

/--
  Compares two unequal large `Bytes` with no sharing.
-/
def treeNe (n: Nat): Bool :=
  let x1 := mkTree n 0
  let x2 := mkTree n 1
  x1 ≠ x2

-- set_option trace.profiler true in
#guard treeNe 18

/-! ## Simple pointer equality benchmarks -/

/--
  Builds a big term (of size 2^n),
  but with a lot of sharing,
  hence the in-memory size is low.
-/
def mkBigShared (leaf: Bytes) (n: Nat): Bytes :=
  if n = 0 then
    leaf
  else
    let x := mkBigShared leaf (n-1)
    hash (concat x x)

/--
  Compares two `Bytes` with equal pointers.
-/
def testEqualPointer (n: Nat): Bool :=
  let x := mkBigShared (leaf 0) n
  x = x

-- set_option trace.profiler true in
#guard testEqualPointer 500000

/--
  Compares two `Bytes` with pointer-equal subterms.
-/
def testEqualPointerSubterm (n: Nat): Bool :=
  let x := mkBigShared (leaf 0) n
  let x1 := force 1 hash x
  let x2 := force 2 hash x
  x1 = x2

-- set_option trace.profiler true in
#guard testEqualPointerSubterm 500000

/--
  Compares two `Bytes` with distinct root nodes.
-/
def testHeadNe (n: Nat): Bool :=
  let x := mkBigShared (leaf 0) n
  let x1 := hash x
  let x2 := concat x x
  x1 ≠ x2

-- set_option trace.profiler true in
#guard testHeadNe 500000

/-! ## Pointer memoization benchmarks -/

/--
  Compares two `Bytes` that share no pointers,
  but have the same DAG shape.
  Requires pointer equality memoization to be fast.
-/
def testPointerMemoization (n: Nat): Bool :=
  let x1 := force 1 (mkBigShared (leaf 0)) n
  let x2 := force 2 (mkBigShared (leaf 0)) n
  x1 = x2

-- set_option trace.profiler true in
#guard testPointerMemoization 50000

/--
  Compares two `Bytes` that share no pointers,
  have the same DAG shape,
  but have different leaves
  (the test should fail fast at the first differing leaf,
  without traversing the whole DAG).
-/
def testLeafNe (n: Nat): Bool :=
  let x1 := mkBigShared (leaf 0) n
  let x2 := mkBigShared (leaf 1) n
  x1 ≠ x2

-- set_option trace.profiler true in
#guard testLeafNe 100000

def mkLevel (w: Nat) (prev: Array Bytes) (shift: Nat): Array Bytes :=
  (List.range w).toArray.map fun i => concat prev[i]! prev[(i + shift) % w]!

def mkMisaligned (w d: Nat) (shiftAt: Nat → Nat): Bytes := Id.run do
  let mut lvl := (List.range w).toArray.map fun i => force i (mkTree d) 0
  for k in 0...4*w do
    lvl := mkLevel w lvl (shiftAt k)
  return lvl[0]!
/--
  Compares two `Bytes` designed to exhibit quadratic behavior
  for algorithms that do pointer memoization
  by remembering pairs of pointers found equal
  (instead of using a union-find structure).
  Fact: each leaf of x1 is compared with each leaf of x2.
  Proof sketch:
  within depth ≤ 2*w, we can choose the distance between the indices being compared
  (always compare the right nodes: x1 shifts twice as fast as x2);
  then within depth ≤ 2*w, we can shift both indices wherever we want
  (alternate between left and right, to go right when both x1 and x2 move right).
  Finally, each leaf is a moderately expensive comparison to perform (using `mkTree`).
-/
def testMisaligned (w d: Nat): Bool :=
  let x1 := mkMisaligned w d (fun _ => 1)
  let x2 := mkMisaligned w d (fun k => k % 2)
  x1 = x2

-- set_option trace.profiler true in
#guard testMisaligned 128 7

/-! ## Many small `Bytes` -/

def mkSmall (i: Nat): Bytes :=
  concat (hash (leaf (i % 256).toUInt8)) (concat (leaf ((i / 256) % 256).toUInt8) (leaf 7))

def manySmall (n: Nat): Bool :=
  (List.range n).all fun i => force 1 mkSmall i = force 2 mkSmall i

-- set_option trace.profiler true in
#guard manySmall 50000

def manySmallNe (n: Nat): Bool :=
  (List.range n).all fun i => (force 1 mkSmall i ≠ force 2 mkSmall (i+1))

-- set_option trace.profiler true in
#guard manySmallNe 50000

/-! ## Folds (typical of Comparse message formats) -/

def mkListLeft (n: Nat) (seed: Nat): Bytes :=
  if n = 0 then leaf 0
  else concat (mkListLeft (n-1) seed) (leaf ((seed + n) % 251).toUInt8)

def testListsLeft (n m: Nat): Bool :=
  (List.range m).all fun i => force 1 (mkListLeft n) i = force 2 (mkListLeft n) i

-- set_option trace.profiler true in
#guard testListsLeft 1000 100

def testListsLeftNe (n m: Nat): Bool :=
  (List.range m).all fun i => force 1 (mkListLeft n) i ≠ force 2 (mkListLeft n) (i+1)

-- set_option trace.profiler true in
#guard testListsLeftNe 1000 100

def mkListRight (n: Nat) (seed: Nat): Bytes :=
  if n = 0 then leaf 0
  else concat (leaf ((seed + n) % 251).toUInt8) (mkListRight (n-1) seed)

def testListsRight (n m: Nat): Bool :=
  (List.range m).all fun i => force 1 (mkListRight n) i = force 2 (mkListRight n) i

-- set_option trace.profiler true in
#guard testListsRight 1000 100

def testListsRightNe (n m: Nat): Bool :=
  (List.range m).all fun i => force 1 (mkListRight n) i ≠ force 2 (mkListRight n) (i+1)

-- set_option trace.profiler true in
#guard testListsRightNe 1000 100
