module

public import Comparse.Formats.Basic
import all Comparse.Formats.Basic

namespace Comparse

variable {Bytes: Type} [BytesLike Bytes]

public
def NonExtensibleMessageFormat.isomorphic
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  : NonExtensibleMessageFormat Bytes b
:=
  subsetIsomorphic mf (fun x => some (f x)) g

public
class LeftInverse (g: b → a) (f: a → b) where
  left_inv (g f): Function.LeftInverse g f

public
class RightInverse (g: b → a) (f: a → b) where
  right_inv (g f): Function.RightInverse g f

namespace NonExtensibleMessageFormat.isomorphic

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  [mf.IsNonAmbiguous]
  [RightInverse g f]
  : (isomorphic mf f g).IsNonAmbiguous
:= by
  dsimp only [isomorphic]
  have: SubsetRightInverse g (fun x => some (f x)) := by
    apply SubsetRightInverse.mk
    have := RightInverse.right_inv g f
    grind
  infer_instance

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  [mf.HasUniqueRepresentation]
  [LeftInverse g f]
  : (isomorphic mf f g).HasUniqueRepresentation
:= by
  dsimp only [isomorphic]
  have: SubsetLeftInverse g (fun x => some (f x)) := by
    apply SubsetLeftInverse.mk
    have := LeftInverse.left_inv g f
    grind
  infer_instance

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  [mf.ParseConsumes]
  : (isomorphic mf f g).ParseConsumes
:= by
  dsimp only [isomorphic]
  infer_instance

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: b)
  : (isomorphic mf f g).wf pred x = mf.wf pred (g x)
:= by
  simp [isomorphic]

end NonExtensibleMessageFormat.isomorphic

public
def NonExtensibleMessageFormat.triviallyIsomorphic
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (_: Function.LeftInverse g f := by intro; rfl)
  (_: Function.RightInverse g f := by intro; rfl)
  : NonExtensibleMessageFormat Bytes b
:=
  isomorphic mf f g

namespace NonExtensibleMessageFormat.triviallyIsomorphic

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  [mf.IsNonAmbiguous]
  : (triviallyIsomorphic mf f g h_left h_right).IsNonAmbiguous
:= by
  dsimp only [triviallyIsomorphic]
  have: RightInverse g f := { right_inv := h_right }
  infer_instance

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  [mf.HasUniqueRepresentation]
  : (triviallyIsomorphic mf f g h_left h_right).HasUniqueRepresentation
:= by
  dsimp only [triviallyIsomorphic]
  have: LeftInverse g f := { left_inv := h_left }
  infer_instance

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  [mf.ParseConsumes]
  : (triviallyIsomorphic mf f g h_left h_right).ParseConsumes
:= by
  dsimp only [triviallyIsomorphic]
  infer_instance

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: b)
  : (triviallyIsomorphic mf f g h_left h_right).wf pred x = mf.wf pred (g x)
:= by
  simp [triviallyIsomorphic]

end NonExtensibleMessageFormat.triviallyIsomorphic

public
def ExtensibleMessageFormat.isomorphic
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  : ExtensibleMessageFormat Bytes b
:=
  subsetIsomorphic mf (fun x => some (f x)) g

namespace ExtensibleMessageFormat.isomorphic

public
instance
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  [mf.IsNonAmbiguous]
  [RightInverse g f]
  : (isomorphic mf f g).IsNonAmbiguous
:= by
  dsimp only [isomorphic]
  have: SubsetRightInverse g (fun x => some (f x)) := by
    apply SubsetRightInverse.mk
    have := RightInverse.right_inv g f
    grind
  infer_instance

public
instance
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  [mf.HasUniqueRepresentation]
  [LeftInverse g f]
  : (isomorphic mf f g).HasUniqueRepresentation
:= by
  dsimp only [isomorphic]
  have: SubsetLeftInverse g (fun x => some (f x)) := by
    apply SubsetLeftInverse.mk
    have := LeftInverse.left_inv g f
    grind
  infer_instance

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: b)
  : (isomorphic mf f g).wf pred x = mf.wf pred (g x)
:= by
  simp [isomorphic]

end ExtensibleMessageFormat.isomorphic

public
def ExtensibleMessageFormat.triviallyIsomorphic
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (_: Function.LeftInverse g f := by intro; rfl)
  (_: Function.RightInverse g f := by intro; rfl)
  : ExtensibleMessageFormat Bytes b
:=
  isomorphic mf f g

namespace ExtensibleMessageFormat.triviallyIsomorphic

public
instance
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  [mf.IsNonAmbiguous]
  : (triviallyIsomorphic mf f g h_left h_right).IsNonAmbiguous
:= by
  dsimp only [triviallyIsomorphic]
  have: RightInverse g f := { right_inv := h_right }
  infer_instance

public
instance
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  [mf.HasUniqueRepresentation]
  : (triviallyIsomorphic mf f g h_left h_right).HasUniqueRepresentation
:= by
  dsimp only [triviallyIsomorphic]
  have: LeftInverse g f := { left_inv := h_left }
  infer_instance

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → b) (g: b → a)
  (h_left: Function.LeftInverse g f)
  (h_right: Function.RightInverse g f)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: b)
  : (triviallyIsomorphic mf f g h_left h_right).wf pred x = mf.wf pred (g x)
:= by
  simp [triviallyIsomorphic]

end ExtensibleMessageFormat.triviallyIsomorphic

def NonExtensibleMessageFormat.subtype.f
  {a: Type}
  {p: a → Prop} [DecidablePred p]
  (x: a)
  : Option (Subtype p)
:=
  if h: p x then
    some ⟨x, h⟩
  else
    none

def NonExtensibleMessageFormat.subtype.g
  {a: Type}
  {p: a → Prop}
  (x: Subtype p)
  : a
:=
  x.val

public
def NonExtensibleMessageFormat.subtype
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  : NonExtensibleMessageFormat Bytes (Subtype p)
:=
  subsetIsomorphic mf subtype.f subtype.g

namespace NonExtensibleMessageFormat.subtype

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.IsNonAmbiguous]
  : (mf.subtype p).IsNonAmbiguous
:= by
  dsimp only [subtype]
  have: SubsetRightInverse g (f (p := p)) := by
    apply SubsetRightInverse.mk
    simp [f, g]
  infer_instance

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.HasUniqueRepresentation]
  : (mf.subtype p).HasUniqueRepresentation
:= by
  dsimp only [subtype]
  have: SubsetLeftInverse g (f (p := p)) := by
    apply SubsetLeftInverse.mk
    simp [f, g]
    grind
  infer_instance

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.ParseConsumes]
  : (mf.subtype p).ParseConsumes
:= by
  dsimp only [subtype]
  infer_instance

@[simp]
public
theorem wf_eq
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Subtype p)
  : (subtype mf p).wf pred x = mf.wf pred x.val
:= by
  simp [subtype, subtype.g]

end NonExtensibleMessageFormat.subtype

def ExtensibleMessageFormat.subtype.f
  {a: Type}
  {p: a → Prop} [DecidablePred p]
  (x: a)
  : Option (Subtype p)
:=
  if h: p x then
    some ⟨x, h⟩
  else
    none

def ExtensibleMessageFormat.subtype.g
  {a: Type}
  {p: a → Prop}
  (x: Subtype p)
  : a
:=
  x.val

public
def ExtensibleMessageFormat.subtype
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  : ExtensibleMessageFormat Bytes (Subtype p)
:=
  subsetIsomorphic mf subtype.f subtype.g

namespace ExtensibleMessageFormat.subtype

public
instance
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.IsNonAmbiguous]
  : (mf.subtype p).IsNonAmbiguous
:= by
  dsimp only [subtype]
  have: SubsetRightInverse g (f (p := p)) := by
    apply SubsetRightInverse.mk
    simp [f, g]
  infer_instance

public
instance
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.HasUniqueRepresentation]
  : (mf.subtype p).HasUniqueRepresentation
:= by
  dsimp only [subtype]
  have: SubsetLeftInverse g (f (p := p)) := by
    apply SubsetLeftInverse.mk
    simp [f, g]
    grind
  infer_instance

@[simp]
public
theorem wf_eq
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Subtype p)
  : (subtype mf p).wf pred x = mf.wf pred x.val
:= by
  simp [subtype, subtype.g]

end ExtensibleMessageFormat.subtype

def NonExtensibleMessageFormat.prod.f {a b: Type} (v: (_: a) × b) : a × b :=
  let ⟨ x, y ⟩ := v
  ⟨ x, y ⟩

def NonExtensibleMessageFormat.prod.g {a b: Type} (v: a × b) : (_: a) × b :=
  let ⟨ x, y ⟩ := v
  ⟨ x, y ⟩

public
def NonExtensibleMessageFormat.prod
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: NonExtensibleMessageFormat Bytes b)
  : NonExtensibleMessageFormat Bytes (Prod a b)
:=
  .isomorphic (.sigma mfa (fun _ => mfb)) prod.f prod.g

namespace NonExtensibleMessageFormat.prod

local instance: RightInverse (@g a b) f where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, f, g]

local instance: LeftInverse (@g a b) f where
  left_inv := by simp [Function.LeftInverse, f, g]

public
instance
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: NonExtensibleMessageFormat Bytes b)
  [mfa.IsNonAmbiguous]
  [mfb.IsNonAmbiguous]
  : (prod mfa mfb).IsNonAmbiguous
:= by
  dsimp only [prod]
  infer_instance

public
instance
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: NonExtensibleMessageFormat Bytes b)
  [mfa.HasUniqueRepresentation]
  [mfb.HasUniqueRepresentation]
  : (prod mfa mfb).HasUniqueRepresentation
:= by
  dsimp only [prod]
  infer_instance

public
instance
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: NonExtensibleMessageFormat Bytes b)
  [mfa.ParseConsumes]
  : (prod mfa mfb).ParseConsumes
:= by
  dsimp only [prod]
  infer_instance

public
instance
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: NonExtensibleMessageFormat Bytes b)
  [mfb.ParseConsumes]
  : (prod mfa mfb).ParseConsumes
:= by
  dsimp only [prod]
  infer_instance

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: NonExtensibleMessageFormat Bytes b)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: a × b)
  : (prod mfa mfb).wf pred x = ((mfa.wf pred x.fst) ∧ (mfb.wf pred x.snd))
:= by
  simp [prod, g]

end NonExtensibleMessageFormat.prod

def ExtensibleMessageFormat.prod.f {a b: Type} (v: (_: a) × b) : a × b :=
  let ⟨ x, y ⟩ := v
  ⟨ x, y ⟩

def ExtensibleMessageFormat.prod.g {a b: Type} (v: a × b) : (_: a) × b :=
  let ⟨ x, y ⟩ := v
  ⟨ x, y ⟩

public
def ExtensibleMessageFormat.prod
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: ExtensibleMessageFormat Bytes b)
  : ExtensibleMessageFormat Bytes (Prod a b)
:=
  .isomorphic (.sigma mfa (fun _ => mfb)) prod.f prod.g

namespace ExtensibleMessageFormat.prod

local instance: RightInverse (@g a b) f where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, f, g]

local instance: LeftInverse (@g a b) f where
  left_inv := by simp [Function.LeftInverse, f, g]

public
instance
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: ExtensibleMessageFormat Bytes b)
  [mfa.IsNonAmbiguous]
  [mfb.IsNonAmbiguous]
  : (prod mfa mfb).IsNonAmbiguous
:= by
  dsimp only [prod]
  infer_instance

public
instance
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: ExtensibleMessageFormat Bytes b)
  [mfa.HasUniqueRepresentation]
  [mfb.HasUniqueRepresentation]
  : (prod mfa mfb).HasUniqueRepresentation
:= by
  dsimp only [prod]
  infer_instance

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: ExtensibleMessageFormat Bytes b)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: a × b)
  : (prod mfa mfb).wf pred x = ((mfa.wf pred x.fst) ∧ (mfb.wf pred x.snd))
:= by
  simp [prod, g]

end ExtensibleMessageFormat.prod

local instance: SubsetRightInverse BytesLike.fromByteArray (BytesLike.toByteArray (Bytes := Bytes)) where
  right_inv := by grind [BytesLike.to_from_ByteArray]

local instance: SubsetLeftInverse BytesLike.fromByteArray (BytesLike.toByteArray (Bytes := Bytes)) where
  left_inv := by grind [BytesLike.from_to_ByteArray]

public
def ExtensibleMessageFormat.byteArray: ExtensibleMessageFormat Bytes ByteArray :=
  subsetIsomorphic ExtensibleMessageFormat.bytes BytesLike.toByteArray BytesLike.fromByteArray
deriving IsNonAmbiguous, HasUniqueRepresentation

@[simp]
public
theorem ExtensibleMessageFormat.byteArray.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: ByteArray)
  : byteArray.wf pred x
:= by
  simp [byteArray, BytesCompatiblePred.pred_fromByteArray]

def ExtensibleMessageFormat.string.f (x: Subtype ByteArray.IsValidUTF8): String :=
  String.ofByteArray x.val x.property

def ExtensibleMessageFormat.string.g (x: String): Subtype ByteArray.IsValidUTF8 :=
  ⟨ x.toByteArray, x.isValidUTF8 ⟩

local instance: RightInverse ExtensibleMessageFormat.string.g ExtensibleMessageFormat.string.f where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, ExtensibleMessageFormat.string.f, ExtensibleMessageFormat.string.g]

local instance: LeftInverse ExtensibleMessageFormat.string.g ExtensibleMessageFormat.string.f where
  left_inv := by simp [Function.LeftInverse, ExtensibleMessageFormat.string.f, ExtensibleMessageFormat.string.g]

public
def ExtensibleMessageFormat.string: ExtensibleMessageFormat Bytes String :=
  isomorphic (subtype byteArray ByteArray.IsValidUTF8) string.f string.g
deriving IsNonAmbiguous, HasUniqueRepresentation

@[simp]
public
theorem ExtensibleMessageFormat.string.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: String)
  : string.wf pred x
:= by
  simp [string]

public
def NonExtensibleMessageFormat.fixedLengthBytes
  (len: Nat)
  : NonExtensibleMessageFormat Bytes ({ b: Bytes // BytesLike.length b = len})
:=
  (ExtensibleMessageFormat.subtype ExtensibleMessageFormat.bytes (fun b => BytesLike.length b = len)).toNonExtensible len (by
    simp [ExtensibleMessageFormat.subtype, ExtensibleMessageFormat.subsetIsomorphic, ExtensibleMessageFormat.bytes, ExtensibleMessageFormat.subtype.g]
  )
deriving IsNonAmbiguous, HasUniqueRepresentation

namespace NonExtensibleMessageFormat.fixedLengthBytes

public
instance (len: Nat) [NeZero len] : ParseConsumes (fixedLengthBytes len: NonExtensibleMessageFormat Bytes _) := by
  dsimp only [fixedLengthBytes]
  infer_instance

@[simp]
public
theorem wf_eq
  (len: Nat)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: { b: Bytes // BytesLike.length b = len})
  : (fixedLengthBytes len).wf pred x = pred x.val
:= by
  simp [fixedLengthBytes]

end NonExtensibleMessageFormat.fixedLengthBytes

def NonExtensibleMessageFormat.fixedLengthByteArray.f
  (len: Nat)
  (b: { b: Bytes // BytesLike.length b = len }):
  Option { b: ByteArray // b.size = len}
:=
  match _: BytesLike.toByteArray b.val with
  | none => none
  | some res =>
    some ⟨ res, by grind [BytesLike.fromByteArray_length, BytesLike.from_to_ByteArray] ⟩

def NonExtensibleMessageFormat.fixedLengthByteArray.g
  (len: Nat)
  (b: { b: ByteArray // b.size = len}):
  { b: Bytes // BytesLike.length b = len }
:=
  ⟨ BytesLike.fromByteArray b.val, by grind [BytesLike.fromByteArray_length] ⟩

local instance (len: Nat): SubsetLeftInverse (NonExtensibleMessageFormat.fixedLengthByteArray.g (Bytes := Bytes) len) (NonExtensibleMessageFormat.fixedLengthByteArray.f len) where
  left_inv := by
    simp [NonExtensibleMessageFormat.fixedLengthByteArray.f, NonExtensibleMessageFormat.fixedLengthByteArray.g]
    grind [BytesLike.from_to_ByteArray]

local instance (len: Nat): SubsetRightInverse (NonExtensibleMessageFormat.fixedLengthByteArray.g (Bytes := Bytes) len) (NonExtensibleMessageFormat.fixedLengthByteArray.f len) where
  right_inv := by
    simp [NonExtensibleMessageFormat.fixedLengthByteArray.f, NonExtensibleMessageFormat.fixedLengthByteArray.g]
    grind [BytesLike.to_from_ByteArray]

public
def NonExtensibleMessageFormat.fixedLengthByteArray
  (len: Nat)
  : NonExtensibleMessageFormat Bytes ({ b: ByteArray // b.size = len})
:=
  subsetIsomorphic (NonExtensibleMessageFormat.fixedLengthBytes len) (fixedLengthByteArray.f len) (fixedLengthByteArray.g len)
deriving IsNonAmbiguous, HasUniqueRepresentation

namespace NonExtensibleMessageFormat.fixedLengthByteArray

public
instance (len: Nat) [NeZero len] : ParseConsumes (fixedLengthByteArray len: NonExtensibleMessageFormat Bytes _) := by
  dsimp only [fixedLengthByteArray]
  infer_instance

@[simp]
public
theorem wf_eq
  (len: Nat)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: { b: ByteArray // b.size = len})
  : (fixedLengthByteArray len).wf pred x
:= by
  simp [fixedLengthByteArray, fixedLengthByteArray.g, BytesCompatiblePred.pred_fromByteArray]

end NonExtensibleMessageFormat.fixedLengthByteArray

def littleEndianToNat (l: List UInt8): Nat :=
  match l with
  | [] => 0
  | h::t =>
    h.toNat + 256*(littleEndianToNat t)

def natToLittleEndian (len: Nat) (n: Nat): List UInt8 :=
  if len = 0 then
    []
  else
    (UInt8.ofNat (n%256))::(natToLittleEndian (len-1) (n/256))

theorem uint8_toNat_le (x: UInt8): x.toNat < 256 := by
  rewrite [UInt8.toNat]
  rewrite [BitVec.toNat]
  grind

theorem natToLittleEndian_littleEndianToNat
  (l: List UInt8)
  : natToLittleEndian l.length (littleEndianToNat l) = l
:= by
  induction l
  · simp [natToLittleEndian, littleEndianToNat]
  rewrite [natToLittleEndian, littleEndianToNat]
  simp (disch := grind [uint8_toNat_le]) [Nat.add_mul_div_left, Nat.div_eq_of_lt]
  simp_all

theorem littleEndianToNat_natToLittleEndian
  (len: Nat) (n: Nat)
  : n < 256^len →
    littleEndianToNat (natToLittleEndian len n) = n
:= by
  fun_induction natToLittleEndian len n
  · grind [littleEndianToNat]
  rename_i ih
  simp (disch := grind) [Nat.div_lt_iff_lt_mul] at ih
  simp [*, littleEndianToNat]
  grind

theorem length_natToLittleEndian (len: Nat) (n: Nat) : (natToLittleEndian len n).length = len := by
  fun_induction natToLittleEndian len n <;> grind

theorem littleEndianToNat_le
  (l: List UInt8)
  : littleEndianToNat l < 256^l.length
:= by
  induction l
  · simp [littleEndianToNat]
  rename_i h t ih
  have := uint8_toNat_le h
  simp [littleEndianToNat, Nat.pow_add_one]
  grind

def NonExtensibleMessageFormat.bitVec.f
  {w: Nat}
  (b: {b: ByteArray // b.size = w})
  : BitVec (8*w)
:=
  BitVec.ofNat _ (littleEndianToNat b.val.data.toList)

def NonExtensibleMessageFormat.bitVec.g
  {w: Nat}
  (n: BitVec (8*w))
  : {b: ByteArray // b.size = w}
:=
  ⟨ ByteArray.mk (natToLittleEndian w n.toNat).toArray,  by simp [ByteArray.size, length_natToLittleEndian] ⟩

local instance (w: Nat): LeftInverse (NonExtensibleMessageFormat.bitVec.g (w := w)) (NonExtensibleMessageFormat.bitVec.f) where
  left_inv := by
    simp only [Function.LeftInverse, NonExtensibleMessageFormat.bitVec.f, NonExtensibleMessageFormat.bitVec.g]
    intro ⟨ ⟨ ⟨ x ⟩ ⟩, h_x ⟩
    simp
    have: 2^(8*w) = 256^w := by simp [Nat.pow_mul]
    have := littleEndianToNat_le x
    have: x.length = w := by simp_all [ByteArray.size]
    grind [Nat.mod_eq_of_lt, natToLittleEndian_littleEndianToNat]

local instance (w: Nat): RightInverse (NonExtensibleMessageFormat.bitVec.g (w := w)) (NonExtensibleMessageFormat.bitVec.f) where
  right_inv := by
    simp only [Function.LeftInverse, Function.RightInverse, NonExtensibleMessageFormat.bitVec.f, NonExtensibleMessageFormat.bitVec.g]
    intro x
    have: 2^(8*w) = 256^w := by simp [Nat.pow_mul]
    grind [littleEndianToNat_natToLittleEndian]

public
def NonExtensibleMessageFormat.bitVec (w: Nat): NonExtensibleMessageFormat Bytes (BitVec (8*w)) :=
  isomorphic (fixedLengthByteArray w) NonExtensibleMessageFormat.bitVec.f NonExtensibleMessageFormat.bitVec.g
deriving IsNonAmbiguous, HasUniqueRepresentation

namespace NonExtensibleMessageFormat.bitVec

public
instance (w: Nat) [NeZero w]: ParseConsumes (bitVec w: NonExtensibleMessageFormat Bytes _) := by
  dsimp only [bitVec]
  infer_instance

@[simp]
public
theorem wf_eq
  (w: Nat)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: BitVec (8*w))
  : (bitVec w).wf pred x
:= by
  simp [bitVec]

end NonExtensibleMessageFormat.bitVec

local instance: @LeftInverse UInt8 (BitVec (8*1)) UInt8.toBitVec UInt8.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt8 (BitVec (8*1)) UInt8.toBitVec UInt8.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

public
def NonExtensibleMessageFormat.uint8: NonExtensibleMessageFormat Bytes UInt8 :=
  isomorphic (bitVec 1) UInt8.ofBitVec UInt8.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint8.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: UInt8)
  : uint8.wf pred x
:= by
  simp only [uint8]
  apply NonExtensibleMessageFormat.bitVec.wf_eq

local instance: @LeftInverse UInt16 (BitVec (8*2)) UInt16.toBitVec UInt16.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt16 (BitVec (8*2)) UInt16.toBitVec UInt16.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

public
def NonExtensibleMessageFormat.uint16: NonExtensibleMessageFormat Bytes UInt16 :=
  isomorphic (bitVec 2) UInt16.ofBitVec UInt16.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint16.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: UInt16)
  : uint16.wf pred x
:= by
  simp only [uint16]
  apply NonExtensibleMessageFormat.bitVec.wf_eq

local instance: @LeftInverse UInt32 (BitVec (8*4)) UInt32.toBitVec UInt32.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt32 (BitVec (8*4)) UInt32.toBitVec UInt32.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

public
def NonExtensibleMessageFormat.uint32: NonExtensibleMessageFormat Bytes UInt32 :=
  isomorphic (bitVec 4) UInt32.ofBitVec UInt32.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint32.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: UInt32)
  : uint32.wf pred x
:= by
  simp only [uint32]
  apply NonExtensibleMessageFormat.bitVec.wf_eq

local instance: @LeftInverse UInt64 (BitVec (8*8)) UInt64.toBitVec UInt64.ofBitVec where
  left_inv := by simp [Function.LeftInverse]

local instance: @RightInverse UInt64 (BitVec (8*8)) UInt64.toBitVec UInt64.ofBitVec where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

public
def NonExtensibleMessageFormat.uint64: NonExtensibleMessageFormat Bytes UInt64 :=
  isomorphic (bitVec 8) UInt64.ofBitVec UInt64.toBitVec
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.uint64.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: UInt64)
  : uint64.wf pred x
:= by
  simp only [uint64]
  apply NonExtensibleMessageFormat.bitVec.wf_eq

def NonExtensibleMessageFormat.fin8.f (n: Nat) (_: n ≤ 256) (x: { x: UInt8 // x.toNat < n }): Fin n :=
  Fin.mk x.val.toNat x.property

def NonExtensibleMessageFormat.fin8.g (n: Nat) (_: n ≤ 256) (x: Fin n): { x: UInt8 // x.toNat < n } :=
  ⟨ UInt8.ofNatLT x.val (by grind), by simp ⟩

local instance (n: Nat) (h: n ≤ 256): LeftInverse (NonExtensibleMessageFormat.fin8.g n h) (NonExtensibleMessageFormat.fin8.f n h) where
  left_inv := by simp [Function.LeftInverse, NonExtensibleMessageFormat.fin8.f, NonExtensibleMessageFormat.fin8.g]

local instance (n: Nat) (h: n ≤ 256): RightInverse (NonExtensibleMessageFormat.fin8.g n h) (NonExtensibleMessageFormat.fin8.f n h) where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.fin8.f, NonExtensibleMessageFormat.fin8.g]

public
def NonExtensibleMessageFormat.fin8 (n: Nat) (h: n ≤ 256): NonExtensibleMessageFormat Bytes (Fin n) :=
  isomorphic (subtype uint8 (fun x => x.toNat < n)) (fin8.f n h) (fin8.g n h)
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.fin8.wf_eq
  (n: Nat) (h: n ≤ 256)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Fin n)
  : (fin8 n h).wf pred x
:= by
  simp [fin8]

def NonExtensibleMessageFormat.bool.f (x: Fin 2): Bool :=
  if x.val = 1 then true else false

def NonExtensibleMessageFormat.bool.g (x: Bool): Fin 2 :=
  if x then 1 else 0

local instance: LeftInverse (NonExtensibleMessageFormat.bool.g) (NonExtensibleMessageFormat.bool.f) where
  left_inv := by simp [Function.LeftInverse, NonExtensibleMessageFormat.bool.f, NonExtensibleMessageFormat.bool.g]

local instance: RightInverse (NonExtensibleMessageFormat.bool.g) (NonExtensibleMessageFormat.bool.f) where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.bool.f, NonExtensibleMessageFormat.bool.g]

public
def NonExtensibleMessageFormat.bool: NonExtensibleMessageFormat Bytes Bool :=
  isomorphic (fin8 2 (by decide)) bool.f bool.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.bool.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Bool)
  : bool.wf pred x
:= by
  simp [bool]

def NonExtensibleMessageFormat.slowNat.f (l: ListUntil (false = ·)): Nat :=
  l.init.length

def NonExtensibleMessageFormat.slowNat.g (n: Nat): ListUntil (false = ·) :=
  {
    init := List.replicate n (⟨ true, by simp ⟩)
    last := ⟨ false, rfl ⟩
  }

local instance: LeftInverse (NonExtensibleMessageFormat.slowNat.g) (NonExtensibleMessageFormat.slowNat.f) where
  left_inv := by
    simp only [Function.LeftInverse, NonExtensibleMessageFormat.slowNat.f, NonExtensibleMessageFormat.slowNat.g]
    intro ⟨ init, last ⟩
    simp only [ListUntil.mk.injEq]
    constructor
    · ext
      grind
    · grind

local instance: RightInverse (NonExtensibleMessageFormat.slowNat.g) (NonExtensibleMessageFormat.slowNat.f) where
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.slowNat.f, NonExtensibleMessageFormat.slowNat.g]

-- Slow unary coding
public
def NonExtensibleMessageFormat.slowNat: NonExtensibleMessageFormat Bytes Nat :=
  isomorphic (listUntil bool (false = ·)) slowNat.f slowNat.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.slowNat.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Nat)
  : slowNat.wf pred x
:= by
  simp [slowNat]

def NonExtensibleMessageFormat.slowBytes.f (x: (len: Nat) × { b: Bytes // BytesLike.length b = len}): Bytes :=
  x.snd.val

def NonExtensibleMessageFormat.slowBytes.g (b: Bytes): (len: Nat) × { b: Bytes // BytesLike.length b = len} :=
  ⟨ BytesLike.length b, ⟨ b, rfl ⟩ ⟩

local instance: LeftInverse (NonExtensibleMessageFormat.slowBytes.g (Bytes := Bytes)) (NonExtensibleMessageFormat.slowBytes.f) where
  left_inv := by
    simp only [Function.LeftInverse, NonExtensibleMessageFormat.slowBytes.f, NonExtensibleMessageFormat.slowBytes.g]
    intro ⟨ a, ⟨ b, c ⟩ ⟩
    simp only [Sigma.mk.injEq]
    constructor
    · assumption
    congr 1 <;> grind

local instance: RightInverse (NonExtensibleMessageFormat.slowBytes.g (Bytes := Bytes)) (NonExtensibleMessageFormat.slowBytes.f) where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.slowBytes.f, NonExtensibleMessageFormat.slowBytes.g]

public
def NonExtensibleMessageFormat.slowBytes: NonExtensibleMessageFormat Bytes Bytes :=
  isomorphic (sigma slowNat fixedLengthBytes) slowBytes.f slowBytes.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.slowBytes.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Bytes)
  : slowBytes.wf pred x = pred x
:= by
  simp [slowBytes, slowBytes.g]

def NonExtensibleMessageFormat.slowString.f (x: (len: Nat) × {s: String // s.utf8ByteSize = len}): String :=
  x.snd.val

def NonExtensibleMessageFormat.slowString.g (s: String): (len: Nat) × {s: String // s.utf8ByteSize = len} :=
  ⟨ s.utf8ByteSize, ⟨ s, rfl ⟩ ⟩

local instance: LeftInverse (NonExtensibleMessageFormat.slowString.g) (NonExtensibleMessageFormat.slowString.f) where
  left_inv := by
    simp only [Function.LeftInverse, NonExtensibleMessageFormat.slowString.f, NonExtensibleMessageFormat.slowString.g]
    intro ⟨ a, ⟨ b, d ⟩ ⟩
    simp only [Sigma.mk.injEq]
    constructor
    · grind
    congr 1 <;> grind

local instance: RightInverse (NonExtensibleMessageFormat.slowString.g) (NonExtensibleMessageFormat.slowString.f) where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.slowString.f, NonExtensibleMessageFormat.slowString.g]

public
def NonExtensibleMessageFormat.slowString: NonExtensibleMessageFormat Bytes String :=
  isomorphic (sigma slowNat (fun len => (ExtensibleMessageFormat.subtype .string (fun s => s.utf8ByteSize = len)).toNonExtensible len (by
    simp [ExtensibleMessageFormat.subtype, ExtensibleMessageFormat.string, ExtensibleMessageFormat.subsetIsomorphic, ExtensibleMessageFormat.isomorphic, ExtensibleMessageFormat.subtype.g, ExtensibleMessageFormat.string.g, ExtensibleMessageFormat.byteArray, ExtensibleMessageFormat.bytes, BytesLike.fromByteArray_length]
  ))) slowString.f slowString.g
  deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.slowString.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: String)
  : slowString.wf pred x
:= by
  simp [slowString, slowString.g]

end Comparse
