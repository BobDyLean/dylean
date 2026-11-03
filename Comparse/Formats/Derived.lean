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
    grind [f, g]
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
    grind [f, g]
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
    simp only [ExtensibleMessageFormat.subtype, ExtensibleMessageFormat.subsetIsomorphic, ExtensibleMessageFormat.bytes, ExtensibleMessageFormat.subtype.g]
    grind
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

def NonExtensibleMessageFormat.unboundedNat.encodingWf (l: ListUntil (UInt32.toNat · < 2^31)): Prop :=
  match l.init with
  | [] => True
  | h::_ => h.val.toNat ≠ 2^31

instance : DecidablePred NonExtensibleMessageFormat.unboundedNat.encodingWf :=
  fun l => by
    unfold NonExtensibleMessageFormat.unboundedNat.encodingWf
    split <;> infer_instance

def NonExtensibleMessageFormat.unboundedNat.f (l: Subtype encodingWf): Nat :=
  (l.val.init.foldl (fun acc n => acc*(2^31) + (n.val.toNat - 2^31)) 0)*(2^31) + l.val.last.val.toNat

def NonExtensibleMessageFormat.unboundedNat.g_aux (acc: List {x: UInt32 // ¬ (UInt32.toNat x < 2^31)}) (n: Nat): List {x: UInt32 // ¬ (UInt32.toNat x < 2^31)} :=
  if n = 0 then acc
  else
    g_aux (⟨ UInt32.ofNat (n%(2^31) + 2^31), by grind ⟩::acc) (n / 2^31)
decreasing_by grind

theorem NonExtensibleMessageFormat.unboundedNat.g_aux_wf
  (acc: List {x: UInt32 // ¬ (UInt32.toNat x < 2^31)}) (n: Nat)
  : (n = 0 → match acc with | [] => True | h::_ => h.val.toNat ≠ 2^31) →
    match g_aux acc n with | [] => True | h::_ => h.val.toNat ≠ 2^31
:= by
  fun_induction g_aux <;> grind

def NonExtensibleMessageFormat.unboundedNat.g (n: Nat): Subtype encodingWf :=
  ⟨
    {
      init := NonExtensibleMessageFormat.unboundedNat.g_aux [] (n / (2^31))
      last := ⟨ UInt32.ofNat (n % 2^31), by grind ⟩
    }
  ,
    by grind [encodingWf, g_aux_wf]
  ⟩

theorem NonExtensibleMessageFormat.unboundedNat.g_aux_append (acc: List {x: UInt32 // ¬ (UInt32.toNat x < 2^31)}) (n: Nat)
  : g_aux acc n = g_aux [] n ++ acc
:= by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rewrite [g_aux.eq_def acc, g_aux.eq_def []]
    split
    · simp
    · rewrite [ih _ (by grind) (_ :: acc), ih _ (by grind) [_]]
      simp

theorem NonExtensibleMessageFormat.unboundedNat.foldl_g_aux (n: Nat)
  : (g_aux [] n).foldl (fun acc n => acc*(2^31) + (n.val.toNat - 2^31)) 0 = n
:= by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rewrite [g_aux.eq_def]
    split
    · grind
    · rewrite [g_aux_append, List.foldl_append]
      grind

theorem NonExtensibleMessageFormat.unboundedNat.g_aux_step (acc: List {x: UInt32 // ¬ (UInt32.toNat x < 2^31)}) (m: Nat) (x: {x: UInt32 // ¬ (UInt32.toNat x < 2^31)})
  (h: m*(2^31) + (x.val.toNat - 2^31) ≠ 0)
  : g_aux acc (m*(2^31) + (x.val.toNat - 2^31)) = g_aux (x::acc) m
:= by
  have hx := x.property
  have hx' := x.val.toNat_lt
  rw [g_aux.eq_def, ite_eq_right h]
  have hd : (⟨UInt32.ofNat ((m*(2^31) + (x.val.toNat - 2^31)) % 2^31 + 2^31), by grind⟩ : {x: UInt32 // ¬ (UInt32.toNat x < 2^31)}) = x := by
    ext
    grind
  have hm : (m*(2^31) + (x.val.toNat - 2^31)) / 2^31 = m := by omega
  rewrite [hm, hd]
  rfl

theorem NonExtensibleMessageFormat.unboundedNat.g_aux_foldl (l acc: List {x: UInt32 // ¬ (UInt32.toNat x < 2^31)}) (a: Nat)
  (h_wf: a ≠ 0 ∨ ∀ h ∈ l.head?, h.val.toNat ≠ 2^31)
  : g_aux acc (l.foldl (fun acc n => acc*(2^31) + (n.val.toNat - 2^31)) a) = g_aux (l ++ acc) a
:= by
  induction l generalizing a acc with
  | nil => grind
  | cons x l ih =>
    have h_ne : a*(2^31) + (x.val.toNat - 2^31) ≠ 0 := by
      rcases h_wf with h_wf | h_wf
      · grind
      · have := h_wf x rfl
        grind
    rewrite [List.foldl_cons, ih _ _ (Or.inl h_ne), g_aux_step _ _ _ h_ne]
    rfl

theorem NonExtensibleMessageFormat.unboundedNat.left_inv: Function.LeftInverse NonExtensibleMessageFormat.unboundedNat.g NonExtensibleMessageFormat.unboundedNat.f := by
  intro ⟨⟨init, last⟩, hwf⟩
  ext
  have hl := last.property
  have hl' : last.val.toNat < 2^31 := hl
  show ListUntil.mk (g_aux [] ((init.foldl (fun acc n => acc*(2^31) + (n.val.toNat - 2^31)) 0 * 2^31 + last.val.toNat) / 2^31)) _ = ⟨init, last⟩
  congr 1
  · rewrite [show (init.foldl (fun acc n => acc*(2^31) + (n.val.toNat - 2^31)) 0 * 2^31 + last.val.toNat) / 2^31 = init.foldl (fun acc n => acc*(2^31) + (n.val.toNat - 2^31)) 0 by grind]
    rewrite [g_aux_foldl _ _ _ (Or.inr _), List.append_nil]
    · rewrite [g_aux.eq_def, ite_eq_left rfl]; grind
    · intro h hh
      unfold encodingWf at hwf
      cases init with
      | nil => cases hh
      | cons y _ => cases hh; grind
  · ext
    grind [f]

local instance: LeftInverse (NonExtensibleMessageFormat.unboundedNat.g) (NonExtensibleMessageFormat.unboundedNat.f) where
  left_inv := NonExtensibleMessageFormat.unboundedNat.left_inv

theorem NonExtensibleMessageFormat.unboundedNat.right_inv: Function.RightInverse NonExtensibleMessageFormat.unboundedNat.g NonExtensibleMessageFormat.unboundedNat.f := by
  grind [f, g, foldl_g_aux]

local instance: RightInverse (NonExtensibleMessageFormat.unboundedNat.g) (NonExtensibleMessageFormat.unboundedNat.f) where
  right_inv := NonExtensibleMessageFormat.unboundedNat.right_inv

-- unbounded unary coding
public
def NonExtensibleMessageFormat.unboundedNat: NonExtensibleMessageFormat Bytes Nat :=
  isomorphic (subtype (listUntil uint32 (UInt32.toNat · < 2^31)) unboundedNat.encodingWf) unboundedNat.f unboundedNat.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.unboundedNat.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Nat)
  : unboundedNat.wf pred x
:= by
  simp [unboundedNat]

def NonExtensibleMessageFormat.unboundedBytes.f (x: (len: Nat) × { b: Bytes // BytesLike.length b = len}): Bytes :=
  x.snd.val

def NonExtensibleMessageFormat.unboundedBytes.g (b: Bytes): (len: Nat) × { b: Bytes // BytesLike.length b = len} :=
  ⟨ BytesLike.length b, ⟨ b, rfl ⟩ ⟩

local instance: LeftInverse (NonExtensibleMessageFormat.unboundedBytes.g (Bytes := Bytes)) (NonExtensibleMessageFormat.unboundedBytes.f) where
  left_inv := by
    simp only [Function.LeftInverse, NonExtensibleMessageFormat.unboundedBytes.f, NonExtensibleMessageFormat.unboundedBytes.g]
    intro ⟨ a, ⟨ b, c ⟩ ⟩
    simp only [Sigma.mk.injEq]
    constructor
    · assumption
    congr 1 <;> grind

local instance: RightInverse (NonExtensibleMessageFormat.unboundedBytes.g (Bytes := Bytes)) (NonExtensibleMessageFormat.unboundedBytes.f) where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.unboundedBytes.f, NonExtensibleMessageFormat.unboundedBytes.g]

public
def NonExtensibleMessageFormat.unboundedBytes: NonExtensibleMessageFormat Bytes Bytes :=
  isomorphic (sigma unboundedNat fixedLengthBytes) unboundedBytes.f unboundedBytes.g
deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.unboundedBytes.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Bytes)
  : unboundedBytes.wf pred x = pred x
:= by
  simp [unboundedBytes, unboundedBytes.g]

def NonExtensibleMessageFormat.unboundedString.f (x: (len: Nat) × {s: String // s.utf8ByteSize = len}): String :=
  x.snd.val

def NonExtensibleMessageFormat.unboundedString.g (s: String): (len: Nat) × {s: String // s.utf8ByteSize = len} :=
  ⟨ s.utf8ByteSize, ⟨ s, rfl ⟩ ⟩

local instance: LeftInverse (NonExtensibleMessageFormat.unboundedString.g) (NonExtensibleMessageFormat.unboundedString.f) where
  left_inv := by
    simp only [Function.LeftInverse, NonExtensibleMessageFormat.unboundedString.f, NonExtensibleMessageFormat.unboundedString.g]
    intro ⟨ a, ⟨ b, d ⟩ ⟩
    simp only [Sigma.mk.injEq]
    constructor
    · grind
    congr 1 <;> grind

local instance: RightInverse (NonExtensibleMessageFormat.unboundedString.g) (NonExtensibleMessageFormat.unboundedString.f) where
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, NonExtensibleMessageFormat.unboundedString.f, NonExtensibleMessageFormat.unboundedString.g]

public
def NonExtensibleMessageFormat.unboundedString: NonExtensibleMessageFormat Bytes String :=
  isomorphic (sigma unboundedNat (fun len => (ExtensibleMessageFormat.subtype .string (fun s => s.utf8ByteSize = len)).toNonExtensible len (by
    simp [ExtensibleMessageFormat.subtype, ExtensibleMessageFormat.string, ExtensibleMessageFormat.subsetIsomorphic, ExtensibleMessageFormat.isomorphic, ExtensibleMessageFormat.subtype.g, ExtensibleMessageFormat.string.g, ExtensibleMessageFormat.byteArray, ExtensibleMessageFormat.bytes, BytesLike.fromByteArray_length]
  ))) unboundedString.f unboundedString.g
  deriving IsNonAmbiguous, HasUniqueRepresentation, ParseConsumes

@[simp]
public
theorem NonExtensibleMessageFormat.unboundedString.wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: String)
  : unboundedString.wf pred x
:= by
  simp [unboundedString, unboundedString.g]

end Comparse
