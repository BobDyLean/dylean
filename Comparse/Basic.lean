module

namespace Comparse

public
class BytesLike (Bytes:Type) where
  length: Bytes → Nat

  empty: Bytes
  empty_length: length empty = 0

  recognizeEmpty: Bytes → Bool
  recognizeEmpty_correct:
    ∀ b:Bytes,
    recognizeEmpty b ↔ b = empty

  concat: Bytes → Bytes → Bytes
  concat_length:
    ∀ b1 b2:Bytes,
    length (concat b1 b2) = (length b1) + (length b2)

  split: Bytes → Nat → Option (Bytes × Bytes)
  split_length:
    ∀ b: Bytes, ∀ i: Nat,
    match split b i with
    | none => True
    | some (b1, b2) => length b1 = i ∧ i + length b2 = length b

  split_concat:
    ∀ b1 b2: Bytes,
    split (concat b1 b2) (length b1) = some (b1, b2)

  concat_split:
    ∀ b: Bytes, ∀ i: Nat,
    match split b i with
    | none => True
    | some (b1, b2) => concat b1 b2 = b

  toByteArray (b: Bytes): Option ByteArray
  fromByteArray (b: ByteArray): Bytes

  fromByteArray_length:
    ∀ b: ByteArray, length (fromByteArray b) = b.size

  to_from_ByteArray:
    ∀ b: ByteArray, toByteArray (fromByteArray b) = some b

  from_to_ByteArray:
    ∀ b: Bytes,
      match toByteArray b with
      | none => True
      | some res => fromByteArray res = b

public
structure NonExtensibleMessageFormat (Bytes: Type) [BytesLike Bytes] (a: Type) where
  parse: Bytes -> Option (a × Bytes)
  serialize: a -> List Bytes
  parse_wf:
    ∀ buf,
      match parse buf with
      | none => True
      | some (_, suffix) =>
        BytesLike.length suffix ≤ BytesLike.length buf

public
structure ExtensibleMessageFormat (Bytes: Type) [BytesLike Bytes] (a: Type) where
  parse: Bytes -> Option a
  serialize: a -> Bytes

variable {Bytes: Type} [BytesLike Bytes]

public
def concatPrefixes (prefixes: List Bytes) (suffix: Bytes) :=
  List.foldr BytesLike.concat suffix prefixes

public
class NonExtensibleMessageFormat.IsNonAmbiguous {a: Type} (mf: NonExtensibleMessageFormat Bytes a) where
  parse_serialize_inv (mf):
    ∀ x: a, ∀ suffix: Bytes,
    mf.parse (concatPrefixes (mf.serialize x) suffix) = some ⟨x, suffix⟩

public
class NonExtensibleMessageFormat.HasUniqueRepresentation {a: Type} (mf: NonExtensibleMessageFormat Bytes a) where
  serialize_parse_inv (mf):
    ∀ buf: Bytes,
    match mf.parse buf with
    | none => True
    | some ⟨x, suffix⟩ => buf = concatPrefixes (mf.serialize x) suffix

public
class NonExtensibleMessageFormat.ParseConsumes {a: Type} (mf: NonExtensibleMessageFormat Bytes a) where
  parse_consumes (mf):
    ∀ buf,
      match mf.parse buf with
      | none => True
      | some (_, suffix) =>
        BytesLike.length suffix < BytesLike.length buf

public
class ExtensibleMessageFormat.IsNonAmbiguous {a: Type} (mf: ExtensibleMessageFormat Bytes a) where
  parse_serialize_inv (mf):
    ∀ x: a,
    mf.parse (mf.serialize x) = some x

public
class ExtensibleMessageFormat.HasUniqueRepresentation {a: Type} (mf: ExtensibleMessageFormat Bytes a) where
  serialize_parse_inv (mf):
    ∀ buf: Bytes,
    match mf.parse buf with
    | none => True
    | some x => buf = mf.serialize x

public
class BytesCompatiblePred (pred: Bytes → Prop) where
  pred_empty: pred BytesLike.empty
  pred_concat: ∀ lhs rhs, pred lhs → pred rhs → pred (BytesLike.concat lhs rhs)
  pred_split: ∀ buf i, pred buf →
    match BytesLike.split buf i with
    | none => True
    | some (lhs, rhs) => pred lhs ∧ pred rhs
  pred_fromByteArray: ∀ b, pred (BytesLike.fromByteArray b)

public
def ExtensibleMessageFormat.wf
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop)
  (x: a)
  : Prop
:=
  pred (mf.serialize x)

public
def NonExtensibleMessageFormat.wf
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop)
  (x: a)
  : Prop
:=
  ∀ b, b ∈ mf.serialize x → pred b

public
theorem ExtensibleMessageFormat.wf_eq
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop)
  (x: a)
  : mf.wf pred x = pred (mf.serialize x)
:= by
  simp [ExtensibleMessageFormat.wf]

end Comparse
