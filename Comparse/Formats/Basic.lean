module

public import Comparse.Basic
import all Comparse.Basic

namespace Comparse

variable {Bytes: Type} [BytesLike Bytes]

@[simp, local grind =]
theorem concatPrefixes_concatPrefixes
  (l1 l2: List Bytes) (suffix: Bytes)
  : concatPrefixes (l1 ++ l2) suffix = concatPrefixes l1 (concatPrefixes l2 suffix)
:= by
  simp [concatPrefixes]

theorem BytesCompatiblePred.pred_concatPrefixes
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (prefixes: List Bytes) (suffix: Bytes)
  : pred (concatPrefixes prefixes suffix) = ((∀ x, x ∈ prefixes → pred x) ∧ (pred suffix))
:= by
  rewrite [eq_iff_iff]
  constructor
  · induction prefixes
    · simp [concatPrefixes]
    rename_i hPrefix tPrefix ih
    have := BytesLike.split_concat hPrefix (List.foldr BytesLike.concat suffix tPrefix)
    grind [concatPrefixes, BytesCompatiblePred.pred_split]
  · induction prefixes
    · simp [concatPrefixes]
    grind [concatPrefixes, BytesCompatiblePred.pred_concat]


public
def NonExtensibleMessageFormat.unit: NonExtensibleMessageFormat Bytes Unit where
  parse b := some ((), b)
  serialize _ := []
  parse_wf := by simp

namespace NonExtensibleMessageFormat.unit

public
instance: (unit: NonExtensibleMessageFormat Bytes Unit).IsNonAmbiguous
where
  parse_serialize_inv x suffix := by
    rfl

public
instance: (unit: NonExtensibleMessageFormat Bytes Unit).HasUniqueRepresentation
where
  serialize_parse_inv buf := by
    rfl

@[simp]
public
theorem wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Unit)
  : unit.wf pred x
:= by
  simp [wf, unit]

end NonExtensibleMessageFormat.unit

public
def ExtensibleMessageFormat.bytes: ExtensibleMessageFormat Bytes Bytes where
  parse b := some b
  serialize b := b

namespace ExtensibleMessageFormat.bytes

public
instance: (bytes: ExtensibleMessageFormat Bytes Bytes).IsNonAmbiguous
where
  parse_serialize_inv x := by
    rfl

public
instance: (bytes: ExtensibleMessageFormat Bytes Bytes).HasUniqueRepresentation
where
  serialize_parse_inv buf := by
    rfl

@[simp]
public
theorem wf_eq
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Bytes)
  : bytes.wf pred x = pred x
:= by
  simp [wf, bytes]

end ExtensibleMessageFormat.bytes

public
def NonExtensibleMessageFormat.toExtensible
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  : ExtensibleMessageFormat Bytes a
where
  parse buf :=
    match mf.parse buf with
    | none => none
    | some (x, rest) =>
      if BytesLike.recognizeEmpty rest then
        some x
      else
        none
  serialize x := concatPrefixes (mf.serialize x) BytesLike.empty

namespace NonExtensibleMessageFormat.toExtensible

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.IsNonAmbiguous]
  : mf.toExtensible.IsNonAmbiguous
where
  parse_serialize_inv x := by
    dsimp only [toExtensible]
    simp [IsNonAmbiguous.parse_serialize_inv, BytesLike.recognizeEmpty_correct]

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.HasUniqueRepresentation]
  : mf.toExtensible.HasUniqueRepresentation
where
  serialize_parse_inv buf := by
    dsimp only [toExtensible]
    split
    · trivial
    rename_i x heq
    split at heq
    · contradiction
    have := HasUniqueRepresentation.serialize_parse_inv mf buf
    simp_all [BytesLike.recognizeEmpty_correct]

@[simp]
public
theorem wf_eq
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: a)
  : mf.toExtensible.wf pred x = mf.wf pred x
:= by
  simp [NonExtensibleMessageFormat.wf, ExtensibleMessageFormat.wf, toExtensible, BytesCompatiblePred.pred_concatPrefixes, BytesCompatiblePred.pred_empty]

end NonExtensibleMessageFormat.toExtensible

public
def ExtensibleMessageFormat.toNonExtensible
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (len: Nat)
  (_: ∀ x, BytesLike.length (mf.serialize x) = len) -- technically only needed of typeclasses
  : NonExtensibleMessageFormat Bytes a
where
  parse buf :=
    match BytesLike.split buf len with
    | none => none
    | some (bufPrefix, suffix) =>
      match mf.parse bufPrefix with
      | none => none
      | some x => some (x, suffix)

  serialize x := [mf.serialize x]

  parse_wf := by grind [BytesLike.split_length]

namespace ExtensibleMessageFormat.toNonExtensible

public
instance
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (len: Nat)
  (h: ∀ x, BytesLike.length (mf.serialize x) = len)
  [mf.IsNonAmbiguous]
  : (mf.toNonExtensible len h).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro x suffix
    dsimp only [toNonExtensible]
    dsimp only [concatPrefixes, List.foldr_cons, List.foldr_nil]
    rewrite [← h x]
    simp [BytesLike.split_concat, IsNonAmbiguous.parse_serialize_inv mf x]

public
instance
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (len: Nat)
  (h: ∀ x, BytesLike.length (mf.serialize x) = len)
  [mf.HasUniqueRepresentation]
  : (mf.toNonExtensible len h).HasUniqueRepresentation
where
  serialize_parse_inv := by
    intro buf
    dsimp only [toNonExtensible]
    dsimp only [concatPrefixes, List.foldr_cons, List.foldr_nil]
    split
    · trivial
    rename_i x suffix heq
    split at heq
    · contradiction
    rename_i bufPrefix suffix' heq'
    split at heq
    · contradiction
    rename_i  x' heq''
    have := BytesLike.concat_split buf len
    have := HasUniqueRepresentation.serialize_parse_inv mf bufPrefix
    grind

public
instance
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (len: Nat)
  (h: ∀ x, BytesLike.length (mf.serialize x) = len)
  [NeZero len]
  : (mf.toNonExtensible len h).ParseConsumes
where
  parse_consumes x := by
    dsimp only [toNonExtensible]
    have := BytesLike.split_length x len
    grind [NeZero]

@[simp]
public
theorem wf_eq
  {a: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (len: Nat)
  (h: ∀ x, BytesLike.length (mf.serialize x) = len)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: a)
  : (mf.toNonExtensible len h).wf pred x = mf.wf pred x
:= by
  simp [NonExtensibleMessageFormat.wf, ExtensibleMessageFormat.wf, toNonExtensible]

end ExtensibleMessageFormat.toNonExtensible

public
def NonExtensibleMessageFormat.sigma
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → NonExtensibleMessageFormat Bytes (b x))
  : NonExtensibleMessageFormat Bytes (Sigma b)
where
  parse buf :=
    match mfa.parse buf with
    | none => none
    | some ⟨xa, bufSuffix⟩ => (
      match (mfb xa).parse bufSuffix with
      | none => none
      | some ⟨xb, bufSuffixSuffix⟩ => (
        some ⟨⟨xa, xb⟩, bufSuffixSuffix⟩
      )
    )
  serialize := λ ⟨xa, xb⟩ =>
    (mfa.serialize xa) ++ ((mfb xa).serialize xb)

  parse_wf := by
    have := mfa.parse_wf
    have := fun x => (mfb x).parse_wf
    grind

namespace NonExtensibleMessageFormat.sigma

public
instance
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → NonExtensibleMessageFormat Bytes (b x))
  [mfa.IsNonAmbiguous]
  [∀ x, (mfb x).IsNonAmbiguous]
  : (sigma mfa mfb).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro ⟨ xa, xb ⟩ suffix
    dsimp only [sigma]
    have := IsNonAmbiguous.parse_serialize_inv mfa xa
    have := IsNonAmbiguous.parse_serialize_inv (mfb xa) xb
    simp_all

public
instance
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → NonExtensibleMessageFormat Bytes (b x))
  [mfa.HasUniqueRepresentation]
  [∀ x, (mfb x).HasUniqueRepresentation]
  : (sigma mfa mfb).HasUniqueRepresentation
where
  serialize_parse_inv buf := by
    dsimp only [sigma]
    split
    · trivial
    rename_i x bufSuffixSuffix heq
    obtain ⟨xa,xb⟩ := x
    split at heq
    · contradiction
    rename_i xa' bufSuffix' heq'
    split at heq
    · contradiction
    rename_i xb' bufSuffixSuffix' heq''
    have := HasUniqueRepresentation.serialize_parse_inv mfa buf
    have := HasUniqueRepresentation.serialize_parse_inv (mfb xa) bufSuffix'
    grind

public
instance
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → NonExtensibleMessageFormat Bytes (b x))
  [mfa.ParseConsumes]
  : (sigma mfa mfb).ParseConsumes
where
  parse_consumes x := by
    dsimp only [sigma]
    have := ParseConsumes.parse_consumes mfa
    have := fun x => (mfb x).parse_wf
    grind

public
instance
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → NonExtensibleMessageFormat Bytes (b x))
  [∀ x, (mfb x).ParseConsumes]
  : (sigma mfa mfb).ParseConsumes
where
  parse_consumes x := by
    dsimp only [sigma]
    have := mfa.parse_wf
    have := fun x => ParseConsumes.parse_consumes (mfb x)
    grind

@[simp]
public
theorem wf_eq
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → NonExtensibleMessageFormat Bytes (b x))
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Sigma b)
  : (sigma mfa mfb).wf pred x = ((mfa.wf pred x.fst) ∧ ((mfb x.fst).wf pred x.snd))
:= by
  simp [wf, sigma]
  grind

end NonExtensibleMessageFormat.sigma

public
def ExtensibleMessageFormat.sigma
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → ExtensibleMessageFormat Bytes (b x))
  : ExtensibleMessageFormat Bytes (Sigma b)
where
  parse buf :=
    match mfa.parse buf with
    | none => none
    | some ⟨xa, bufSuffix⟩ => (
      match (mfb xa).parse bufSuffix with
      | none => none
      | some xb => (
        some ⟨xa, xb⟩
      )
    )
  serialize := λ ⟨xa, xb⟩ =>
    concatPrefixes (mfa.serialize xa) ((mfb xa).serialize xb)

namespace ExtensibleMessageFormat.sigma

public
instance
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → ExtensibleMessageFormat Bytes (b x))
  [mfa.IsNonAmbiguous]
  [∀ x, (mfb x).IsNonAmbiguous]
  : (sigma mfa mfb).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro ⟨ xa, xb ⟩
    dsimp only [sigma]
    have := NonExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv mfa xa
    have := IsNonAmbiguous.parse_serialize_inv (mfb xa) xb
    simp_all

public
instance
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → ExtensibleMessageFormat Bytes (b x))
  [mfa.HasUniqueRepresentation]
  [∀ x, (mfb x).HasUniqueRepresentation]
  : (sigma mfa mfb).HasUniqueRepresentation
where
  serialize_parse_inv buf := by
    dsimp only [sigma]
    split
    · trivial
    rename_i x heq
    obtain ⟨xa,xb⟩ := x
    split at heq
    · contradiction
    rename_i xa' bufSuffix' heq'
    split at heq
    · contradiction
    rename_i xb' heq''
    have := NonExtensibleMessageFormat.HasUniqueRepresentation.serialize_parse_inv mfa buf
    have := HasUniqueRepresentation.serialize_parse_inv (mfb xa) bufSuffix'
    grind

@[simp]
public
theorem wf_eq
  {a: Type} {b: a → Type}
  (mfa: NonExtensibleMessageFormat Bytes a)
  (mfb: (x: a) → ExtensibleMessageFormat Bytes (b x))
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Sigma b)
  : (sigma mfa mfb).wf pred x = ((mfa.wf pred x.fst) ∧ ((mfb x.fst).wf pred x.snd))
:= by
  simp [NonExtensibleMessageFormat.wf, ExtensibleMessageFormat.wf, sigma, BytesCompatiblePred.pred_concatPrefixes]

end ExtensibleMessageFormat.sigma

public
class SubsetRightInverse (g: b → a) (f: a → Option b) where
  right_inv (g f): ∀ x, f (g x) = some x

public
class SubsetLeftInverse (g: b → a) (f: a → Option b) where
  left_inv (g f):
    ∀ x,
      match f x with
      | none => True
      | some y => g y = x

public
def NonExtensibleMessageFormat.subsetIsomorphic
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  : NonExtensibleMessageFormat Bytes b
where
  parse buf :=
    match mf.parse buf with
    | none => none
    | some (x, suffix) =>
      match f x with
      | none => none
      | some y => some (y, suffix)
  serialize x :=
    mf.serialize (g x)
  parse_wf := by have := mf.parse_wf; grind

namespace NonExtensibleMessageFormat.subsetIsomorphic

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  [mf.IsNonAmbiguous]
  [SubsetRightInverse g f]
  : (subsetIsomorphic mf f g).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro x suffix
    dsimp only [subsetIsomorphic]
    have := IsNonAmbiguous.parse_serialize_inv mf (g x)
    have := SubsetRightInverse.right_inv g f
    grind

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  [mf.HasUniqueRepresentation]
  [SubsetLeftInverse g f]
  : (subsetIsomorphic mf f g).HasUniqueRepresentation
where
  serialize_parse_inv := by
    intro buf
    dsimp only [subsetIsomorphic]
    have := HasUniqueRepresentation.serialize_parse_inv mf buf
    have := SubsetLeftInverse.left_inv g f
    grind

public
instance
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  [mf.ParseConsumes]
  : (subsetIsomorphic mf f g).ParseConsumes
where
  parse_consumes buf := by
    dsimp only [subsetIsomorphic]
    have := ParseConsumes.parse_consumes mf
    grind

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: b)
  : (subsetIsomorphic mf f g).wf pred x = mf.wf pred (g x)
:= by
  simp [wf, subsetIsomorphic]

end NonExtensibleMessageFormat.subsetIsomorphic

public
def ExtensibleMessageFormat.subsetIsomorphic
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  : ExtensibleMessageFormat Bytes b
where
  parse buf :=
    match mf.parse buf with
    | none => none
    | some x => f x
  serialize x :=
    mf.serialize (g x)

namespace ExtensibleMessageFormat.subsetIsomorphic

public
instance
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  [mf.IsNonAmbiguous]
  [SubsetRightInverse g f]
  : (subsetIsomorphic mf f g).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro x
    dsimp only [subsetIsomorphic]
    have := IsNonAmbiguous.parse_serialize_inv mf (g x)
    have := SubsetRightInverse.right_inv g f
    grind

public
instance
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  [mf.HasUniqueRepresentation]
  [SubsetLeftInverse g f]
  : (subsetIsomorphic mf f g).HasUniqueRepresentation
where
  serialize_parse_inv := by
    intro buf
    dsimp only [subsetIsomorphic]
    have := HasUniqueRepresentation.serialize_parse_inv mf buf
    have := SubsetLeftInverse.left_inv g f
    grind

@[simp]
public
theorem wf_eq
  {a b: Type}
  (mf: ExtensibleMessageFormat Bytes a)
  (f: a → Option b) (g: b → a)
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: b)
  : (subsetIsomorphic mf f g).wf pred x = mf.wf pred (g x)
:= by
  simp [wf, subsetIsomorphic]

end ExtensibleMessageFormat.subsetIsomorphic

public
def ExtensibleMessageFormat.list.parse
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  (buf: Bytes)
  : Option (List a)
:=
  if BytesLike.recognizeEmpty buf then
    some []
  else
    match _: mf.parse buf with
    | none => none
    | some (h, suffix) =>
      match parse mf suffix with
      | none => none
      | some t => some (h::t)
termination_by BytesLike.length buf
decreasing_by
  have := NonExtensibleMessageFormat.ParseConsumes.parse_consumes mf buf
  grind

public
def ExtensibleMessageFormat.list.serialize
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (l: List a)
  : Bytes
:=
  match l with
  | [] => BytesLike.empty
  | h::t => concatPrefixes (mf.serialize h) (serialize mf t)

public
def ExtensibleMessageFormat.list
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  : ExtensibleMessageFormat Bytes (List a)
:=
  { parse := list.parse mf, serialize := list.serialize mf }

namespace ExtensibleMessageFormat.list

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  [mf.IsNonAmbiguous]
  : (list mf).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro l
    dsimp only [list]
    induction l
    · dsimp only [list.serialize]; rewrite [list.parse]
      simp [BytesLike.recognizeEmpty_correct]
    · rename_i h t _
      dsimp only [list.serialize]; rewrite [list.parse]
      split
      · exfalso
        have := NonExtensibleMessageFormat.ParseConsumes.parse_consumes mf (concatPrefixes (mf.serialize h) (serialize mf t))
        have := NonExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv mf h (serialize mf t)
        have := BytesLike.recognizeEmpty_correct (concatPrefixes (mf.serialize h) (serialize mf t))
        have := BytesLike.empty_length (Bytes := Bytes)
        grind
      have := NonExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv mf h (serialize mf t)
      grind

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  [mf.HasUniqueRepresentation]
  : (list mf).HasUniqueRepresentation
where
  serialize_parse_inv := by
    intro buf
    dsimp only [list]
    fun_induction parse mf buf <;> dsimp only [list.serialize]
    · grind [BytesLike.recognizeEmpty_correct]
    · have := NonExtensibleMessageFormat.HasUniqueRepresentation.serialize_parse_inv mf
      grind

@[simp]
public
theorem wf_eq
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (l: List a)
  : (list mf).wf pred l = (∀ x, x ∈ l → mf.wf pred x)
:= by
  simp only [wf, list]
  induction l
  · simp [list.serialize, BytesCompatiblePred.pred_empty]
  simp_all [list.serialize, BytesCompatiblePred.pred_concatPrefixes]
  grind [NonExtensibleMessageFormat.wf]

end ExtensibleMessageFormat.list

public
structure ListUntil {a: Type} (p: a → Prop) [DecidablePred p] where
  init: List {x: a // ¬ p x}
  last: {x: a // p x}

public
def NonExtensibleMessageFormat.listUntil.parse
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  (p: a → Prop) [DecidablePred p]
  (buf: Bytes)
  : Option (ListUntil p × Bytes)
:=
  match _: mf.parse buf with
  | none => none
  | some (h, suffix) =>
    if h_h: p h then
      some ({init := [], last := ⟨ h, h_h ⟩}, suffix)
    else
      match parse mf p suffix with
      | none => none
      | some ({ init, last }, suffixSuffix) =>
        some ({ init := (⟨ h, h_h ⟩)::init, last}, suffixSuffix)
termination_by BytesLike.length buf
decreasing_by
  have := NonExtensibleMessageFormat.ParseConsumes.parse_consumes mf buf
  grind

public
def NonExtensibleMessageFormat.listUntil.serialize
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  (p: a → Prop) [DecidablePred p]
  (l: ListUntil p)
  : List Bytes
:=
  l.init
    |>.map Subtype.val
    |>.map mf.serialize
    |>.foldr (· ++ ·) (mf.serialize l.last.val)

public
def NonExtensibleMessageFormat.listUntil
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  (p: a → Prop) [DecidablePred p]
  : NonExtensibleMessageFormat Bytes (ListUntil p)
where
  parse := listUntil.parse mf p
  serialize := listUntil.serialize mf p
  parse_wf buf := by
    fun_induction listUntil.parse mf p buf
    all_goals
      have := NonExtensibleMessageFormat.ParseConsumes.parse_consumes mf
      grind

namespace NonExtensibleMessageFormat.listUntil

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.IsNonAmbiguous] [mf.ParseConsumes]
  : (listUntil mf p).IsNonAmbiguous
where
  parse_serialize_inv := by
    intro ⟨ init, last ⟩ suffix
    dsimp only [listUntil]
    induction init
    · simp only [serialize, List.map_nil, List.foldr_nil]; rewrite [parse]
      have := IsNonAmbiguous.parse_serialize_inv mf
      grind
    rename_i hInit tInit ih
    have := IsNonAmbiguous.parse_serialize_inv mf
    simp [serialize]; rewrite [parse]
    simp [serialize] at ih
    grind

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.HasUniqueRepresentation] [mf.ParseConsumes]
  : (listUntil mf p).HasUniqueRepresentation
where
  serialize_parse_inv := by
    intro buf
    dsimp only [listUntil]
    fun_induction parse mf p buf
    all_goals
      have := HasUniqueRepresentation.serialize_parse_inv mf
      grind [serialize]

public
instance
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  (p: a → Prop) [DecidablePred p]
  [mf.ParseConsumes]
  : (listUntil mf p).ParseConsumes
where
  parse_consumes buf := by
    dsimp only [listUntil]
    fun_induction listUntil.parse mf p buf
    all_goals
      have := NonExtensibleMessageFormat.ParseConsumes.parse_consumes mf
      grind

@[simp]
public
theorem wf_eq
  {a: Type}
  (mf: NonExtensibleMessageFormat Bytes a)
  [mf.ParseConsumes]
  (p: a → Prop) [DecidablePred p]
  (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (l: ListUntil p)
  : (listUntil mf p).wf pred l = ((∀ x, x ∈ l.init → mf.wf pred x.val) ∧ (mf.wf pred l.last.val))
:= by
  simp only [wf, listUntil]
  obtain ⟨ init, last ⟩ := l
  induction init
  · simp [listUntil.serialize]
  simp_all [listUntil.serialize]
  grind

end NonExtensibleMessageFormat.listUntil

end Comparse
