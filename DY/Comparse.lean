module

public import Comparse
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat

namespace DY.Comparse

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

public
instance: Comparse.BytesLike Bytes where
  length := Bytes.length

  empty := Literal.literalToBytes .empty
  empty_length := by simp

  recognizeEmpty b := b = Literal.literalToBytes .empty
  recognizeEmpty_correct b := by simp

  concat := Concat.concat
  concat_length := by simp

  split := Concat.split
  split_length := by grind [Concat.length_split]

  split_concat := Concat.split_concat

  concat_split buf i := by grind [Concat.concat_split]

  toByteArray := Literal.bytesToLiteral
  fromByteArray := Literal.literalToBytes

  fromByteArray_length := by simp

  to_from_ByteArray := Literal.bytesToLiteral_literalToBytes

  from_to_ByteArray := by grind [Literal.literalToBytes_bytesToLiteral]

public
class ParseableSerializeable (a: Type) where
  mf: Comparse.ExtensibleMessageFormat Bytes a
  [mf_na: mf.IsNonAmbiguous]
  [mf_ur: mf.HasUniqueRepresentation]

attribute [instance] ParseableSerializeable.mf_na
attribute [instance] ParseableSerializeable.mf_ur

public
def parse {a: Type} [ParseableSerializeable a] (buf: Bytes): Err a :=
  ParseableSerializeable.mf.parse buf

public
def serialize {a: Type} [ParseableSerializeable a] (x: a): Bytes :=
  ParseableSerializeable.mf.serialize x

@[simp]
public
theorem parse_serialize_inv
  {a: Type} [ParseableSerializeable a]
  (x: a)
  : parse (serialize x) = some x
:= by
  simp [parse, serialize, Comparse.ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv]

-- TODO: do we need this grind pattern, or is the injectivity one below enough?
grind_pattern parse_serialize_inv => serialize x

@[grind inj]
public
theorem serialize_injective
  {a: Type} [ParseableSerializeable a]
  : Function.Injective (serialize: a → Bytes)
:= by
  simp only [Function.Injective]
  grind

theorem serialize_parse_inv
  {a: Type} [ParseableSerializeable a]
  (buf: Bytes) (x: a)
  : parse buf = some x →
    buf = serialize x
:= by
  simp only [parse, serialize]
  grind [Comparse.ExtensibleMessageFormat.HasUniqueRepresentation.serialize_parse_inv]

@[implicit_reducible]
public
def ParseableSerializeable.make
  {a: Type}
  (mf: Comparse.ExtensibleMessageFormat Bytes a)
  [mf.IsNonAmbiguous]
  [mf.HasUniqueRepresentation]
  : ParseableSerializeable a
where
  mf := mf

@[implicit_reducible]
public
def ParseableSerializeable.makeNE
  {a: Type}
  (mf: Comparse.NonExtensibleMessageFormat Bytes a)
  [mf.IsNonAmbiguous]
  [mf.HasUniqueRepresentation]
  : ParseableSerializeable a
:=
  .make (mf.toExtensible)

-- TODO: FormatRel
public
def formatRel [ParseableSerializeable a] (buf: Bytes) (x: a): Prop :=
  buf = serialize x

public
instance [TraceInvariant] [ParseableSerializeable a]:
  HoareTriple
    (parse buf: Err a)
    (fun _ => True)
    (fun res _ => formatRel buf res)
where
  pf := by
    simp only [hoareTriple, wp, formatRel, OptionT.run]
    grind [serialize_parse_inv]

public
theorem serialize_formatRel [ParseableSerializeable a] (x: a):
  (formatRel (serialize x) x)
:= by
  simp [formatRel]

grind_pattern serialize_formatRel => serialize x

public
theorem parse_formatRel [ParseableSerializeable a] (b: Bytes):
  match (parse b: Err a) with
  | none => True
  | some x => formatRel b x
:= by
  grind [formatRel, serialize_parse_inv]

grind_pattern parse_formatRel => parse (a := a) b

public
class BytesCompatibleTracePred (pre: Bytes → τ → Prop) where
  pf: ∀ tr: τ, Comparse.BytesCompatiblePred (pre · tr)

public
instance (pre: Bytes → τ → Prop) [inst: BytesCompatibleTracePred pre] (tr: τ): Comparse.BytesCompatiblePred (pre · tr) := inst.pf tr

public
instance
  [TraceTypes]
  [BytesWellFormed]
  [BytesWellFormed.Has Literal.invariants.well_formed] [BytesWellFormed.Has Concat.invariants.well_formed]
  : BytesCompatibleTracePred Bytes.WellFormed
where
  pf tr := {
    pred_empty := by
      simp [Comparse.BytesLike.empty]
    pred_concat := by
      simp [Comparse.BytesLike.concat]
      grind
    pred_split := by
      intro buf i
      have := Concat.split.WellFormed buf i tr
      simp [Comparse.BytesLike.split]
      grind
    pred_fromByteArray := by
      simp [Comparse.BytesLike.fromByteArray]
  }

public
instance
  [TraceTypes]
  [BytesInvariants]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  : BytesCompatibleTracePred Bytes.Invariant
where
  pf tr := {
    pred_empty := by
      simp [Comparse.BytesLike.empty]
    pred_concat := by
      simp [Comparse.BytesLike.concat]
      grind
    pred_split := by
      intro buf i
      have := Concat.split.Invariant buf i tr
      simp [Comparse.BytesLike.split]
      grind
    pred_fromByteArray := by
      simp [Comparse.BytesLike.fromByteArray]
  }

public
instance
  [TraceTypes]
  [BytesInvariants]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  : BytesCompatibleTracePred Bytes.Publishable
where
  pf tr := {
    pred_empty := by
      simp [Bytes.Publishable, Comparse.BytesLike.empty]
      grind
    pred_concat := by
      simp [Bytes.Publishable, Comparse.BytesLike.concat]
      grind
    pred_split := by
      intro buf i
      have := Concat.split.Invariant buf i tr
      have := Concat.split.label buf i tr
      simp [Bytes.Publishable, Comparse.BytesLike.split]
      grind
    pred_fromByteArray := by
      simp [Bytes.Publishable, Comparse.BytesLike.fromByteArray]
      grind
  }

public
instance
  [TraceTypes]
  [BytesInvariants]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  (l: Label)
  : BytesCompatibleTracePred (Bytes.KnowableBy l)
where
  pf tr := {
    pred_empty := by
      simp [Bytes.KnowableBy, Comparse.BytesLike.empty]
      grind
    pred_concat := by
      simp [Bytes.KnowableBy, Comparse.BytesLike.concat]
      grind
    pred_split := by
      intro buf i
      have := Concat.split.Invariant buf i tr
      have := Concat.split.label buf i tr
      simp [Bytes.KnowableBy, Comparse.BytesLike.split]
      grind
    pred_fromByteArray := by
      simp [Bytes.KnowableBy, Comparse.BytesLike.fromByteArray]
      grind
  }

public
instance
  [ExecTraceTypes]
  [BaseAttackerKnowledge] [AttackerKnowledge]
  [AttackerKnowledge.Has Literal.attackerKnowledge] [AttackerKnowledge.Has Concat.attackerKnowledge]
  : BytesCompatibleTracePred Bytes.AttackerKnows
where
  pf tr := {
    pred_empty := by
      simp only [Comparse.BytesLike.empty]
      grind [Literal.attacker_knows_literalToBytes]
    pred_concat := by
      simp only [Comparse.BytesLike.concat]
      grind[Concat.attacker_knows_concat]
    pred_split := by
      intro buf i
      have := Concat.attacker_knows_split buf i tr
      simp only [Comparse.BytesLike.split]
      grind
    pred_fromByteArray := by
      simp only [Comparse.BytesLike.fromByteArray]
      grind [Literal.attacker_knows_literalToBytes]
  }

-- TODO naming convention
@[expose]
public
def isWellFormed [ParseableSerializeable a] (pre: Bytes → τ → Prop) (x: a) (tr: τ): Prop :=
  ParseableSerializeable.mf.wf (pre · tr) x

public
theorem IsWellFormed_FormatRel [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  formatRel buf x →
  (pre buf tr = isWellFormed pre x tr)
:= by
  simp [formatRel, serialize, isWellFormed]
  simp_all [Comparse.ExtensibleMessageFormat.wf_eq]

public
theorem IsWellFormed_FormatRel_BytesWellFormed [TraceTypes] [BytesWellFormed] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.WellFormed tr = isWellFormed Bytes.WellFormed x tr)
:=
  IsWellFormed_FormatRel Bytes.WellFormed

grind_pattern IsWellFormed_FormatRel_BytesWellFormed => formatRel buf x, buf.WellFormed tr

public
theorem IsWellFormed_FormatRel_BytesInvariant [TraceTypes] [BytesInvariant] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Invariant tr = isWellFormed Bytes.Invariant x tr)
:=
  IsWellFormed_FormatRel Bytes.Invariant

grind_pattern IsWellFormed_FormatRel_BytesInvariant => formatRel buf x, buf.Invariant tr

public
theorem IsWellFormed_FormatRel_IsPublishable [TraceTypes] [BytesInvariants] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Publishable tr = isWellFormed Bytes.Publishable x tr)
:=
  IsWellFormed_FormatRel Bytes.Publishable

grind_pattern IsWellFormed_FormatRel_IsPublishable => formatRel buf x, Bytes.Publishable buf tr

public
theorem isWellFormedParse [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  parse buf = some x →
  pre buf tr →
  isWellFormed pre x tr
:= by
  have := serialize_parse_inv buf x
  simp_all [serialize, isWellFormed]
  grind [Comparse.ExtensibleMessageFormat.wf_eq]

end DY.Comparse
