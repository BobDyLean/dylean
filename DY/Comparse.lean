module

public import DY.Bytes

namespace DY.Comparse

variable [BytesFunctor]

public
class ParseableSerializeable (a: Type) where
  parse: Bytes -> Err a
  serialize: a -> Bytes

  parse_serialize_inv:
    ∀ x: a,
      parse (serialize x) = some x

  serialize_parse_inv:
    ∀ buf: Bytes, ∀ x: a,
      parse buf = some x →
      buf = serialize x

export ParseableSerializeable (parse)
export ParseableSerializeable (serialize)
export ParseableSerializeable (parse_serialize_inv)
export ParseableSerializeable (serialize_parse_inv)

@[simp]
public
theorem parse_serialize_inv_grind [ParseableSerializeable a] (x: a):
  ParseableSerializeable.parse (serialize x) = some x
  := by
  exact (parse_serialize_inv x)

grind_pattern parse_serialize_inv_grind => serialize x

public
def formatRel [ParseableSerializeable a] (buf: Bytes) (x: a) :=
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

@[grind! .]
public
theorem parse_formatRel [ParseableSerializeable a] (b: Bytes):
  match (parse b: Err a) with
  | none => True
  | some x => formatRel b x
  := by
    grind [formatRel, serialize_parse_inv]

@[expose]
public
def isWellFormed [ParseableSerializeable a] (pre: Bytes → τ → Prop) (x: a) (tr: τ): Prop :=
  pre (serialize x) tr

public
theorem isWellFormedFormatRel [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  formatRel buf x →
  (pre buf tr = isWellFormed pre x tr)
  := by
    grind [isWellFormed, formatRel]

public
theorem isWellFormedFormatRelBytesWellFormed [TraceTypes] [BytesWellFormed] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.WellFormed tr = isWellFormed Bytes.WellFormed x tr)
  := isWellFormedFormatRel Bytes.WellFormed

grind_pattern isWellFormedFormatRelBytesWellFormed => formatRel buf x, buf.WellFormed tr

public
theorem isWellFormedFormatRelBytesInvariant [TraceTypes] [BytesInvariant] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Invariant tr = isWellFormed Bytes.Invariant x tr)
  := isWellFormedFormatRel Bytes.Invariant

grind_pattern isWellFormedFormatRelBytesInvariant => formatRel buf x, buf.Invariant tr

public
theorem isWellFormedFormatRelIsPublishable [TraceTypes] [BytesInvariants] [ParseableSerializeable a]:
  ∀ (buf: Bytes) (x: a) (tr: ProofTrace),
  formatRel buf x →
  (buf.Publishable tr = isWellFormed Bytes.Publishable x tr)
  := isWellFormedFormatRel Bytes.Publishable

grind_pattern isWellFormedFormatRelIsPublishable => formatRel buf x, Bytes.Publishable buf tr

public
theorem isWellFormedParse [ParseableSerializeable a] (pre: Bytes → τ → Prop) (buf: Bytes) (x: a) (tr: τ):
  parse buf = some x →
  pre buf tr →
  isWellFormed pre x tr
  := by
    grind [isWellFormed, serialize_parse_inv]

public
class BytesCompatible (pre: Bytes → τ → Prop) where
  dummy: Unit

public
instance [TraceTypes] [BytesWellFormed]: BytesCompatible Bytes.WellFormed where
  dummy := ()

public
instance [TraceTypes] [BytesInvariant]: BytesCompatible Bytes.Invariant where
  dummy := ()

public
instance [TraceTypes] [BytesInvariants]: BytesCompatible Bytes.Publishable where
  dummy := ()

public
instance [TraceTypes] [BytesInvariants] (l: Label): BytesCompatible (Bytes.KnowableBy l) where
  dummy := ()

public
instance [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]: BytesCompatible Bytes.AttackerKnows where
  dummy := ()

public
axiom comparseMetaProgramExists {a: Type}: ParseableSerializeable a

end DY.Comparse
