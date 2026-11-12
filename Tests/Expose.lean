module

import DY
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.Sign
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentGlobalState
import DY.Actions.PersistentLocalState

/-!
  Checks that the definitions of the DY model that downstream proofs need to unfold
  are exposed to plain `import DY` (no `import all`).

  Every `example` below is a definitional unfolding (or a lemma application) that
  only type-checks when the body of the corresponding definition is visible.
  This guards against accidentally re-sealing a definition that is part of the
  reasoning API (e.g. for refinement proofs between a protocol model and an
  implementation, which reason about the operational semantics directly rather
  than through Hoare triples).
-/

namespace Tests.Expose

open DY

section Trace

variable [ExecTraceTypes]

example {α: Type} (x: Traceful α) (tr: ExecTrace): x.run tr = x tr := rfl

example {α: Type} (f: (tr: ExecTrace) → Option α × { trOut // tr ≤ trOut }): Traceful.mk f = f := rfl

example {EntryT: Type} [ExecTraceTypes.Has EntryT] (entry: EntryT)
  : appendEntry entry = Traceful.mk fun tr => (some tr.length, ⟨tr.append entry, Trace.append_le tr entry⟩)
:= rfl

example {EntryT: Type} [ExecTraceTypes.Has EntryT] (timestamp: Nat)
  : (getEntry timestamp: Traceful EntryT) = Traceful.mk fun tr => ((tr.at? timestamp: Option EntryT), ⟨tr, Trace.le_refl tr⟩)
:= rfl

example: getTimestamp = Traceful.mk fun tr => (some tr.length, ⟨tr, Trace.le_refl tr⟩) := rfl

end Trace

section Fixpoint

example {α: Type} (f: Fixpoint.Set α → Fixpoint.Set α) (x: α)
  : Fixpoint.mkLeastFixpoint f x = ∀ s: Fixpoint.Set α, (∀ y, f s y → s y) → s x
:= rfl

end Fixpoint

section Actions

variable [BytesFunctor] [ExecTraceTypes]

example [ExecTraceTypes.Has Network.ExecEntryT] (msg: Bytes)
  : Network.sendMessage msg = appendEntry ({ msg }: Network.ExecEntryT)
:= by unfold Network.sendMessage; rfl

example [ExecTraceTypes.Has Network.ExecEntryT] (handle: Nat)
  : Network.receiveMessage handle = (do
      let msg: Network.ExecEntryT ← getEntry handle
      pure msg.msg)
:= rfl

example [ExecTraceTypes.Has Network.ExecEntryT] (tr: ExecTrace) (b: Bytes) (i: Nat)
  : tr.MessageSentAt b i = (tr.at? i = some ({ msg := b }: Network.ExecEntryT))
:= rfl

example [ExecTraceTypes.Has Network.ExecEntryT] (tr: ExecTrace) (b: Bytes)
  : tr.MessageSent b = ∃ i, tr.MessageSentAt b i
:= rfl

example [ExecTraceTypes.Has Network.ExecEntryT] (tr: ExecTrace) (i: Nat)
  : tr.getMessageSentAt i = (match (tr.at? i: Option Network.ExecEntryT) with
      | none => none
      | some entry => some entry.msg)
:= rfl

example (tr: ExecTrace) (entry: Network.ExecEntryT) (msg: Bytes)
  : Network.baseAttackerKnowledge.attackerKnows tr entry msg = (msg = entry.msg)
:= rfl

example {EventT: Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)] (ev: EventT) (time: Nat) (tr: ExecTrace)
  : tr.EventLoggedAt ev time = (tr.at? time = some ({ ev }: ProtocolEvent.ExecEntryT EventT))
:= rfl

example (EventT: Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)] (i: Nat) (tr: ExecTrace)
  : Trace.getEventAt EventT i tr = (match (tr.at? i: Option (ProtocolEvent.ExecEntryT EventT)) with
      | none => none
      | some entry => some entry.ev)
:= rfl

example {EventT: Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)] (ev: EventT)
  : ProtocolEvent.logEvent ev = (do
      let _ ← appendEntry ({ ev }: ProtocolEvent.ExecEntryT EventT)
      pure ())
:= rfl

example (EventT: Type) (tr: ExecTrace) (entry: ProtocolEvent.ExecEntryT EventT) (b: Bytes)
  : (ProtocolEvent.baseAttackerKnowledge EventT).attackerKnows tr entry b = False
:= rfl

example [BytesFunctor.Has Random.SubF] [ExecTraceTypes.Has Random.ExecEntryT] (size: Nat)
  : Random.genRand size = (do
      let time ← appendEntry ({ length := size }: Random.ExecEntryT)
      pure (({ timestamp := time, size }: Random.Random Bytes).pack))
:= rfl

example (p: Bytes → Prop) (out: Bytes) [BytesFunctor.Has Random.SubF]
  : Random.attKnowsRand.pred p out = False
:= rfl

example (tr: ExecTrace) (entry: Random.ExecEntryT) (b: Bytes)
  : Random.baseAttackerKnowledge.attackerKnows tr entry b = False
:= rfl

example {StateT: Type} [ExecTraceTypes.Has (PersistentGlobalState.State.ExecEntryT StateT)] (st: StateT)
  : PersistentGlobalState.storeGlobalState st = appendEntry ({ st }: PersistentGlobalState.State.ExecEntryT StateT)
:= by unfold PersistentGlobalState.storeGlobalState; rfl

example {StateT: Type} [ExecTraceTypes.Has (PersistentGlobalState.State.ExecEntryT StateT)] (handle: Nat)
  : PersistentGlobalState.getGlobalState handle = (do
      let e: PersistentGlobalState.State.ExecEntryT StateT ← getEntry handle
      pure e.st)
:= rfl

example (StateT: Type) (tr: ExecTrace) (entry: PersistentGlobalState.State.ExecEntryT StateT) (b: Bytes)
  : (PersistentGlobalState.State.baseAttackerKnowledge StateT).attackerKnows tr entry b = False
:= rfl

example {StateT: Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)]
  (participant: Participant) (state: StateT)
  : PersistentLocalState.storeLocalState participant state =
    PersistentGlobalState.storeGlobalState ({ participant, state }: PersistentLocalState.LocalState StateT)
:= rfl

example {StateT: Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)]
  (participant: Participant) (handle: Nat)
  : PersistentLocalState.getLocalState participant handle = (do
      let st: PersistentLocalState.LocalState StateT ← PersistentGlobalState.getGlobalState handle
      guard (st.participant = participant)
      pure st.state)
:= rfl

end Actions

section AttackerKnowledge

variable [BytesFunctor] [ExecTraceTypes]

example [BaseAttackerKnowledge] (tr: ExecTrace) (b: Bytes)
  : tr.BaseAttackerKnows b = ∃ i h_i, BaseAttackerKnowledge.attackerKnows.attackerKnows (tr.prefix i) (tr.at i h_i) b
:= rfl

example [BaseAttackerKnowledge] (tr: ExecTrace)
  : Bytes.AttackerKnows.baseKnowledge tr = SubAttackerKnowledge.fromPred tr.BaseAttackerKnows
:= rfl

example {n: Nat} {Types: Fin n → Type}
  (subs: (id: Fin n) → SubBaseAttackerKnowledge (Types id))
  (tr: ExecTrace) (x: ExecTraceTypes.combine Types) (b: Bytes)
  : (SubBaseAttackerKnowledge.combine subs).attackerKnows tr x b = (subs x.id).attackerKnows tr x.entry b
:= by simp

example {n: Nat} {SubF: Type → Type} (atts: Fin n → SubAttackerKnowledge SubF)
  : (SubAttackerKnowledge.combine' atts).pred = Fixpoint.combine fun id => (atts id).pred
:= by simp

end AttackerKnowledge

section EquationalTheory

variable [BytesFunctor]

example [BytesFunctor.Has Concat.SubF] [BytesLength] (p: Bytes → Prop) (out: Bytes)
  : Concat.concat.attackerKnowledge.pred p out = ∃ lhs rhs, out = Concat.concat lhs rhs ∧ p lhs ∧ p rhs
:= rfl

example [BytesFunctor.Has Concat.SubF] [BytesLength] (p: Bytes → Prop) (out: Bytes)
  : Concat.splitLeft.attackerKnowledge.pred p out = ∃ inp rhs i, some (out, rhs) = Concat.split inp i ∧ p inp
:= rfl

example [BytesFunctor.Has Concat.SubF] [BytesLength] (p: Bytes → Prop) (out: Bytes)
  : Concat.splitRight.attackerKnowledge.pred p out = ∃ inp lhs i, some (lhs, out) = Concat.split inp i ∧ p inp
:= rfl

example [BytesFunctor.Has DiffieHellman.SubF] (p: Bytes → Prop) (out: Bytes)
  : DiffieHellman.dhPk.attackerKnowledge.pred p out = ∃ sk, out = DiffieHellman.dhPk sk ∧ p sk
:= rfl

example [BytesFunctor.Has DiffieHellman.SubF] (p: Bytes → Prop) (out: Bytes)
  : DiffieHellman.dh.attackerKnowledge.pred p out = ∃ pk sk, out = DiffieHellman.dh pk sk ∧ p pk ∧ p sk
:= rfl

example [BytesFunctor.Has KdfExtract.SubF] (p: Bytes → Prop) (out: Bytes)
  : KdfExtract.kdfExtract.attackerKnowledge.pred p out = ∃ salt ikm, out = KdfExtract.kdfExtract salt ikm ∧ p salt ∧ p ikm
:= rfl

example [BytesFunctor.Has Literal.SubF] (p: Bytes → Prop) (out: Bytes)
  : Literal.literalToBytes.attackerKnowledge.pred p out = ∃ lit, out = Literal.literalToBytes lit
:= rfl

example [BytesFunctor.Has Signature.SubF] (p: Bytes → Prop) (out: Bytes)
  : Signature.vk.attackerKnowledge.pred p out = ∃ sk, out = Signature.vk sk ∧ p sk
:= rfl

example [BytesFunctor.Has Signature.SubF] (p: Bytes → Prop) (out: Bytes)
  : Signature.sign.attackerKnowledge.pred p out = ∃ sk nonce msg, out = Signature.sign sk nonce msg ∧ p sk ∧ p nonce ∧ p msg
:= rfl

example (x: KdfExtract.KdfExtract.SubF Bytes) (rec: ∀ y: Bytes, sizeOf y ≤ ALaCarte.FunctorSizeOf.sizeOf x → Nat)
  : KdfExtract.KdfExtract.SubF.length x rec = 32
:= rfl

example (timestamp size: Nat)
  (rec: ∀ y: Bytes, sizeOf y ≤ ALaCarte.FunctorSizeOf.sizeOf ({ timestamp, size }: Random.Random Bytes) → Nat)
  : Random.Random.length { timestamp, size } rec = size
:= rfl

end EquationalTheory

section Bytes

variable [BytesFunctor]

example [BytesLength] (b: Bytes): b.length = Bytes.rec BytesLength.funs b := rfl

example {SubF: Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] (x y: BytesView SubF)
  (h: x.pack = y.pack): x = y
:= BytesView.pack_inj.mp h

example {n: Nat} {SubFs: Fin n → Type → Type} [∀ id, SubBytesFunctor (SubFs id)] {a: Type}
  (funs: (id: Fin n) → Bytes.PartialFunction (SubFs id) a)
  (x: BytesFunctor.combine SubFs Bytes)
  (rec: ∀ y: Bytes, sizeOf y ≤ ALaCarte.FunctorSizeOf.sizeOf x → a)
  : Bytes.PartialFunction.combine funs x rec = funs x.id x.val rec
:= Bytes.PartialFunction.combine_apply funs x rec

-- Two different constructors never pack to the same bytes when the
-- side condition reduces to `none` by `rfl` (true for disjoint summands of a
-- concrete `BytesFunctor`, see `BytesView.pack_ne_pack`).
example
  {SubF1 SubF2: Type → Type}
  [SubBytesFunctor SubF1] [SubBytesFunctor SubF2]
  [BytesFunctor.Has SubF1] [BytesFunctor.Has SubF2]
  (x: BytesView SubF1) (y: BytesView SubF2)
  (h: ALaCarte.SubFunctorTC.proj (f := SubF2) (ALaCarte.SubFunctorTC.inj (f := SubF1) (g := BytesF) x) = none)
  : x.pack ≠ y.pack
:= BytesView.pack_ne_pack x y h

end Bytes

section Comparse

variable [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

example {a: Type} [Comparse.ParseableSerializeable a] (x: a)
  : Comparse.serialize x = Comparse.ParseableSerializeable.mf.serialize x
:= rfl

example {a: Type} [Comparse.ParseableSerializeable a] (buf: Bytes)
  : Comparse.parse buf = (Comparse.ParseableSerializeable.mf.parse buf: Err a)
:= rfl

example {B: Type} [_root_.Comparse.BytesLike B] (prefixes: List B) (suffix: B)
  : _root_.Comparse.concatPrefixes prefixes suffix = List.foldr _root_.Comparse.BytesLike.concat suffix prefixes
:= rfl

end Comparse

end Tests.Expose
