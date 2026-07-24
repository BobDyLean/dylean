module

import DY.Meta
public import Examples.Ratchet.Specification
import all Examples.Ratchet.Specification

namespace DY.Example.Ratchet

open DY.Comparse

-- Future work: the following section is boilerplate that could be meta-programmed
public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT RatchetEvent)]
  [traceProof3: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT StateMyTurn)]
  [traceProof4: ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT StateOtherTurn)]
  [traceProof5: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "Ratchet PKI")]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3
attribute [reducible, scoped instance] HasProofTrace.traceProof4
attribute [reducible, scoped instance] HasProofTrace.traceProof5

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

def transcriptToHash (transcript: Transcript): Bytes :=
  transcript.foldr (fun elem txhash => computeTranscriptHash txhash elem) initialTranscriptHash

theorem computeTranscriptHash_neq_initialTranscriptHash
  (previousTxHash: Bytes) (elem: TranscriptElement)
  : initialTranscriptHash ≠ computeTranscriptHash previousTxHash elem
:= by
  have: initialTranscriptHash.length = 0 := by
    simp [initialTranscriptHash, Comparse.BytesLike.empty]
  have: (computeTranscriptHash previousTxHash elem).length ≠ 0 := by
    simp [computeTranscriptHash]
  grind

theorem computeTranscriptHash_inj
  (previousTxHash1: Bytes) (elem1: TranscriptElement)
  (previousTxHash2: Bytes) (elem2: TranscriptElement)
  : computeTranscriptHash previousTxHash1 elem1 = computeTranscriptHash previousTxHash2 elem2 →
    (previousTxHash1 = previousTxHash2 ∧ elem1 = elem2)
:= by
  simp only [computeTranscriptHash]
  grind [Hash.hash_inj]

@[grind inj]
theorem transcriptToHash_inj
  : Function.Injective transcriptToHash
:= by
  unfold Function.Injective
  intro transcript1 transcript2
  induction transcript1 generalizing transcript2
  · cases transcript2 <;>
    simp [transcriptToHash, computeTranscriptHash_neq_initialTranscriptHash]
  cases transcript2
  · simp [transcriptToHash]
    grind [computeTranscriptHash_neq_initialTranscriptHash]
  simp_all only [transcriptToHash, List.foldr_cons, List.cons.injEq]
  grind [computeTranscriptHash_inj]

def stateLabel
  (me: Participant) (transcript: Transcript)
  : Label
where
  isCorrupt tr := StateCompromised me transcript tr

def stateTxHashLabel
  (txHash: Bytes)
  : Label
where
  isCorrupt tr :=
    ∃ transcript,
      transcriptToHash transcript = txHash ∧
      match transcript with
      | e1::e2::_ =>
        StateCompromised e1.recipient transcript tr ∨ StateCompromised e2.recipient transcript tr
      | _ => True
  isCorruptLater tr1 tr2 _ := by
    intro _ -- grind bug?
    grind

theorem stateTxHashLabel_eq
  (transcript: Transcript)
  (h: 2 ≤ transcript.length)
  : stateTxHashLabel (transcriptToHash transcript) =
      (stateLabel transcript[0].recipient transcript).join (stateLabel transcript[1].recipient transcript)
:= by
  ext
  simp [stateTxHashLabel, stateLabel]
  grind [cases List]

instance: KdfExpand.KdfExpandInvariant where
  usage prkUsage info := Usage.nothing
  label prkUsage prkLabel info :=
    prkLabel.join (stateTxHashLabel info)

mutual
def isKeyMyTurn (l: Transcript) (k: Bytes): Prop :=
  match l with
  | [] | [_] => k = firstKey
  | e1::e2::rest =>
    ∃ kPrev dhSk,
      isKeyOtherTurn (e2::rest) kPrev ∧
      DiffieHellman.dhPk dhSk = e2.dhPk ∧
      k = KdfExpand.kdfExpand (KdfExtract.kdfExtract (DiffieHellman.dh e1.dhPk dhSk) kPrev) (transcriptToHash l) 32

def isKeyOtherTurn (l: Transcript) (k: Bytes): Prop :=
  match l with
  | [] | [_] => k = firstKey
  | e1::e2::rest =>
    ∃ kPrev dhSk,
      isKeyMyTurn (e2::rest) kPrev ∧
      DiffieHellman.dhPk dhSk = e1.dhPk ∧
      k = KdfExpand.kdfExpand (KdfExtract.kdfExtract (DiffieHellman.dh e2.dhPk dhSk) kPrev) (transcriptToHash l) 32
end

theorem isKeyMyTurn_isKeyOtherTurn
  (l: Transcript) (k1 k2: Bytes)
  : isKeyMyTurn l k1 →
    isKeyOtherTurn l k2 →
    k1 = k2
:= by
  induction l generalizing k1 k2
  · simp [isKeyMyTurn, isKeyOtherTurn]; grind
  rename_i e1 e2rest _
  cases e2rest
  · simp [isKeyMyTurn, isKeyOtherTurn]; grind
  rename_i e2 rest _
  conv => lhs; unfold isKeyMyTurn
  conv => rhs; lhs; unfold isKeyOtherTurn
  grind

def labelBeforeTimestamp (l: Label) (i: Nat): Label where
  isCorrupt tr := l.isCorrupt (tr.prefix i)

def labelBeforeEvent (l: Label) (me other: Participant) (transcript: Transcript): Label where
  isCorrupt tr :=
    ∃ trBefore,
      trBefore ≤ tr ∧
      l.isCorrupt trBefore ∧
      (¬ (∃ k, trBefore.EventLogged (RatchetEvent.ReceiveUpdate me other transcript k)))
  isCorruptLater := by grind [Trace.le_trans]

theorem labelBeforeEvent_canFlow_labelBeforeTimestamp
  (l: Label) (me other: Participant) (transcript: Transcript)
  (i: Nat)
  (tr: ExecTrace)
  : i ≤ tr.length →
    (∃ k, (tr.prefix i).EventLogged (RatchetEvent.ReceiveUpdate me other transcript k)) →
    (∀ i', i' < i → ¬ ∃ k, (tr.prefix i').EventLogged (RatchetEvent.ReceiveUpdate me other transcript k)) →
    (labelBeforeEvent l me other transcript).canFlow (labelBeforeTimestamp l (i-1)) tr
:= by
  simp only [Label.canFlow, labelBeforeEvent, labelBeforeTimestamp]
  intro h1 h2 h3
  intro trLater h_le h
  exists tr.prefix (i-1)
  apply And.intro; grind [Trace.le_trans]
  apply And.intro
  · grind
  grind

noncomputable
def minimum.aux (p: Nat → Prop) (i1 i2: Nat): Nat := by
  by_cases i1 ≥ i2 ∨ p i1
  · exact i1
  · exact minimum.aux p (i1+1) i2
termination_by i2-i1

omit [HasProofTrace] in
theorem minimum.aux.thm
  (p: Nat → Prop) (i1 i2: Nat)
  : (∀ i, i < i1 → ¬ p i) →
    p i2 →
    p (minimum.aux p i1 i2) ∧
    (∀ i, i < (minimum.aux p i1 i2) → ¬ p i)
:= by
  fun_induction minimum.aux <;> grind

omit [HasProofTrace] in
theorem minimum
  (p: Nat → Prop) (i: Nat) (h: p i)
  : ∃ min, p min ∧ ∀ i', i' < min → ¬ p i'
:=
  ⟨ minimum.aux p 0 i, minimum.aux.thm p 0 i (by grind) h ⟩

theorem event_minimum_prefix
  {EventT: Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (pred: EventT → Prop)
  (tr: ExecTrace)
  : (∃ ev, pred ev ∧ tr.EventLogged ev) →
    ∃ i ev',
      pred ev' ∧
      tr.EventLoggedAt ev' i ∧
      (tr.prefix (i+1)).EventLogged ev' ∧
      (∀ i' ev'', i' ≤ i → pred ev'' → ¬ (tr.prefix i').EventLogged ev'')
:= by
  intro _
  have ⟨ i, h_logged_before_i, h_not_logged ⟩ := minimum (fun i => ∃ ev, pred ev ∧ (tr.prefix i).EventLogged ev) tr.length (by grind)
  have ⟨ ev', h_pred, i', h_logged ⟩ := h_logged_before_i
  by_cases i' = i-1
  · grind
  exfalso
  have := h_not_logged (i'+1) (by grind)
  simp only [Trace.EventLogged, not_exists, not_and] at this
  apply this ev' h_pred i'
  have := DY.Trace.EventLoggedAt_le' ev' i' (tr.prefix (i'+1)) (tr.prefix i) (by grind) (by grind)
  grind

def ltkLabel (p: Participant): Label where
  isCorrupt tr := ∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" p spk tr

mutual
def keyLabelMyTurn (me other: Participant) (transcript: Transcript): Label :=
  match transcript with
  | [] | [_] => Label.pub
  | _::transcriptTail =>
    (((stateLabel me transcript).join (stateLabel other transcript)).join (
      (keyLabelOtherTurn me other transcriptTail).meet (
        (stateLabel me transcriptTail).join (
          (stateLabel other transcript).join (labelBeforeEvent (ltkLabel other) me other transcript)
        )
      )
    ))

def keyLabelOtherTurn (me other: Participant) (transcript: Transcript): Label :=
  match transcript with
  | [] | [_] => Label.pub
  | _::transcriptTail =>
    (((stateLabel me transcript).join (stateLabel other transcript)).join (
      (keyLabelMyTurn me other transcriptTail).meet (
        (stateLabel me transcript).join (
          (stateLabel other transcriptTail).join (labelBeforeEvent (ltkLabel other) me other transcriptTail)
        )
      )
    ))
end

theorem keyLabelMyTurn_shortTranscript
  (me other: Participant) (transcript: Transcript)
  : transcript.length ≤ 1 →
    keyLabelMyTurn me other transcript = Label.pub
:= by
  unfold keyLabelMyTurn
  grind [cases List]

theorem keyLabelOtherTurn_shortTranscript
  (me other: Participant) (transcript: Transcript)
  : transcript.length ≤ 1 →
    keyLabelOtherTurn me other transcript = Label.pub
:= by
  unfold keyLabelOtherTurn
  grind [cases List]

theorem keyLabelMyTurn_eq
  (me other: Participant) (transcript: Transcript)
  : 2 ≤ transcript.length →
    keyLabelMyTurn me other transcript =
    (((stateLabel me transcript).join (stateLabel other transcript)).join (
      (keyLabelOtherTurn me other transcript.tail).meet (
        (stateLabel me transcript.tail).join (
          (stateLabel other transcript).join (labelBeforeEvent (ltkLabel other) me other transcript)
        )
      )
    ))
:= by
  unfold keyLabelMyTurn
  grind

theorem keyLabelOtherTurn_eq
  (me other: Participant) (transcript: Transcript)
  : 2 ≤ transcript.length →
    keyLabelOtherTurn me other transcript =
    (((stateLabel me transcript).join (stateLabel other transcript)).join (
      (keyLabelMyTurn me other transcript.tail).meet (
        (stateLabel me transcript).join (
          (stateLabel other transcript.tail).join (labelBeforeEvent (ltkLabel other) me other transcript.tail)
        )
      )
    ))
:= by
  unfold keyLabelOtherTurn
  grind

structure LongTermKeyUsage where
  principal: Participant

instance : ParseableSerializeable LongTermKeyUsage := .make <|
  .triviallyIsomorphic
    (.string)
    (fun principal => { principal })
    (fun { principal := principal } => principal)

@[grind]
def mkLongTermKeyUsage (me: Participant): Usage := {
  type := "SigKey",
  tag := "Ratchet PKI",
  data := serialize ({ principal := me }: LongTermKeyUsage)
}

@[grind inj]
theorem mkLongTermKeyUsage_inj:
  Function.Injective mkLongTermKeyUsage
  := by
    simp [Function.Injective, mkLongTermKeyUsage]
    grind

instance RatchetSignPred
  : Signature.SignPred
where
  pred skUsg _ msg tr :=
    ∃ signer, skUsg = mkLongTermKeyUsage signer ∧ (
      match parse msg with
      | none => False
      | some (msg: SigInput) =>
        ∃ transcript,
          transcriptToHash transcript = msg.transcriptHash ∧
          (∃ k h,
            isKeyOtherTurn transcript k ∧
            tr.erase.EventLogged (RatchetEvent.SendUpdate signer (transcript.head h).recipient transcript k)
          ) ∧
          (∃ dhSk h, -- work around dhSkLabel :|
            dhSk.WellFormed tr ∧ -- TODO could be removed?
            DiffieHellman.dhPk dhSk = (transcript.head h).dhPk ∧
            dhSk.label tr = stateLabel signer transcript
          )
    )

instance
  [BytesInvariants]
  [BytesInvariants.Has DiffieHellman.DhPk.invariants]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  : Signature.SignPredProof
where
  pred_later := by
    intro _ _ _ _ _ _ _ _ _ _ _
    intro ⟨ server, h ⟩
    exists server
    grind [DiffieHellman.dhPk.WellFormed]

end BytesInvariants

-- Future work: the following section is boilerplate that could be meta-programmed
public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInvProof: BytesInvariantsProofs]
  [bytesInv0: BytesInvariants.Has Random.invariants]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has Hash.invariants]
  [bytesInv4: BytesInvariants.Has Signature.invariants]
  [bytesInv5: BytesInvariants.Has DiffieHellman.invariants]
  [bytesInv6: BytesInvariants.Has KdfExtract.invariants]
  [bytesInv7: BytesInvariants.Has KdfExpand.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3
attribute [           scoped instance] HasBytesInvariants.bytesInv4
attribute [           scoped instance] HasBytesInvariants.bytesInv5
attribute [           scoped instance] HasBytesInvariants.bytesInv6
attribute [           scoped instance] HasBytesInvariants.bytesInv7

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

instance StateMyTurn.Invariant : PersistentLocalState.CompromisableLocalStateInv StateMyTurn
where
  invariant me st tr :=
    let { transcript, recipient, transcriptHash, otherDhPk, k } := st
    transcriptHash = transcriptToHash transcript ∧
    transcriptHash.Publishable tr ∧
    (∀ elem ∈ transcript, elem.dhPk.Publishable tr) ∧
    (∃ h, (transcript.head h).recipient = me) ∧
    (∃ h, (transcript.head h).dhPk = otherDhPk) ∧
    isKeyMyTurn transcript k ∧
    otherDhPk.Publishable tr ∧
    ((stateLabel recipient transcript).join ((labelBeforeEvent (ltkLabel recipient) me recipient transcript))).canFlow (otherDhPk.dhSkLabel tr) tr.erase ∧
    k.Invariant tr ∧
    (k.label tr).canFlow (stateLabel me transcript) tr.erase ∧
    (keyLabelMyTurn me recipient transcript).canFlow (k.label tr) tr.erase ∧
    (tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k))
  invariant_later := by grind
  invariant_implies_KnowableBy me st tr := by
    have: (stateLabel me st.transcript).canFlow (PersistentLocalState.label me st) tr.erase := by
      cases st
      simp [Label.canFlow, stateLabel, StateCompromised]
      grind
    grind [canFlowTrans]

-- for monotonicity
theorem StateMyTurnInv_imp_Invariant
  (participant: Participant) (st: StateMyTurn)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.otherDhPk.Invariant tr ∧
      st.k.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] StateMyTurnInv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr

instance StateOtherTurn.Invariant : PersistentLocalState.CompromisableLocalStateInv StateOtherTurn
where
  invariant me st tr :=
    let { transcript, recipient, transcriptHash, myDhSk, k } := st
    transcriptHash = transcriptToHash transcript ∧
    transcriptHash.Publishable tr ∧
    (∀ elem ∈ transcript, elem.dhPk.Publishable tr) ∧
    (∃ h, (transcript.head h).recipient = recipient) ∧
    (∃ h, (transcript.head h).dhPk = DiffieHellman.dhPk myDhSk) ∧
    isKeyOtherTurn transcript k ∧
    myDhSk.Invariant tr ∧
    myDhSk.label tr = stateLabel me transcript ∧
    k.Invariant tr ∧
    (k.label tr).canFlow (stateLabel me transcript) tr.erase ∧
    (keyLabelOtherTurn me recipient transcript).canFlow (k.label tr) tr.erase ∧
    (tr.erase.EventLogged (RatchetEvent.SendUpdate me recipient transcript k))
  invariant_later := by grind
  invariant_implies_KnowableBy me st tr := by
    have: (stateLabel me st.transcript).canFlow (PersistentLocalState.label me st) tr.erase := by
      cases st
      simp [Label.canFlow, stateLabel, StateCompromised]
      grind
    grind [canFlowTrans]

-- for monotonicity
theorem StateOtherTurnInv_imp_Invariant
  (participant: Participant) (st: StateOtherTurn)
  : PersistentLocalState.LocalStateInv.invariant participant st tr → (
      st.myDhSk.Invariant tr ∧
      st.k.Invariant tr
    )
:= by
  simp [PersistentLocalState.LocalStateInv.invariant]
  grind

grind_pattern [grind_later] StateOtherTurnInv_imp_Invariant => PersistentLocalState.LocalStateInv.invariant participant st tr

@[grind]
instance : LongTermKeys.ProofConfig "Ratchet PKI" mkLongTermKeyUsage (LongTermKeys.label "Ratchet PKI")
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.signkeyLabel tr = LongTermKeys.label "Ratchet PKI" who vk ∧
    vk.SignkeyHasUsage (mkLongTermKeyUsage who) tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

instance RatchetEventInv : ProtocolEvent.EventInv (RatchetEvent)
where
  invariant tr ev :=
    match ev with
    | .SendUpdate me other transcript k =>
      (2 ≤ transcript.length → ∃ k', tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me other transcript.tail k')) ∧
      k.Invariant tr ∧
      (keyLabelOtherTurn me other transcript).canFlow (k.label tr) tr.erase
    | .ReceiveUpdate me other transcript k =>
      (2 ≤ transcript.length → ∃ k', tr.erase.EventLogged (RatchetEvent.SendUpdate me other transcript.tail k')) ∧
      k.Invariant tr ∧
      (∃ h,
        (transcript.head h).dhPk.Invariant tr ∧
        ((stateLabel other transcript).join (labelBeforeTimestamp (ltkLabel other) tr.length)).canFlow ((transcript.head h).dhPk.dhSkLabel tr) tr.erase
      ) ∧
      ( ∀ h: 2 ≤ transcript.length,
        (((stateLabel me transcript).join (stateLabel other transcript)).join (
          (keyLabelOtherTurn me other transcript.tail).meet (
            (stateLabel me transcript.tail).join (
            ((transcript.head (by grind)).dhPk.dhSkLabel tr)
            )
          )
        )).canFlow (k.label tr) tr.erase
       ) ∧
      (
        tr.erase.EventLogged (RatchetEvent.SendUpdate other me transcript k) ∨
        (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" other spk tr.erase)
      )

end TraceInvariant

-- Future work: the following section is boilerplate that could be meta-programmed
public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT RatchetEvent)]
  [traceInv3: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT StateMyTurn)]
  [traceInv4: TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT StateOtherTurn)]
  [traceInv5: TraceInvariant.Has (LongTermKeys.ProofEntryT "Ratchet PKI")]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.traceInv4
attribute [           scoped instance] HasTraceInvariant.traceInv5
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

@[instance]
theorem initialTranscriptHash.spec
  : HoareTriplePure
    (initialTranscriptHash)
    (fun _ => True)
    (fun res tr => res.Publishable tr)
:= by
  apply HoareTriplePure.mk
  intro tr _
  unfold initialTranscriptHash
  -- TODO from here it should be simply `grind`
  simp [Comparse.BytesLike.empty]
  simp [Bytes.Publishable]
  grind

@[instance]
theorem computeTranscriptHash.spec
  (previousTranscriptHash: Bytes) (elem: TranscriptElement)
  : HoareTriplePure
      (computeTranscriptHash previousTranscriptHash elem)
      (fun tr =>
        previousTranscriptHash.Publishable tr ∧
        elem.dhPk.Publishable tr
      )
      (fun res tr =>
        res.Publishable tr
      )
:= by
  apply HoareTriplePure.mk
  intro tr _
  unfold computeTranscriptHash
  lift_lets; intro input
  have: (serialize input).Publishable tr := by grind
  grind [Hash.hash.Invariant, Hash.hash.label]

@[instance]
theorem firstKey.spec
  : HoareTriplePure
    (firstKey)
    (fun _ => True)
    (fun res tr => res.Publishable tr)
:= by
  apply HoareTriplePure.mk
  intro tr _
  unfold firstKey
  -- TODO from here it should be simply `grind`
  simp [Bytes.Publishable]
  grind

@[instance]
theorem initiate.spec (me other: Participant) (mySigKeyHandle: Nat)
  : HoareTriple
    (initiate me other mySigKeyHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initiate
  step with ⟨ fun dhSk => stateLabel me [{ recipient := other, dhPk := (DiffieHellman.dhPk dhSk)}], Usage.nothing ⟩
  step
  step_intro
  step_intro
  hoist
  step
  step
  step
  step with ⟨ fun _ => Label.secret, Usage.nothing ⟩
  step_intro
  step
  step_intro
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    grind [keyLabelOtherTurn_shortTranscript]
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    unfold transcriptToHash isKeyOtherTurn
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind [canFlowTrans]
    grind [keyLabelOtherTurn_shortTranscript]
  step_let sig with ⟨ mkLongTermKeyUsage me ⟩ by
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    left
    apply And.intro; grind
    simp only [Signature.SignPred.pred]
    exists me
    unfold transcriptToHash isKeyOtherTurn
    simp only [parse_serialize_inv, true_and]
    exists transcript
    grind
  step by
    have: (serialize ({ transcriptHash := transcriptHash }: SigInput)).Publishable tr := by grind
    grind
  step
  grind

@[instance]
theorem processInitiate.spec (me other: Participant) (otherVerifKeyHandle: Nat) (msgHandle: Nat)
  : HoareTriple
    (processInitiate me other otherVerifKeyHandle msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold processInitiate
  step
  step
  step_intro
  step_intro
  hoist
  step
  step
  step
  step with ⟨ mkLongTermKeyUsage other ⟩
  step
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro
    · have: transcriptToHash transcript = transcriptHash := by grind [transcriptToHash]
      simp_all [Signature.SignPred.pred, LongTermKeys.IsLongTermPublicKey]
      have : msg.dhPk.dhSkLabel tr = stateLabel other transcript ∨ (LongTermKeys.label "Ratchet PKI" other verifKey).canFlow Label.pub tr.erase := by grind
      simp_all [Label.canFlow, labelBeforeTimestamp, ltkLabel, LongTermKeys.label]
      have: tr.erase.length = tr.length := by grind
      grind
    apply And.intro; grind
    simp_all [Signature.SignPred.pred, LongTermKeys.IsLongTermPublicKey, LongTermKeys.label]
    have: isKeyMyTurn transcript k := by unfold isKeyMyTurn; grind
    have := fun k' => isKeyMyTurn_isKeyOtherTurn transcript k k'
    have : transcriptToHash transcript = transcriptHash := by unfold transcriptToHash; grind
    grind
  step_intro
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    apply And.intro; unfold transcriptToHash; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; unfold isKeyMyTurn; grind
    apply And.intro; grind
    have: ((stateLabel st.recipient st.transcript).join (labelBeforeEvent (ltkLabel st.recipient) me st.recipient st.transcript)).canFlow (msg.dhPk.dhSkLabel tr) tr.erase := by
      have ⟨ i, ev, ⟨ k', h_ev ⟩, _ ⟩ := event_minimum_prefix (fun ev => ∃ k, ev = (RatchetEvent.ReceiveUpdate me st.recipient transcript k)) tr.erase (by grind)
      have := labelBeforeEvent_canFlow_labelBeforeTimestamp (ltkLabel st.recipient) me st.recipient transcript (i+1) tr.erase (by grind) (by grind) (by grind)
      have := Trace.EventLoggedAt_imp_EventInv (RatchetEvent.ReceiveUpdate me st.recipient transcript k') (i) tr (by grind) (by grind)
      simp only [ProtocolEvent.EventInv.invariant] at this
      simp_all [Label.canFlow]
      grind [Trace.le_trans]
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind [canFlowTrans]
    apply And.intro; grind [keyLabelMyTurn_shortTranscript]
    grind
  grind

@[instance]
theorem sendUpdate.spec (me: Participant) (mySigKeyHandle: Nat) (stHandle: Nat)
  : HoareTriple
    (sendUpdate me mySigKeyHandle stHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold sendUpdate
  step
  step with ⟨ fun dhSk => stateLabel me ({ recipient := st.recipient, dhPk := (DiffieHellman.dhPk dhSk)}::st.transcript), Usage.nothing ⟩
  step
  step_intro
  step_intro
  step by
    simp_all [PersistentLocalState.LocalStateInv.invariant]
    grind
  have: transcriptToHash transcript = transcriptHash := by simp_all only [PersistentLocalState.LocalStateInv.invariant, transcriptToHash]; grind
  step
  step with ⟨ fun _ => Label.secret, Usage.nothing ⟩
  step_intro
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  hoist
  step by
    have: st.k.Invariant tr := by simp_all only [PersistentLocalState.LocalStateInv.invariant]
    grind
  step_intro
  step with ⟨ k_prk.usage tr ⟩ by simp [Bytes.HasUsage]; grind
  have: isKeyOtherTurn transcript k := by unfold isKeyOtherTurn; simp_all [PersistentLocalState.LocalStateInv.invariant]; grind
  have: (keyLabelOtherTurn me st.recipient transcript).canFlow (k.label tr) tr.erase := by
    have: ((k_prk.label tr).join (stateTxHashLabel transcriptHash)).canFlow (k.label tr) tr.erase := by
      simp_all [KdfExpand.KdfExpandInvariant.label]
    have: stateTxHashLabel transcriptHash = (stateLabel me transcript).join (stateLabel st.recipient transcript) := by
      simp_all [PersistentLocalState.LocalStateInv.invariant]
      have := stateTxHashLabel_eq transcript
      grind
    have: ((dhss.label tr).meet (keyLabelMyTurn me st.recipient (transcript.tail))).canFlow (k_prk.label tr) tr.erase := by
      simp_all [PersistentLocalState.LocalStateInv.invariant]
      grind [canFlowTrans]
    have: (stateLabel me transcript).canFlow (dhSk.label tr) tr.erase := by grind
    have: ((stateLabel st.recipient transcript.tail).join ((labelBeforeEvent (ltkLabel st.recipient) me st.recipient transcript.tail))).canFlow (st.otherDhPk.dhSkLabel tr) tr.erase := by
      simp_all [PersistentLocalState.LocalStateInv.invariant]
      grind
    have: 2 ≤ transcript.length := by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
    have := keyLabelOtherTurn_eq me st.recipient transcript (by grind)
    simp_all [Label.canFlow]
    have: tr.erase.length = tr.length := by grind
    grind [Trace.le_trans]
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    simp_all [PersistentLocalState.LocalStateInv.invariant]
    grind
  step_intro
  step by
    subst st
    simp only [PersistentLocalState.LocalStateInv.invariant]
    apply And.intro; simp_all [PersistentLocalState.LocalStateInv.invariant, transcriptToHash]
    apply And.intro; grind
    apply And.intro; simp_all [PersistentLocalState.LocalStateInv.invariant]; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro
    · have: (k.label tr).canFlow (stateTxHashLabel transcriptHash) tr.erase := by simp_all only [KdfExpand.KdfExpandInvariant.label]; grind [canFlowTrans]
      simp_all [PersistentLocalState.LocalStateInv.invariant]
      have := stateTxHashLabel_eq transcript
      grind
    apply And.intro; grind
    grind
  step_let sig with ⟨ mkLongTermKeyUsage me ⟩ by
    simp [Signature.SignPred.pred]
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    left
    apply And.intro; grind
    exists me
    apply And.intro; grind
    exists transcript
    apply And.intro; grind
    apply And.intro; grind
    grind
  step by
    have: (serialize ({ transcriptHash := transcriptHash }: SigInput)).Publishable tr := by grind
    grind
  step
  grind

theorem eventLogged_receiveUpdate_dhPk_label
  (me recipient: Participant) (transcript: Transcript) (k: Bytes)
  (tr: ProofTrace)
  (h_transcript: 2 ≤ transcript.length)
  : tr.Invariant →
    tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k) →
    ((stateLabel recipient transcript).join (labelBeforeEvent (ltkLabel recipient) me recipient transcript)).canFlow ((transcript.head (by grind)).dhPk.dhSkLabel tr) tr.erase
:= by
  intro _ _ _
  have ⟨ i, ev, ⟨ k', h_ev ⟩, _ ⟩ := event_minimum_prefix (fun ev => ∃ k, ev = (RatchetEvent.ReceiveUpdate me recipient transcript k)) tr.erase (by grind)
  have := labelBeforeEvent_canFlow_labelBeforeTimestamp (ltkLabel recipient) me recipient transcript (i+1) tr.erase (by grind) (by grind) (by grind)
  have := Trace.EventLoggedAt_imp_EventInv (RatchetEvent.ReceiveUpdate me recipient transcript k') (i) tr (by grind) (by grind)
  simp only [ProtocolEvent.EventInv.invariant] at this
  simp_all [Label.canFlow]
  grind [Trace.le_trans]

theorem eventLogged_receiveUpdate_key_label
  (me recipient: Participant) (transcript: Transcript) (k: Bytes)
  (tr: ProofTrace)
  : 2 ≤ transcript.length →
    tr.Invariant →
    tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k) →
    (keyLabelMyTurn me recipient transcript).canFlow (k.label tr) tr.erase
:= by
  intro _ _ _
  have := eventLogged_receiveUpdate_dhPk_label me recipient transcript k tr
  have := keyLabelMyTurn_eq me recipient transcript (by grind)
  have := Trace.EventLogged_imp_EventInv (RatchetEvent.ReceiveUpdate me recipient transcript k) tr (by grind) (by grind)
  simp only [ProtocolEvent.EventInv.invariant] at this
  simp_all [Label.canFlow]
  have: tr.erase.length = tr.length := by grind
  grind [Trace.le_trans]

@[instance]
theorem processUpdate.spec (me: Participant) (otherVerifKeyHandle: Nat) (stHandle msgHandle: Nat)
  : HoareTriple
    (processUpdate me otherVerifKeyHandle stHandle msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold processUpdate
  step
  step
  step
  step_intro
  step_intro
  step by
    simp_all [PersistentLocalState.LocalStateInv.invariant]
    grind
  have: transcriptToHash transcript = transcriptHash := by simp_all only [PersistentLocalState.LocalStateInv.invariant, transcriptToHash]; grind
  step
  step with ⟨ mkLongTermKeyUsage st.recipient ⟩
  step by simp_all [PersistentLocalState.LocalStateInv.invariant]; grind
  hoist
  step by simp_all [PersistentLocalState.LocalStateInv.invariant]
  step_intro
  step with ⟨ k_prk.usage tr ⟩ by simp_all [PersistentLocalState.LocalStateInv.invariant, Bytes.HasUsage]
  have: isKeyMyTurn transcript k := by unfold isKeyMyTurn; simp_all [PersistentLocalState.LocalStateInv.invariant]; grind
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    apply And.intro
    · simp_all [PersistentLocalState.LocalStateInv.invariant, Bytes.HasUsage]
      grind
    apply And.intro; grind
    apply And.intro
    · simp_all [PersistentLocalState.LocalStateInv.invariant]
      simp_all [Signature.SignPred.pred, LongTermKeys.IsLongTermPublicKey]
      have : msg.dhPk.dhSkLabel tr = stateLabel st.recipient transcript ∨ (LongTermKeys.label "Ratchet PKI" st.recipient verifKey).canFlow Label.pub tr.erase := by grind
      simp_all [Label.canFlow, labelBeforeTimestamp, ltkLabel, LongTermKeys.label]
      have: tr.erase.length = tr.length := by grind
      grind
    apply And.intro
    · have: ((k_prk.label tr).join (stateTxHashLabel transcriptHash)).canFlow (k.label tr) tr.erase := by
        simp_all [KdfExpand.KdfExpandInvariant.label]
      have: stateTxHashLabel transcriptHash = (stateLabel me transcript).join (stateLabel st.recipient transcript) := by
        simp_all [PersistentLocalState.LocalStateInv.invariant]
        have := stateTxHashLabel_eq transcript
        grind
      have: ((dhss.label tr).meet (keyLabelOtherTurn me st.recipient (transcript.tail))).canFlow (k_prk.label tr) tr.erase := by
        simp_all [PersistentLocalState.LocalStateInv.invariant]
        grind [canFlowTrans]
      have: (stateLabel me transcript.tail).canFlow (st.myDhSk.label tr) tr.erase := by simp_all [PersistentLocalState.LocalStateInv.invariant]; grind
      grind [Label.canFlow]
    simp_all [Signature.SignPred.pred, LongTermKeys.IsLongTermPublicKey, LongTermKeys.label]
    have := fun k' => isKeyMyTurn_isKeyOtherTurn transcript k k'
    grind
  step_intro
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant]
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro; grind
    apply And.intro
    · have := eventLogged_receiveUpdate_dhPk_label me st.recipient st.transcript st.k tr
      simp_all [PersistentLocalState.LocalStateInv.invariant]
      grind
    apply And.intro; grind
    apply And.intro
    · have: (k.label tr).canFlow (stateTxHashLabel transcriptHash) tr.erase := by simp_all only [KdfExpand.KdfExpandInvariant.label]; grind [canFlowTrans]
      simp_all [PersistentLocalState.LocalStateInv.invariant]
      have := stateTxHashLabel_eq transcript
      grind
    have := eventLogged_receiveUpdate_key_label me st.recipient st.transcript st.k tr
    have: 2 ≤ transcript.length := by simp_all only [PersistentLocalState.LocalStateInv.invariant]; grind
    apply And.intro; grind
    grind
  grind

@[instance]
theorem StateMyTurn.compromise.spec (stHandle: Nat): HoareTriple (StateMyTurn.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold StateMyTurn.compromise; step; grind

@[instance]
theorem StateOtherTurn.compromise.spec (stHandle: Nat): HoareTriple (StateOtherTurn.compromise stHandle) (fun _ => True) (fun _ _ => True)
:= by unfold StateOtherTurn.compromise; step; grind

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

-- Future work: the following section is boilerplate that could be meta-programmed
section
public instance: ReachableImpliesInvariant initiate.reachability := .mk (fun (me, other, mySigKeyHandle) => initiate.spec me other mySigKeyHandle)
public instance: ReachableImpliesInvariant processInitiate.reachability := .mk (fun (me, other, otherVerifKeyHandle, msgHandle) => processInitiate.spec me other otherVerifKeyHandle msgHandle)
public instance: ReachableImpliesInvariant sendUpdate.reachability := .mk (fun (me, mySigKeyHandle, stHandle) => sendUpdate.spec me mySigKeyHandle stHandle)
public instance: ReachableImpliesInvariant processUpdate.reachability := .mk (fun (me, otherVerifKeyHandle, stHandle, msgHandle) => processUpdate.spec me otherVerifKeyHandle stHandle msgHandle)
public instance: ReachableImpliesInvariant StateMyTurn.compromise.reachability := .mk (fun (stHandle) => StateMyTurn.compromise.spec stHandle)
public instance: ReachableImpliesInvariant StateOtherTurn.compromise.reachability := .mk (fun (stHandle) => StateOtherTurn.compromise.spec stHandle)
end

#combine into ReachabilityTheorem from
  Network,
  LongTermKeys "Ratchet PKI",
  initiate,
  processInitiate,
  sendUpdate,
  processUpdate,
  StateMyTurn.compromise,
  StateOtherTurn.compromise,

end ReachabilityImpliesInvariant

section LabelLemma

variable [HasTraceInvariant]

theorem keyLabelMyTurn_isCorrupt_eq
  (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
  : (keyLabelMyTurn me recipient transcript).isCorrupt tr = (
      (
        transcript.length ≤ 1 ∨
        StateCompromised me transcript tr ∨
        StateCompromised me transcript.tail tr ∨
        StateCompromised recipient transcript tr
      ) ∨ (
        (keyLabelOtherTurn me recipient transcript.tail).isCorrupt tr ∧
        (labelBeforeEvent (ltkLabel recipient) me recipient transcript).isCorrupt tr
      )
    )
:= by
  have: StateCompromised me transcript.tail tr → (keyLabelOtherTurn me recipient transcript.tail).isCorrupt tr := by
    unfold keyLabelOtherTurn
    split
    · grind
    · grind
    simp [stateLabel]
    grind
  unfold keyLabelMyTurn
  split
  · grind
  · grind
  simp [stateLabel]
  grind

theorem keyLabelOtherTurn_isCorrupt_eq
  (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
  : (keyLabelOtherTurn me recipient transcript).isCorrupt tr = (
      (
        transcript.length ≤ 1 ∨
        StateCompromised me transcript tr ∨
        StateCompromised recipient transcript tr ∨
        StateCompromised recipient transcript.tail tr
      ) ∨ (
        (keyLabelMyTurn me recipient transcript.tail).isCorrupt tr ∧
        (labelBeforeEvent (ltkLabel recipient) me recipient transcript.tail).isCorrupt tr
      )
    )
:= by
  have: StateCompromised recipient transcript.tail tr → (keyLabelMyTurn me recipient transcript.tail).isCorrupt tr := by
    unfold keyLabelMyTurn
    split
    · grind
    · grind
    simp [stateLabel]
    grind
  unfold keyLabelOtherTurn
  split
  · grind
  · grind
  simp [stateLabel]
  grind

theorem keyLabelMyTurn_isCorrupt_implies_lemma
  (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
  : (keyLabelOtherTurn me recipient transcript).isCorrupt tr →
    ¬ (labelBeforeEvent (ltkLabel recipient) me recipient transcript.tail).isCorrupt tr →
    (
      transcript.length ≤ 1 ∨
      StateCompromised me transcript tr ∨
      StateCompromised recipient transcript tr ∨
      StateCompromised recipient transcript.tail tr
    )
:= by
  conv =>
    lhs
    rewrite [keyLabelOtherTurn_isCorrupt_eq]
  grind

theorem keyLabelMyTurn_isCorrupt_implies
  (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
  : (keyLabelMyTurn me recipient transcript).isCorrupt tr → (
      (
        transcript.length ≤ 1 ∨
        StateCompromised me transcript tr ∨
        StateCompromised me transcript.tail tr ∨
        StateCompromised recipient transcript tr
      ) ∨ (
        ∃ previousTranscript,
          previousTranscript <:+ transcript ∧
          1 ≤ previousTranscript.length ∧
          (previousTranscript.length % 2) = (transcript.length % 2) ∧
          (labelBeforeEvent (ltkLabel recipient) me recipient previousTranscript).isCorrupt tr ∧ (
            previousTranscript.length ≤ 2 ∨
            StateCompromised me previousTranscript tr ∨
            StateCompromised me previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail.tail tr
          )
      )
    )
:= by
  intro h_corrupt
  by_cases transcript.length ≤ 1
  · left; grind
  rewrite [keyLabelMyTurn_isCorrupt_eq] at h_corrupt
  by_cases ¬ (labelBeforeEvent (ltkLabel recipient) me recipient transcript).isCorrupt tr
  · left; grind
  cases h_corrupt
  · left; grind
  right
  rename_i h_corrupt
  obtain ⟨ h_key_corrupt, h_sig_corrupt ⟩ := h_corrupt
  by_cases (labelBeforeEvent (ltkLabel recipient) me recipient transcript.tail.tail).isCorrupt tr
  · rewrite [keyLabelOtherTurn_isCorrupt_eq] at h_key_corrupt
    cases h_key_corrupt
    · grind [List.tail_suffix]
    have := keyLabelMyTurn_isCorrupt_implies me recipient transcript.tail.tail tr (by grind)
    cases this
    · by_cases transcript.length ≤ 2
      · exists transcript
        grind
      -- in the following, `grind` does case splitting
      -- and chooses between `exists transcript` and `exists transcript.tail.tail`!
      grind [List.tail_suffix]
    rename_i h
    obtain ⟨ previousTranscript, _, _ ⟩ := h
    exists previousTranscript
    grind [List.tail_suffix]
  have := keyLabelMyTurn_isCorrupt_implies_lemma _ _ _ _ h_key_corrupt (by grind)
  exists transcript
  grind [List.tail_suffix]
termination_by transcript.length
decreasing_by grind [cases List]

theorem keyLabelOtherTurn_isCorrupt_implies
  (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace)
  : (keyLabelOtherTurn me recipient transcript).isCorrupt tr → (
      (
        transcript.length ≤ 1 ∨
        StateCompromised me transcript tr ∨
        StateCompromised recipient transcript tr ∨
        StateCompromised recipient transcript.tail tr
      ) ∨ (
        ∃ previousTranscript,
          previousTranscript <:+ transcript.tail ∧
          1 ≤ previousTranscript.length ∧
          (previousTranscript.length % 2) = (transcript.tail.length % 2) ∧
          (labelBeforeEvent (ltkLabel recipient) me recipient previousTranscript).isCorrupt tr ∧ (
            previousTranscript.length ≤ 2 ∨
            StateCompromised me previousTranscript tr ∨
            StateCompromised me previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail.tail tr
          )
      )
    )
:= by
  intro h_corrupt
  by_cases transcript.length ≤ 1
  · left; grind
  rewrite [keyLabelOtherTurn_isCorrupt_eq] at h_corrupt
  cases h_corrupt
  · left; grind
  rename_i h_corrupt
  obtain ⟨ h_key_corrupt, h_sig_corrupt ⟩ := h_corrupt
  have := keyLabelMyTurn_isCorrupt_implies _ _ _ _ h_key_corrupt
  cases this
  · grind [List.tail_suffix]
  right
  grind [List.tail_suffix]

theorem labelBeforeEvent_ltkLabel_isCorrupt_implies
  (me recipient: Participant) (transcript: Transcript)
  (tr: ExecTrace)
  : (∃ k, tr.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k)) →
    (labelBeforeEvent (ltkLabel recipient) me recipient transcript).isCorrupt tr →
    ∀ i k,
      tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript k) i →
      (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk (tr.prefix i))
:= by
  intro h_ev h_corrupt
  simp only [labelBeforeEvent, ltkLabel] at h_corrupt
  have ⟨ i', ev, ⟨ k', h_ev' ⟩, h_ev'_logged ⟩ := event_minimum_prefix (fun ev => ∃ k, ev = (RatchetEvent.ReceiveUpdate me recipient transcript k)) tr (by grind)
  intro i k h_ev
  obtain ⟨ trBefore, _ ⟩ := h_corrupt
  have := Trace.le_imp_prefix_eq trBefore tr (by grind)
  have: ¬ tr.prefix (i'+1) ≤ trBefore := by grind
  have := DY.Trace.EventLoggedAt_le' (RatchetEvent.ReceiveUpdate me recipient transcript k) i (tr.prefix (i+1)) tr
  have := fun h => h_ev'_logged.right.right (i+1) (RatchetEvent.ReceiveUpdate me recipient transcript k) h (by grind) (by grind)
  have: trBefore.length ≤ i' := by grind
  have: i' < i+1 := by grind
  have: trBefore ≤ tr.prefix i := by grind
  grind

theorem logged_receive_update_implies_logged_previous_transcript
  (me recipient: Participant) (transcript previousTranscript: Transcript) (tr: ProofTrace)
  : tr.Invariant →
    previousTranscript <:+ transcript →
    1 ≤ previousTranscript.length →
    (previousTranscript.length % 2) = (transcript.length % 2) →
    (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k)) →
    (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient previousTranscript k))
:= by
  intro h_inv h_suffix h_length1 h_length2
  have h_disj: (previousTranscript = transcript ∨ previousTranscript = transcript.tail) ∨ previousTranscript <:+ transcript.tail.tail := by
    obtain ⟨ pref, h_pref ⟩ := h_suffix
    grind
  cases h_disj
  · grind
  have: 3 ≤ transcript.length := by grind
  intro ⟨ k, h_ev ⟩
  apply logged_receive_update_implies_logged_previous_transcript me recipient transcript.tail.tail previousTranscript tr (by grind) (by grind) (by grind) (by grind [cases List])
  have ⟨ _, h_ev' ⟩: (∃ k, tr.erase.EventLogged (RatchetEvent.SendUpdate me recipient transcript.tail k)) := by
    have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_inv h_ev
    simp only [ProtocolEvent.EventInv.invariant] at h_ev_inv
    grind
  have ⟨ _, h_ev'' ⟩: (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript.tail.tail k)) := by
    have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_inv h_ev'
    simp only [ProtocolEvent.EventInv.invariant] at h_ev_inv
    grind
  grind


end LabelLemma

end DY.Example.Ratchet
