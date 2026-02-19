/-
  This module allows to modularly prove the attacker knowledge theorem:
  this is a key theorem in the DyLean methodology,
  saying for traces that satisfy the trace invariant,
  if the attacker knows a `Bytes`,
  then this `Bytes` must be publishable.
-/

module

public import DY.Bytes.Basic
public import DY.Bytes.Invariants
public import DY.Bytes.AttackerKnowledge
public import DY.Trace


namespace DY

variable [BytesFunctor]
variable [TraceInvariant]
variable [BytesInvariants]

public
class SubAttackerKnowledgeTheorem {SubF: Type → Type} (att: SubAttackerKnowledge SubF) where
  pf: ∀ b: Bytes, ∀ tr: ProofTrace, tr.Invariant → att.pred (·.Publishable tr) b → b.Publishable tr

public
class AttackerKnowledgeTheorem [AttackerKnowledge] where
  inst: SubAttackerKnowledgeTheorem (AttackerKnowledge.attackerKnowledge)

section AttackerKnowledgeTheorem

public
instance
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  [pfs: ∀ id, SubAttackerKnowledgeTheorem (atts id)]
  : SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' atts)
where
  pf := by
    intro b tr h_tr
    apply SubAttackerKnowledge.combine'.implies
    intro id b
    exact (pfs id).pf b tr h_tr

public
instance
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: ∀ id, SubAttackerKnowledge (SubFs id))
  [pfs: ∀ id, SubAttackerKnowledgeTheorem (atts id)]
  : SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine atts)
where
  pf := by
    intro b tr h_tr
    apply SubAttackerKnowledge.combine.implies
    intro id b
    exact (pfs id).pf b tr h_tr

end AttackerKnowledgeTheorem

public
axiom Bytes.MessageSent_implies_Publishable (b: Bytes) (tr: ProofTrace): tr.Invariant → tr.MessageSent b → b.Publishable tr

public
theorem Bytes.AttackerKnows_implies_Publishable
  [AttackerKnowledge]
  [inst: AttackerKnowledgeTheorem]
  (b: Bytes) (tr: ProofTrace)
  : tr.Invariant →
    Bytes.AttackerKnows b tr →
    b.Publishable tr
:= by
  intro h_tr
  apply Bytes.AttackerKnows.is_least_fixpoint (·.Publishable tr) b tr
  · intro b
    exact inst.inst.pf b tr h_tr
  · intro b
    exact Bytes.MessageSent_implies_Publishable b tr h_tr

end DY
