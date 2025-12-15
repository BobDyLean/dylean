import DY.Kleene
import DY.Bytes.Type
import DY.Bytes.EquationalTheory
import DY.Trace.Type

namespace DY

def EquationalTheories.mapTheories [EquationalTheories] {α: Type u} (f: TheoryId → α): List α :=
  EquationalTheories.theories.mapFinIdx (fun id _ h_id =>
    f (Fin.mk id h_id)
  )

theorem EquationalTheories.mem_mapTheories
  {α: Type u}
  [EquationalTheories]
  (f: TheoryId → α)
  (x: α)
  :
  (x ∈ EquationalTheories.mapTheories f) ↔
  (exists id, f id = x)
  := by
    simp [mapTheories]
    constructor
    · intro ⟨ id, h_id, h⟩
      exists Fin.mk id h_id
    · intro ⟨ id, h_id ⟩
      exists id.val
      exists id.isLt

-- TODO: messages sent on network
def Bytes.AttackerKnows.pred [EquationalTheories] (tr: Trace α): Kleene.Set Bytes → Kleene.Set Bytes :=
  (Kleene.combine (EquationalTheories.mapTheories (fun id =>
    Kleene.combine (EquationalTheories.theories[id].attackerKnowledge.map AttackerKnowledge.pred)
  )))

theorem Bytes.AttackerKnows.pred_is_scott_continuous
  [EquationalTheories]
  (tr: Trace α)
  :
  Kleene.IsScottContinuous (Bytes.AttackerKnows.pred tr)
  := by
    unfold pred
    apply Kleene.combine_isScottContinuous
    simp only [EquationalTheories.mem_mapTheories, forall_exists_index]
    intros _ id h
    subst h
    apply Kleene.combine_isScottContinuous
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro attKnowledge h_attKnowledge
    exact attKnowledge.pred_scott_continuous

def Bytes.AttackerKnows [EquationalTheories] (b: Bytes) (tr: Trace α): Prop :=
  Kleene.mkWeakestFixpoint (Bytes.AttackerKnows.pred tr) b

theorem Bytes.AttackerKnows.prove
  [EquationalTheories]
  (theory: EquationalTheory)
  [inst: HasEquationalTheory theory]
  (att: AttackerKnowledge)
  (b: Bytes) (tr: Trace α)
  :
    att ∈ theory.attackerKnowledge →
    att.pred (Bytes.AttackerKnows · tr) b →
    Bytes.AttackerKnows b tr
  := by
    apply theory.into_theory_id
    generalize HasEquationalTheory.id theory = id
    clear inst
    unfold AttackerKnows
    intro h_att h_b
    rewrite [← Kleene.mkWeakestFixpoint_is_fixpoint (pred tr) (AttackerKnows.pred_is_scott_continuous tr)]
    unfold pred
    simp only [Kleene.combine]
    exists Kleene.combine (EquationalTheories.theories[id].attackerKnowledge.map AttackerKnowledge.pred)
    constructor
    · simp only [EquationalTheories.mapTheories, List.mem_mapFinIdx]
      exists id.val
      exists id.isLt
    simp only [Kleene.combine]
    exists att.pred
    grind

theorem Bytes.AttackerKnows.is_least_fixpoint
  [EquationalTheories]
  (pred: Bytes → Prop)
  (h_pred:
    ∀ (id: TheoryId) att out,
      att ∈ EquationalTheories.theories[id].attackerKnowledge →
      att.pred pred out →
      pred out
  )
  (b: Bytes) (tr: Trace α)
  :
    Bytes.AttackerKnows b tr →
    pred b
  :=
    Kleene.mkWeakestFixpoint_is_weakest (AttackerKnows.pred tr) (AttackerKnows.pred_is_scott_continuous tr) pred (by
      simp only [Subset, AttackerKnows.pred]
      intro b
      simp [Kleene.combine, EquationalTheories.mem_mapTheories]
      grind
    ) b

theorem Bytes.AttackerKnows.pred_trace_erase [EquationalTheories] (tr: Trace α):
  Bytes.AttackerKnows.pred tr = Bytes.AttackerKnows.pred (tr.erase)
  := by
    simp [Bytes.AttackerKnows.pred]

end DY
