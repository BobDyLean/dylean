module

import DY.Meta
import DY.Meta.Utils
public import Examples.Ratchet.Specification
public import Examples.Ratchet.Proof
import all Examples.Ratchet.Proof
public import Examples.Ratchet.Instance

namespace DY.Example.Ratchet

public
theorem authentication
  (me recipient: Participant)
  (transcript: Transcript) (k: Bytes)
  (time: Nat)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript k) time →
    (
      let trBefore := tr.prefix time
      trBefore.EventLogged (RatchetEvent.SendUpdate recipient me transcript k) ∨
      (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk trBefore)
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant] at this
  grind

/--
info: 'DY.Example.Ratchet.authentication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms authentication

mutual

public
def ReceiveUpdateKeyCompromiseScenario (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace): Prop :=
  (
    transcript.length ≤ 1 ∨
    StateCompromised me transcript tr ∨
    StateCompromised me transcript.tail tr ∨
    StateCompromised recipient transcript tr
  ) ∨ (
    (∃ k i, tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript k) i) ∧
    (∀ k i,
      tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript k) i →
      (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk (tr.prefix i))
    ) ∧
    ∃ _: 1 ≤ transcript.length,
    SendUpdateKeyCompromiseScenario me recipient transcript.tail tr
  )

public
def SendUpdateKeyCompromiseScenario (me recipient: Participant) (transcript: Transcript) (tr: ExecTrace): Prop :=
  (
    transcript.length ≤ 1 ∨
    StateCompromised me transcript tr ∨
    StateCompromised recipient transcript tr ∨
    StateCompromised recipient transcript.tail tr
  ) ∨ (
    (∃ k i, tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript.tail k) i) ∧
    (∀ k i,
      tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript.tail k) i →
      (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk (tr.prefix i))
    ) ∧
    ∃ _: 1 ≤ transcript.length,
    ReceiveUpdateKeyCompromiseScenario me recipient transcript.tail tr
  )

end

section Lemmas

mutual

theorem ReceiveUpdateKeyCompromiseScenario_lemma
  (me recipient: Participant) (transcript: Transcript) (tr: ProofTrace)
  : tr.Invariant →
    (∃ k i, tr.erase.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient transcript k) i) →
    (keyLabelMyTurn me recipient transcript).isCorrupt tr.erase →
    ReceiveUpdateKeyCompromiseScenario me recipient transcript tr.erase
:= by
  intro h_inv h_ev h_corrupt
  unfold ReceiveUpdateKeyCompromiseScenario
  by_cases transcript.length ≤ 1
  · grind
  rewrite [keyLabelMyTurn_isCorrupt_eq] at h_corrupt
  cases h_corrupt
  · left; grind
  right
  rename_i h_corrupt
  obtain ⟨ h_key_corrupt, h_sig_corrupt ⟩ := h_corrupt
  repeat' apply And.intro
  · grind
  · have := labelBeforeEvent_ltkLabel_isCorrupt_implies me recipient transcript tr.erase (by grind) (by grind)
    grind
  · refine ⟨ by grind, ?_ ⟩
    apply SendUpdateKeyCompromiseScenario_lemma me recipient transcript.tail tr
    · exact h_inv
    · obtain ⟨ k, i, h_ev ⟩ := h_ev
      have h_ev_inv := Trace.EventLoggedAt_imp_EventInv _ _ _ h_inv h_ev
      simp only [ProtocolEvent.EventInv.invariant] at h_ev_inv
      grind
    · grind

theorem SendUpdateKeyCompromiseScenario_lemma
  (me recipient: Participant) (transcript: Transcript) (tr: ProofTrace)
  : tr.Invariant →
    (∃ k i, tr.erase.EventLoggedAt (RatchetEvent.SendUpdate me recipient transcript k) i) →
    (keyLabelOtherTurn me recipient transcript).isCorrupt tr.erase →
    SendUpdateKeyCompromiseScenario me recipient transcript tr.erase
:= by
  intro h_inv h_ev h_corrupt
  unfold SendUpdateKeyCompromiseScenario
  by_cases transcript.length ≤ 1
  · grind
  rewrite [keyLabelOtherTurn_isCorrupt_eq] at h_corrupt
  cases h_corrupt
  · left; grind
  right
  rename_i h_corrupt
  obtain ⟨ h_key_corrupt, h_sig_corrupt ⟩ := h_corrupt
  have: ∃ k i, Trace.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient (List.tail transcript) k) i (Trace.erase tr) := by
    obtain ⟨ k, i, h_ev ⟩ := h_ev
    have h_ev_inv := Trace.EventLoggedAt_imp_EventInv _ _ _ h_inv h_ev
    simp only [ProtocolEvent.EventInv.invariant] at h_ev_inv
    grind
  repeat' apply And.intro
  · grind
  · have := labelBeforeEvent_ltkLabel_isCorrupt_implies me recipient transcript.tail tr.erase (by grind) (by grind)
    grind
  · refine ⟨ by grind, ?_ ⟩
    apply ReceiveUpdateKeyCompromiseScenario_lemma me recipient transcript.tail tr
    · exact h_inv
    · grind
    · grind

end

end Lemmas

public
theorem secrecy_receiveUpdate_recursive
  (me recipient: Participant)
  (transcript: Transcript) (k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k)  →
    ReceiveUpdateKeyCompromiseScenario me recipient transcript tr
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  by_cases transcript.length ≤ 1
  · unfold ReceiveUpdateKeyCompromiseScenario
    grind
  have h_corrupt: (keyLabelMyTurn me recipient transcript).isCorrupt tr.erase := by
    have := eventLogged_receiveUpdate_key_label me recipient transcript k tr (by grind) (by grind) (by grind)
    grind [Label.canFlow]
  have := ReceiveUpdateKeyCompromiseScenario_lemma me recipient transcript tr h_trinv (by grind)
  grind

/--
info: 'DY.Example.Ratchet.secrecy_receiveUpdate_recursive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms secrecy_receiveUpdate_recursive

public
theorem secrecy_sendUpdate_recursive
  (me recipient: Participant)
  (transcript: Transcript) (k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLogged (RatchetEvent.SendUpdate me recipient transcript k)  →
    SendUpdateKeyCompromiseScenario me recipient transcript tr
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  by_cases transcript.length ≤ 1
  · unfold SendUpdateKeyCompromiseScenario
    grind
  have h_corrupt: (keyLabelOtherTurn me recipient transcript).isCorrupt tr.erase := by
    have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_trinv h_ev
    simp [ProtocolEvent.EventInv.invariant] at h_ev_inv
    grind [Label.canFlow]
  have := SendUpdateKeyCompromiseScenario_lemma me recipient transcript tr h_trinv (by grind)
  grind

/--
info: 'DY.Example.Ratchet.secrecy_sendUpdate_recursive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms secrecy_sendUpdate_recursive

public
theorem secrecy_receiveUpdate_unfolded
  (me recipient: Participant)
  (transcript: Transcript) (k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript k)  →
    (
      (
        transcript.length ≤ 1 ∨
        StateCompromised me transcript tr ∨
        StateCompromised me transcript.tail tr ∨
        StateCompromised recipient transcript tr
      ) ∨ (
        ∃ previousTranscript i k,
          previousTranscript <:+ transcript ∧
          tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient previousTranscript k) i ∧
          (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk (tr.prefix i)) ∧ (
            previousTranscript.length ≤ 2 ∨
            StateCompromised me previousTranscript tr ∨
            StateCompromised me previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail.tail tr
          )
      )
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  by_cases transcript.length ≤ 1
  · grind
  have := eventLogged_receiveUpdate_key_label me recipient transcript k tr (by grind) (by grind) (by grind)
  have h_corrupt: (keyLabelMyTurn me recipient transcript).isCorrupt tr.erase := by grind [Label.canFlow]
  have h_almost_theorem := keyLabelMyTurn_isCorrupt_implies _ _ _ _ h_corrupt
  cases h_almost_theorem
  · left; grind
  rename_i h_almost_theorem
  right
  obtain ⟨ previousTranscript, _ ⟩ := h_almost_theorem
  exists previousTranscript
  have := logged_receive_update_implies_logged_previous_transcript me recipient transcript previousTranscript tr (by grind) (by grind) (by grind) (by grind) (by grind)
  have := labelBeforeEvent_ltkLabel_isCorrupt_implies me recipient previousTranscript tr.erase (by grind) (by grind)
  grind

/--
info: 'DY.Example.Ratchet.secrecy_receiveUpdate_unfolded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms secrecy_receiveUpdate_unfolded

public
theorem secrecy_sendUpdate_unfolded
  (me recipient: Participant)
  (transcript: Transcript) (k: Bytes)
  : ∀ tr: ExecTrace,
    tr.Reachable reachability →
    k.AttackerKnows tr →
    tr.EventLogged (RatchetEvent.SendUpdate me recipient transcript k)  →
    (
      (
        transcript.length ≤ 1 ∨
        StateCompromised me transcript tr ∨
        StateCompromised recipient transcript tr ∨
        StateCompromised recipient transcript.tail tr
      ) ∨ (
        ∃ previousTranscript i k,
          previousTranscript <:+ transcript ∧
          tr.EventLoggedAt (RatchetEvent.ReceiveUpdate me recipient previousTranscript k) i ∧
          (∃ spk, LongTermKeys.LongTermKeyCompromised "Ratchet PKI" recipient spk (tr.prefix i)) ∧ (
            previousTranscript.length ≤ 2 ∨
            StateCompromised me previousTranscript tr ∨
            StateCompromised me previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail tr ∨
            StateCompromised recipient previousTranscript.tail.tail tr
          )
      )
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  by_cases transcript.length ≤ 1
  · grind
  have h_corrupt: (keyLabelOtherTurn me recipient transcript).isCorrupt tr.erase := by
    have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_trinv h_ev
    simp [ProtocolEvent.EventInv.invariant] at h_ev_inv
    grind [Label.canFlow]
  have h_ev_tail: (∃ k, tr.erase.EventLogged (RatchetEvent.ReceiveUpdate me recipient transcript.tail k)) := by
    have h_ev_inv := Trace.EventLogged_imp_EventInv _ _ h_trinv h_ev
    simp [ProtocolEvent.EventInv.invariant] at h_ev_inv
    grind
  have h_almost_theorem := keyLabelOtherTurn_isCorrupt_implies _ _ _ _ h_corrupt
  cases h_almost_theorem
  · left; grind
  rename_i h_almost_theorem
  right
  obtain ⟨ previousTranscript, _ ⟩ := h_almost_theorem
  exists previousTranscript
  have := logged_receive_update_implies_logged_previous_transcript me recipient transcript.tail previousTranscript tr (by grind) (by grind) (by grind) (by grind) (by grind)
  have := labelBeforeEvent_ltkLabel_isCorrupt_implies me recipient previousTranscript tr.erase (by grind) (by grind)
  grind [List.tail_suffix]

/--
info: 'DY.Example.Ratchet.secrecy_sendUpdate_unfolded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms secrecy_sendUpdate_unfolded

end DY.Example.Ratchet
