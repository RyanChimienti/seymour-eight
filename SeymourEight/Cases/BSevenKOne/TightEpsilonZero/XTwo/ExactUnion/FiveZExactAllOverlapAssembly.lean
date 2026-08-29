import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactSelectedBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactLabels

set_option linter.style.header false

/-!
# Assembly of the exact five-`Z` all-overlaps certificate

This is the graph-to-certificate integration point for a selected six-element
external union and any of the six possible intersections with `H`.
-/

namespace SeymourEight.FiveZExactAllOverlapAssembly

open FiveZExactRisk FiveZExactCoreBridge FiveZExactGraphBridge
  FiveZExactHBridge FiveZExactGlobalBridge FiveZExactSelectedBridge
  FiveZExactLabels BSevenKOneCounting Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev AllowedOverlap (overlap a1In : Nat) : Prop :=
  (overlap = 0 ∧ a1In = 0) ∨ (overlap = 1 ∧ a1In = 0) ∨
  (overlap = 2 ∧ a1In = 0) ∨ (overlap = 1 ∧ a1In = 1) ∨
  (overlap = 2 ∧ a1In = 1) ∨ (overlap = 3 ∧ a1In = 1)

private theorem overlapWToH_range_of_allowed (overlap a1In : Nat)
    (hAllowed : AllowedOverlap overlap a1In) (wi : Fin 6) :
    overlapWToH overlap a1In wi < 3 ∨
      overlapWToH overlap a1In wi = 3 := by
  rcases hAllowed with h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals simp only [overlapWToH]
  all_goals split_ifs <;> omega

private theorem mapped_index_of_h_selected (overlap a1In : Nat)
    (hAllowed : AllowedOverlap overlap a1In) (hi : Fin 3)
    (hSelected : overlapHInW overlap a1In hi = true) :
    ∃ wi : Fin 6, overlapWToH overlap a1In wi < 3 ∧
      overlapWToH overlap a1In wi = hi := by
  rcases hAllowed with h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  · simp [overlapHInW] at hSelected
    omega
  · have hhi : hi.val = 1 := by
      simp [overlapHInW] at hSelected
      omega
    refine ⟨0, by simp [overlapWToH], ?_⟩
    simp [overlapWToH]
    omega
  · have hhi : 1 ≤ hi.val ∧ hi.val ≤ 2 := by
      simp [overlapHInW] at hSelected
      omega
    refine ⟨⟨hi.val - 1, by omega⟩, ?_, ?_⟩
    · change (if hi.val - 1 < 2 then hi.val - 1 + 1 else 3) < 3
      rw [if_pos (by omega)]
      omega
    · change (if hi.val - 1 < 2 then hi.val - 1 + 1 else 3) = hi.val
      rw [if_pos (by omega)]
      omega
  · have hhi : hi.val = 0 := by
      simp [overlapHInW] at hSelected
      omega
    refine ⟨0, by simp [overlapWToH], ?_⟩
    simp [overlapWToH]
    omega
  · have hhi : hi.val ≤ 1 := by
      simp [overlapHInW] at hSelected
      omega
    refine ⟨⟨hi.val, by omega⟩, ?_, ?_⟩
    · simp only [overlapWToH]
      split_ifs <;> omega
    · simp only [overlapWToH]
      split_ifs <;> omega
  · refine ⟨⟨hi.val, by omega⟩, ?_, ?_⟩
    · simp [overlapWToH]
    · simp [overlapWToH]

private theorem outside_of_overlap_labels (C : G.LocalConfiguration)
    (S : Finset V) (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (overlap a1In : Nat)
    (hAllowed : AllowedOverlap overlap a1In)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S) :
    ∀ wi : Fin 6,
      overlapWToH overlap a1In wi = 3 → (w wi).1 ∉ C.H := by
  intro wi hwi hwH
  obtain ⟨hi, hhi⟩ := h.surjective ⟨(w wi).1, hwH⟩
  have hhiVal : (h hi).1 = (w wi).1 := congrArg Subtype.val hhi
  have hSelected : overlapHInW overlap a1In hi = true :=
    (hHSelected hi).2 (by rw [hhiVal]; exact (w wi).2)
  obtain ⟨wi', hwi'Mapped, hwi'hi⟩ :=
    mapped_index_of_h_selected overlap a1In hAllowed hi hSelected
  have hww : (w wi').1 = (w wi).1 := by
    rw [hMapped wi' hwi'Mapped]
    have hFin : (⟨overlapWToH overlap a1In wi', hwi'Mapped⟩ : Fin 3) = hi := by
      apply Fin.ext
      exact hwi'hi
    rw [hFin, hhiVal]
  have : wi' = wi := by
    apply w.injective
    apply Subtype.ext
    exact hww
  subst wi'
  omega

private theorem fin_three_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  omega

private theorem exists_w_for_overlap (C : G.LocalConfiguration)
    (S : Finset V) (hSCard : S.card = 6)
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (overlap a1In : Nat)
    (hAllowed : AllowedOverlap overlap a1In)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S) :
    ∃ w : Fin 6 ≃ {v : V // v ∈ S},
      ∀ (wi : Fin 6) (hm : overlapWToH overlap a1In wi < 3),
        (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1 := by
  classical
  rcases hAllowed with h00 | h10 | h20 | h11 | h21 | h31
  · rcases h00 with ⟨rfl, rfl⟩
    let w := finsetEquivFin S hSCard
    refine ⟨w, ?_⟩
    intro wi hm
    simp [overlapWToH] at hm
  · rcases h10 with ⟨rfl, rfl⟩
    have hh1 : (h 1).1 ∈ S := (hHSelected 1).1 (by decide)
    let w := finsetEquivFinAtZero S (by omega) hSCard (h 1).1 hh1
    refine ⟨w, ?_⟩
    intro wi hm
    have hwi : wi = 0 := by
      apply Fin.ext
      simp only [overlapWToH] at hm
      split_ifs at hm <;> omega
    subst wi
    simpa [w, overlapWToH] using
      finsetEquivFinAtZero_zero S (by omega) hSCard (h 1).1 hh1
  · rcases h20 with ⟨rfl, rfl⟩
    have hh1 : (h 1).1 ∈ S := (hHSelected 1).1 (by decide)
    have hh2 : (h 2).1 ∈ S := (hHSelected 2).1 (by decide)
    have hne : (h 1).1 ≠ (h 2).1 := by
      intro heq
      have : (1 : Fin 3) = 2 := by
        apply h.injective
        apply Subtype.ext
        exact heq
      omega
    let w := finsetEquivFinAtZeroOne S (by omega) hSCard
      (h 1).1 hh1 (h 2).1 hh2 hne
    refine ⟨w, ?_⟩
    intro wi hm
    have hwi : wi = 0 ∨ wi = 1 := by
      simp only [overlapWToH] at hm
      split_ifs at hm <;> omega
    rcases hwi with rfl | rfl
    · simp [w, overlapWToH]
    · simpa [w, overlapWToH] using
        finsetEquivFinAtZeroOne_one S (by omega) hSCard
          (h 1).1 hh1 (h 2).1 hh2 hne
  · rcases h11 with ⟨rfl, rfl⟩
    have hh0 : (h 0).1 ∈ S := (hHSelected 0).1 (by decide)
    let w := finsetEquivFinAtZero S (by omega) hSCard (h 0).1 hh0
    refine ⟨w, ?_⟩
    intro wi hm
    have hwi : wi = 0 := by
      apply Fin.ext
      simp only [overlapWToH] at hm
      split_ifs at hm <;> omega
    subst wi
    simpa [w, overlapWToH] using
      finsetEquivFinAtZero_zero S (by omega) hSCard (h 0).1 hh0
  · rcases h21 with ⟨rfl, rfl⟩
    have hh0 : (h 0).1 ∈ S := (hHSelected 0).1 (by decide)
    have hh1 : (h 1).1 ∈ S := (hHSelected 1).1 (by decide)
    have hne : (h 0).1 ≠ (h 1).1 := by
      intro heq
      have : (0 : Fin 3) = 1 := by
        apply h.injective
        apply Subtype.ext
        exact heq
      omega
    let w := finsetEquivFinAtZeroOne S (by omega) hSCard
      (h 0).1 hh0 (h 1).1 hh1 hne
    refine ⟨w, ?_⟩
    intro wi hm
    have hwi : wi = 0 ∨ wi = 1 := by
      simp only [overlapWToH] at hm
      split_ifs at hm <;> omega
    rcases hwi with rfl | rfl
    · simp [w, overlapWToH]
    · simpa [w, overlapWToH] using
        finsetEquivFinAtZeroOne_one S (by omega) hSCard
          (h 0).1 hh0 (h 1).1 hh1 hne
  · rcases h31 with ⟨rfl, rfl⟩
    have hh0 : (h 0).1 ∈ S := (hHSelected 0).1 (by decide)
    have hh1 : (h 1).1 ∈ S := (hHSelected 1).1 (by decide)
    have hh2 : (h 2).1 ∈ S := (hHSelected 2).1 (by decide)
    have hne01 : (h 0).1 ≠ (h 1).1 := by
      intro heq
      have : (0 : Fin 3) = 1 := h.injective (Subtype.ext heq)
      omega
    have hne02 : (h 0).1 ≠ (h 2).1 := by
      intro heq
      have : (0 : Fin 3) = 2 := h.injective (Subtype.ext heq)
      omega
    have hne12 : (h 1).1 ≠ (h 2).1 := by
      intro heq
      have : (1 : Fin 3) = 2 := h.injective (Subtype.ext heq)
      omega
    let w := finsetEquivFinAtZeroOneTwo S (by omega) hSCard
      (h 0).1 hh0 (h 1).1 hh1 (h 2).1 hh2 hne01 hne02 hne12
    refine ⟨w, ?_⟩
    intro wi hm
    have hwi : wi = 0 ∨ wi = 1 ∨ wi = 2 := by
      simp only [overlapWToH] at hm
      split_ifs at hm <;> omega
    rcases hwi with rfl | rfl | rfl
    · simp [w, overlapWToH]
    · simp [w, overlapWToH]
    · simpa [w, overlapWToH] using
        finsetEquivFinAtZeroOneTwo_two S (by omega) hSCard
          (h 0).1 hh0 (h 1).1 hh1 (h 2).1 hh2 hne01 hne02 hne12

private theorem exists_compatible_overlap_labels (C : G.LocalConfiguration)
    (S : Finset V) (hSCard : S.card = 6)
    (hHCard : C.H.card = 3) (hA1Card : C.A1.card = 1)
    (hXCard : C.X.card = 2) :
    ∃ (overlap a1In : Nat) (w : Fin 6 ≃ {v : V // v ∈ S})
        (h : Fin 3 ≃ {v : V // v ∈ C.H}),
      AllowedOverlap overlap a1In ∧
      (∀ (wi : Fin 6) (hm : overlapWToH overlap a1In wi < 3),
        (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1) ∧
      (∀ hi : Fin 3,
        overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S) ∧
      (h 0).1 ∈ C.A1 ∧ (h 1).1 ∈ C.X ∧ (h 2).1 ∈ C.X := by
  classical
  let eA1 : Fin 1 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  have package (overlap a1In : Nat) (h : Fin 3 ≃ {v : V // v ∈ C.H})
      (hAllowed : AllowedOverlap overlap a1In)
      (hSelected : ∀ hi : Fin 3,
        overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
      (hh0 : (h 0).1 ∈ C.A1) (hh1 : (h 1).1 ∈ C.X)
      (hh2 : (h 2).1 ∈ C.X) :
      ∃ (overlap a1In : Nat) (w : Fin 6 ≃ {v : V // v ∈ S})
          (h : Fin 3 ≃ {v : V // v ∈ C.H}),
        AllowedOverlap overlap a1In ∧
        (∀ (wi : Fin 6) (hm : overlapWToH overlap a1In wi < 3),
          (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1) ∧
        (∀ hi : Fin 3,
          overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S) ∧
        (h 0).1 ∈ C.A1 ∧ (h 1).1 ∈ C.X ∧ (h 2).1 ∈ C.X := by
    obtain ⟨w, hMapped⟩ :=
      exists_w_for_overlap G C S hSCard h overlap a1In hAllowed hSelected
    exact ⟨overlap, a1In, w, h, hAllowed, hMapped, hSelected,
      hh0, hh1, hh2⟩
  by_cases hs0 : (eA1 0).1 ∈ S
  · by_cases hs1 : (eX 0).1 ∈ S
    · by_cases hs2 : (eX 1).1 ∈ S
      · let h := hLabelEquiv G C hHCard eA1 eX
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX]
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX]
          exact (eX 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX]
          exact (eX 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 3 1 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, hs0, hs1, hs2]
        exact package 3 1 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
      · let h := hLabelEquiv G C hHCard eA1 eX
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX]
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX]
          exact (eX 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX]
          exact (eX 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 2 1 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, hs0, hs1, hs2]
        exact package 2 1 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
    · by_cases hs2 : (eX 1).1 ∈ S
      · let eX' : Fin 2 ≃ {v : V // v ∈ C.X} := (Equiv.swap 0 1).trans eX
        let h := hLabelEquiv G C hHCard eA1 eX'
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX']
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX']
          exact (eX' 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX']
          exact (eX' 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 2 1 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, eX', hs0, hs1, hs2]
        exact package 2 1 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
      · let h := hLabelEquiv G C hHCard eA1 eX
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX]
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX]
          exact (eX 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX]
          exact (eX 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 1 1 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, hs0, hs1, hs2]
        exact package 1 1 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
  · by_cases hs1 : (eX 0).1 ∈ S
    · by_cases hs2 : (eX 1).1 ∈ S
      · let h := hLabelEquiv G C hHCard eA1 eX
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX]
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX]
          exact (eX 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX]
          exact (eX 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 2 0 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, hs0, hs1, hs2]
        exact package 2 0 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
      · let h := hLabelEquiv G C hHCard eA1 eX
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX]
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX]
          exact (eX 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX]
          exact (eX 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 1 0 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, hs0, hs1, hs2]
        exact package 1 0 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
    · by_cases hs2 : (eX 1).1 ∈ S
      · let eX' : Fin 2 ≃ {v : V // v ∈ C.X} := (Equiv.swap 0 1).trans eX
        let h := hLabelEquiv G C hHCard eA1 eX'
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX']
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX']
          exact (eX' 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX']
          exact (eX' 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 1 0 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, eX', hs0, hs1, hs2]
        exact package 1 0 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2
      · let h := hLabelEquiv G C hHCard eA1 eX
        have hh0 : (h 0).1 ∈ C.A1 := by
          rw [hLabelEquiv_zero G C hHCard eA1 eX]
          exact (eA1 0).2
        have hh1 : (h 1).1 ∈ C.X := by
          rw [hLabelEquiv_one G C hHCard eA1 eX]
          exact (eX 0).2
        have hh2 : (h 2).1 ∈ C.X := by
          rw [hLabelEquiv_two G C hHCard eA1 eX]
          exact (eX 1).2
        have hSelected : ∀ hi : Fin 3,
            overlapHInW 0 0 hi = true ↔ (h hi).1 ∈ S := by
          intro hi
          rcases fin_three_cases hi with rfl | rfl | rfl
          all_goals simp [overlapHInW, h, hs0, hs1, hs2]
        exact package 0 0 h (by simp [AllowedOverlap]) hSelected hh0 hh1 hh2

theorem impossible_of_selectedCompatibleLabels (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 2)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (hPZ : 32 ≤ edgeCount G C.P C.Z)
    (S : Finset V) (hS : S ⊆ zExternalUnion G C) (hSCard : S.card = 6)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7)
    (hRetains : zExternalUnion G C ∩ C.H ⊆ S)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (overlap a1In : Nat)
    (hAllowed :
      (overlap = 0 ∧ a1In = 0) ∨ (overlap = 1 ∧ a1In = 0) ∨
      (overlap = 2 ∧ a1In = 0) ∨ (overlap = 1 ∧ a1In = 1) ∨
      (overlap = 2 ∧ a1In = 1) ∨ (overlap = 3 ∧ a1In = 1))
    (hRange : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi < 3 ∨
        overlapWToH overlap a1In wi = 3)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hOutside : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi = 3 → (w wi).1 ∉ C.H)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hAR : ∀ q : Nat, (hq : q < 4) → (a ⟨q + 4, by omega⟩).1 ∈ C.R) :
    False := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) (fun j ↦ (a j).1)
  have hSquares := orientedSquare_coreBits_true G.Adj hG.1
    (fun u v huv ↦ hG.2 huv) (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) (fun j ↦ (a j).1)
  have hCross := orientedCross_coreBits_true G.Adj
    (fun u v huv ↦ hG.2 huv) (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) (fun j ↦ (a j).1)
  have hHTotalNat := totalHToP_coreBits_toNat G C p h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) (fun j ↦ (a j).1)
  have hHTotalLower : 11 ≤ edgeCount G C.H C.P := by
    have hCount := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    simpa only [hx, Nat.choose] using hCount
  have hHTotal : (11 : BitVec 8).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHTotalNat]
    exact hHTotalLower
  have hMissingNat := totalMissingPZ_coreBits_toNat_add_edges G C p z
    (fun j ↦ (h j).1) (fun j ↦ (w j).1) (fun j ↦ (a j).1)
  change (totalMissingPZ bits).toNat + edgeCount G C.P C.Z = 35 at hMissingNat
  have hMissing : (totalMissingPZ bits).ule 3 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    change (totalMissingPZ bits).toNat ≤ 3
    omega
  have hHPositive := hPOut_positive_coreBits_true G C hG hPB hMin p
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) h (fun j ↦ (a j).1)
    (by simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree)
  have hFixedA := fixedAStructure_coreBits_true G C hG hPivot hk hMin hPB p
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) h a hA0 hAH
    hH0A1 hH1X hH2X hAR
  have hWCoverage := selectedWCoverage_coreBits_true G C S hS p z w
    (fun j ↦ (h j).1) (fun j ↦ (a j).1)
  have hZDegrees : all 5 (fun zi =>
      (7 : BitVec 8).ule (zDegree bits zi)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    exact zDegree_selected_ge_seven G C S hS hSCard hWCard p z w
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) hMin i hi
  have hZRows : all 5 (fun zi =>
      zNonSeymourOverlap overlap a1In bits zi) = true := by
    rw [all_eq_true_iff]
    intro i hi
    exact zNonSeymourOverlap_coreBits_true G C S hS hSCard hWCard hRetains
      p z w h (fun j ↦ (a j).1) overlap a1In hMapped hHSelected
      hNoSeymour i hi
  have hHRows : all 3 (hNonSeymour bits) = true := by
    rw [all_eq_true_iff]
    intro i hi
    have hRow := hRow_coreBits_true G C hG hPB p z
      (fun j ↦ (w j).1) h a hA0 hAH hMin hNoSeymour i hi
    rw [Bool.and_eq_true] at hRow
    exact hRow.2
  have hPRows : all 7 (fun pi =>
      pNonSeymourOverlap overlap a1In bits pi) = true := by
    rw [all_eq_true_iff]
    intro i hi
    exact pNonSeymourOverlap_coreBits_true G C S hS hG hPB hEpsilon
      p z w h (fun j ↦ (a j).1) overlap a1In hRange hMapped hOutside
      hHSelected hNoSeymour i hi
  have hOverlapRows : overlapRows overlap a1In bits = true := by
    simp only [overlapRows, Bool.and_eq_true]
    exact ⟨hZRows, hPRows⟩
  have hAnyRows : anyOverlapRows bits = true := by
    rcases hAllowed with h00 | h10 | h20 | h11 | h21 | h31
    all_goals rcases ‹_ ∧ _› with ⟨rfl, rfl⟩
    all_goals simp [anyOverlapRows, hOverlapRows]
  have hCore : familyCoreAnyOverlap bits = true := by
    rw [familyCoreAnyOverlap]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSquares.1, hCross.1⟩, hCross.2⟩,
      hSquares.2.1⟩, hHTotal⟩, hMissing⟩, hHPositive⟩, hFixedA⟩,
      hWCoverage⟩, hZDegrees⟩, hHRows⟩, hAnyRows⟩
  exact impossible_of_encodedAllOverlaps G.Adj
    (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1) (fun j ↦ (a j).1) hCore

/-- Exact cardinalities alone supply a retained six-set and all compatible
labels; no separate hypothesis about the intersection with `H` is needed. -/
theorem impossible_of_exactCards (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 2)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (hPZ : 32 ≤ edgeCount G C.P C.Z)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7)
    (hHCard : C.H.card = 3) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 1) (hXCard : C.X.card = 2)
    (hRCard : C.R.card = 4) : False := by
  classical
  obtain ⟨S, hS, hSCard, hRetains⟩ :=
    exists_six_subset_containing_inter (zExternalUnion G C) C.H
      hWCard hHCard
  obtain ⟨overlap, a1In, w, h, hAllowed, hMapped, hHSelected,
      hH0A1, hH1X, hH2X⟩ :=
    exists_compatible_overlap_labels G C S hSCard hHCard hA1Card hXCard
  have hRange : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi < 3 ∨
        overlapWToH overlap a1In wi = 3 :=
    overlapWToH_range_of_allowed overlap a1In hAllowed
  have hOutside : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi = 3 → (w wi).1 ∉ C.H :=
    outside_of_overlap_labels G C S w h overlap a1In hAllowed
      hMapped hHSelected
  let p : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let z : Fin 5 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let eR : Fin 4 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a : Fin 8 ≃ {v : V // v ∈ C.A} :=
    aLabelEquiv G C hACard h eR
  have hA0 : (a 0).1 = C.a1 := aLabelEquiv_zero G C hACard h eR
  have hAH : ∀ j : Fin 3,
      (a ⟨j + 1, by omega⟩).1 = (h j).1 := by
    intro j
    exact aLabelEquiv_h G C hACard h eR j
  have hAR : ∀ q : Nat, (hq : q < 4) →
      (a ⟨q + 4, by omega⟩).1 ∈ C.R := by
    intro q hq
    rw [aLabelEquiv_r G C hACard h eR ⟨q, hq⟩]
    exact (eR ⟨q, hq⟩).2
  exact impossible_of_selectedCompatibleLabels G C hG hPivot hMin
    hNoSeymour hRootDegree hk hx hPB hEpsilon hPZ S hS hSCard hWCard
    hRetains p z w h a overlap a1In hAllowed hRange hMapped hOutside
    hHSelected hA0 hAH hH0A1 hH1X hH2X hAR

/-- Graph-level contradiction for the exact five-`Z` branch whenever the
external union has size six or seven, uniformly over all intersections with
`H`. -/
theorem impossible_exactFiveZ_unionSixOrSeven (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 2) (hz : C.z = 5)
    (hEpsilon : epsilonS G C = 0)
    (hPZ : 32 ≤ edgeCount G C.P C.Z)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7) : False := by
  have hPB := SeymourEight.BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 5 := by
    change C.Z.card = 5 at hz
    exact hz
  have hHCard : C.H.card = 3 := by
    change C.h = 3
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 1 := by
    change C.A1.card = 1 at hk
    exact hk
  have hXCard : C.X.card = 2 := by
    change C.X.card = 2 at hx
    exact hx
  have hRCard : C.R.card = 4 := by
    have hXR := x_add_card_R_eq_six G C hG hRootDegree hk
    change C.X.card = 2 at hx
    change C.X.card + C.R.card = 6 at hXR
    omega
  exact impossible_of_exactCards G C hG hPivot hMin hNoSeymour
    hRootDegree hk hx hPB hEpsilon hPZ hPCard hZCard hWCard hHCard
    hACard hA1Card hXCard hRCard

/-- Defect-parameter form of `impossible_exactFiveZ_unionSixOrSeven`. -/
theorem impossible_exactFiveZ_unionSixOrSeven_of_missing
    (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 2) (hz : C.z = 5)
    (hEpsilon : epsilonS G C = 0)
    (hMissing : 35 - edgeCount G C.P C.Z ≤ 3)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7) : False := by
  have hPB := SeymourEight.BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 5 := by
    change C.Z.card = 5 at hz
    exact hz
  have hPZ := thirtyTwo_le_PZ_of_missing_le_three
    G C hPCard hZCard hMissing
  exact impossible_exactFiveZ_unionSixOrSeven G C hG hPivot hMin
    hNoSeymour hRootDegree hBCard hk hx hz hEpsilon hPZ hWCard

end SeymourEight.FiveZExactAllOverlapAssembly
