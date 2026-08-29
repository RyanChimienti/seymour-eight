import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.HighDefect.Global
import SeymourEight.Reduction

set_option linter.style.header false

namespace SeymourEight.FiveZHighDefectGraphBridge

open FiveZHighDefect FiveZHighDefectBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZExactGlobalBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem filterCard_le_count {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, Q (e j).1 → b j = true) :
    (S.filter Q).card ≤ (count n b).toNat := by
  classical
  rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum n b hn,
    filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hQ : Q (e j).1
  · simp [hQ, hGood j hQ]
  · simp [hQ]

def deletionVertex (p : Fin 7 → V) (a : Fin 8 → V) (d : Nat) : V :=
  if hd : d = 0 then a 1
  else if hd8 : d < 8 then p ⟨d - 1, by omega⟩
  else p 0

omit [Fintype V] [DecidableEq V] in
theorem labelled_aOneNeighbor (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 5 → V) (d : Nat) (hd : d < 8) :
    labelledVertex a p z (aOneNeighbor d) = deletionVertex p a d := by
  classical
  by_cases hd0 : d = 0
  · subst d
    simp [aOneNeighbor, deletionVertex, labelledVertex]
  · have hdPos : 0 < d := by omega
    simp [aOneNeighbor, deletionVertex, hd0, hd, labelledVertex,
      show ¬d + 7 < 8 by omega, show d + 7 < 15 by omega,
      show d + 7 - 8 = d - 1 by omega]

theorem deletionVertex_injective (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A}) :
    Function.Injective (fun d : Fin 8 ↦
      deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d) := by
  let e := retainedLabelEquiv G C a p z
  intro d₁ d₂ heq
  have hLabelEq : labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
      (fun i ↦ (z i).1) (aOneNeighbor d₁) =
    labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
      (fun i ↦ (z i).1) (aOneNeighbor d₂) := by
    simpa [labelled_aOneNeighbor (fun i ↦ (p i).1)
      (fun i ↦ (a i).1) (fun i ↦ (z i).1)] using heq
  have hFin : (⟨aOneNeighbor d₁, by
        simp [aOneNeighbor]; split <;> omega⟩ : Fin 20) =
      ⟨aOneNeighbor d₂, by simp [aOneNeighbor]; split <;> omega⟩ := by
    apply e.injective
    apply Subtype.ext
    simpa [e, retainedLabelEquiv_val] using hLabelEq
  have hNat : aOneNeighbor d₁ = aOneNeighbor d₂ := Fin.ext_iff.mp hFin
  apply Fin.ext
  simp only [aOneNeighbor] at hNat
  split at hNat <;> split at hNat <;> omega

theorem retainedAfterDelete_true_iff (deleted vertex : Nat) :
    retainedAfterDelete deleted vertex = true ↔
      ∃ d < 8, d ≠ deleted ∧ vertex = aOneNeighbor d := by
  rw [retainedAfterDelete, any_eq_true_iff]
  constructor
  · rintro ⟨d, hd, hrow⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    exact ⟨d, hd, hrow.1, hrow.2⟩
  · rintro ⟨d, hd, hne, heq⟩
    exact ⟨d, hd, by simp [hne, heq]⟩

theorem outNeighbors_a0_eq_labelled (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hDegree : G.outdegree (a 0).1 = 8)
    (hA01 : G.Adj (a 0).1 (a 1).1)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1) :
    G.outNeighborFinset (a 0).1 =
      Finset.univ.image (fun d : Fin 8 ↦
        deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d) := by
  let e := retainedLabelEquiv G C a p z
  have hInject := deletionVertex_injective G C p z a
  apply Finset.Subset.antisymm
  · intro v hv
    have hCardImage : (Finset.univ.image (fun d : Fin 8 ↦
        deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d)).card = 8 := by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro x hx y hy hxy
        exact hInject hxy
    have hSubset : Finset.univ.image (fun d : Fin 8 ↦
        deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d) ⊆
        G.outNeighborFinset (a 0).1 := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨d, _, rfl⟩
      by_cases hd0 : (d : Nat) = 0
      · simp [deletionVertex, hd0, Digraph.mem_outNeighborFinset, hA01]
      · simp [deletionVertex, hd0, Digraph.mem_outNeighborFinset, hA0P]
    have hEqCard : (G.outNeighborFinset (a 0).1).card =
        (Finset.univ.image (fun d : Fin 8 ↦
          deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d)).card := by
      change G.outdegree (a 0).1 = _
      omega
    have hEq : Finset.univ.image (fun d : Fin 8 ↦
        deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d) =
        G.outNeighborFinset (a 0).1 :=
      Finset.eq_of_subset_of_card_le hSubset (by omega)
    rw [hEq]
    exact hv
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨d, _, rfl⟩
    by_cases hd0 : (d : Nat) = 0
    · simp [deletionVertex, hd0, Digraph.mem_outNeighborFinset, hA01]
    · simp [deletionVertex, hd0, Digraph.mem_outNeighborFinset, hA0P]

theorem deletionExpansionCount_ge_seven
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 → V) (r : Fin 4 → V)
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hDegree : G.outdegree (a 0).1 = 8)
    (hA01 : G.Adj (a 0).1 (a 1).1)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = h i)
    (hAR : ∀ i : Fin 4, (a ⟨i + 4, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 4, ¬G.Adj (p i).1 (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 5, ¬G.Adj (a i).1 (z j).1)
    (deleted : Nat) (hd : deleted < 8) :
    7 ≤ (deletionExpansionCount
      (coreBits G.Adj (fun i ↦ (p i).1) h r (fun i ↦ (z i).1)
        (fun i ↦ (a i).1)) deleted).toNat := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r
    (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  let dv := deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) deleted
  let S := (G.outNeighborFinset (a 0).1).erase dv
  let E := G.outNeighborFinsetOf S \ (S ∪ {(a 0).1})
  have hN := outNeighbors_a0_eq_labelled G C p z a hDegree hA01 hA0P
  have hdArc : G.Adj (a 0).1 dv := by
    apply (Digraph.mem_outNeighborFinset (G := G)).mp
    rw [hN]
    apply Finset.mem_image.mpr
    exact ⟨⟨deleted, hd⟩, Finset.mem_univ _, rfl⟩
  have hECard : 7 ≤ E.card := by
    simpa [S, E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hdArc
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro v hvE
    rcases Finset.mem_sdiff.mp hvE with ⟨hvReach, _⟩
    obtain ⟨middle, hmS, hmv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hmOut : middle ∈ G.outNeighborFinset (a 0).1 :=
      Finset.mem_of_mem_erase hmS
    have hmAP := A_outgoingCaptured G C hG (a 0).1 (a 0).2 hmOut
    rcases Finset.mem_union.mp hmAP with hmA | hmB
    · exact A_outgoingCaptured_retained G C hG hPB middle hmA
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
    · have hmP : middle ∈ C.P := by simpa [hPB] using hmB
      exact P_outgoingCaptured_retained G C hG hPB hEpsilon middle hmP
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
  let e := retainedLabelEquiv G C a p z
  have hCount : E.card ≤ (deletionExpansionCount bits deleted).toNat := by
    have hFilter := filterCard_le_count (V := V) (retainedVertexSet G C) e
      (deletionReached bits deleted) (fun v ↦ v ∈ E) (by omega) (by
        intro target htE
        rw [retainedLabelEquiv_val] at htE
        rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
        obtain ⟨middle, hmS, hmt⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
        have hmOut : middle ∈ G.outNeighborFinset (a 0).1 :=
          Finset.mem_of_mem_erase hmS
        rw [hN] at hmOut
        rcases Finset.mem_image.mp hmOut with ⟨d, _, hdMiddle⟩
        have hdNe : (d : Nat) ≠ deleted := by
          intro hdeq
          apply (Finset.mem_erase.mp hmS).1
          simpa [dv, hdeq] using hdMiddle.symm
        let middleIndex := aOneNeighbor (d : Nat)
        have hmIndex : middleIndex < 15 := by
          simp [middleIndex, aOneNeighbor]
          split <;> omega
        have hMiddleLabel : labelledVertex (fun i ↦ (a i).1)
            (fun i ↦ (p i).1) (fun i ↦ (z i).1) middleIndex = middle := by
          rw [labelled_aOneNeighbor (fun i ↦ (p i).1) (fun i ↦ (a i).1)
            (fun i ↦ (z i).1) d d.isLt]
          exact hdMiddle
        have hRetMiddle : retainedAfterDelete deleted middleIndex = true :=
          (retainedAfterDelete_true_iff deleted middleIndex).2
            ⟨d, d.isLt, hdNe, rfl⟩
        have hArc : coreArc bits middleIndex target = true := by
          rw [coreArc_coreBits G (fun i ↦ (p i).1) h r
            (fun i ↦ (z i).1) (fun i ↦ (a i).1)
            hA0P hP0 hAH hAR hPR hAZ middleIndex target hmIndex target.isLt]
          simp [hMiddleLabel, hmt]
        have htNeZero : (target : Nat) ≠ 0 := by
          intro ht0
          have htA0 : labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
              (fun i ↦ (z i).1) target = (a 0).1 := by
            have : target = 0 := Fin.ext ht0
            subst target
            simp [labelledVertex]
          exact htOutside (Finset.mem_union_right S (by simp [htA0]))
        have htNotRet : retainedAfterDelete deleted target = false := by
          apply Bool.eq_false_of_not_eq_true
          intro htRet
          rcases (retainedAfterDelete_true_iff deleted target).1 htRet with
            ⟨d', hd', hd'Ne, htIndex⟩
          have htLabel : labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
              (fun i ↦ (z i).1) target =
              deletionVertex (fun i ↦ (p i).1) (fun i ↦ (a i).1) d' := by
            rw [htIndex, labelled_aOneNeighbor (fun i ↦ (p i).1)
              (fun i ↦ (a i).1) (fun i ↦ (z i).1) d' hd']
          apply htOutside
          apply Finset.mem_union_left {(a 0).1}
          apply Finset.mem_erase.mpr
          constructor
          · intro heq
            have hDelEq : deletionVertex (fun i ↦ (p i).1)
                (fun i ↦ (a i).1) d' = dv := by simpa [htLabel] using heq
            have hIndexEq : (⟨d', hd'⟩ : Fin 8) = ⟨deleted, hd⟩ :=
              deletionVertex_injective G C p z a hDelEq
            exact hd'Ne (Fin.ext_iff.mp hIndexEq)
          · rw [hN]
            apply Finset.mem_image.mpr
            exact ⟨⟨d', hd'⟩, Finset.mem_univ _, htLabel.symm⟩
        unfold deletionReached
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨htNeZero, by simp [htNotRet]⟩, ?_⟩
        rw [any_eq_true_iff]
        exact ⟨middleIndex, by omega, by simp [hRetMiddle, hArc]⟩)
    have hFilterEq : ((retainedVertexSet G C).filter fun v ↦ v ∈ E).card =
        E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv ↦ hv.2, fun hv ↦ ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    simpa [deletionExpansionCount] using hFilter
  exact hECard.trans hCount

theorem aOneDeletionExpands_coreBits_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 → V) (r : Fin 4 → V)
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hDegree : G.outdegree (a 0).1 = 8)
    (hA01 : G.Adj (a 0).1 (a 1).1)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = h i)
    (hAR : ∀ i : Fin 4, (a ⟨i + 4, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 4, ¬G.Adj (p i).1 (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 5, ¬G.Adj (a i).1 (z j).1) :
    aOneDeletionExpands (coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)) = true := by
  rw [aOneDeletionExpands, all_eq_true_iff]
  intro deleted hd
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  exact deletionExpansionCount_ge_seven G hBound C hG hPB hEpsilon
    hNoSeymour p h r z a hDegree hA01 hA0P hP0 hAH hAR hPR hAZ deleted hd

end SeymourEight.FiveZHighDefectGraphBridge
