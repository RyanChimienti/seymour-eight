import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.HDeletionBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidConsequence
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.Counts

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.RigidBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  EffectiveBridge CommonBridge DefectBridge HDeletionBridge
open Rigid

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pointwise_eq_of_sum_eq_card_mul_upper {W : Type*}
    (S : Finset W) (f : W → Nat) (d : Nat)
    (hUpper : ∀ v ∈ S, f v ≤ d)
    (hSum : ∑ v ∈ S, f v = S.card * d) :
    ∀ v ∈ S, f v = d := by
  intro v hv
  apply Nat.le_antisymm (hUpper v hv)
  by_contra hNot
  have hStrict : f v < d := by omega
  have hSumStrict : (∑ w ∈ S, f w) < ∑ _w ∈ S, d := by
    apply Finset.sum_lt_sum
    · exact hUpper
    · exact ⟨v, hv, hStrict⟩
  simp [hSum] at hSumStrict

omit [Fintype V] [DecidableEq V] in
theorem cross_complete_of_max (S T : Finset V)
    (hG : G.IsOriented)
    (hMax : edgeCount G S T + edgeCount G T S = S.card * T.card)
    {u v : V} (hu : u ∈ S) (hv : v ∈ T) :
    G.Adj u v ∨ G.Adj v u := by
  classical
  have hIncident : ∀ w ∈ T,
      directCount G S w + internalInDegree G S w ≤ S.card := by
    intro w hw
    have hDisjoint : Disjoint
        (CertificateBridge.internalFirstNeighbors G S w)
        (S.filter fun x ↦ G.Adj x w) := by
      rw [Finset.disjoint_left]
      intro x hxOut hxIn
      exact hG.2 (Finset.mem_filter.mp hxOut).2
        (Finset.mem_filter.mp hxIn).2
    calc
      directCount G S w + internalInDegree G S w =
          (CertificateBridge.internalFirstNeighbors G S w ∪
            (S.filter fun x ↦ G.Adj x w)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
        rfl
      _ ≤ S.card := Finset.card_le_card (by
        intro x hx
        rcases Finset.mem_union.mp hx with hxOut | hxIn
        · exact (Finset.mem_filter.mp hxOut).1
        · exact (Finset.mem_filter.mp hxIn).1)
  have hSum : ∑ w ∈ T,
      (directCount G S w + internalInDegree G S w) = T.card * S.card := by
    rw [Finset.sum_add_distrib, ← edgeCount,
      ← edgeCount_eq_sum_incoming (G := G)]
    simpa [Nat.mul_comm, Nat.add_comm] using hMax
  have hvMax := pointwise_eq_of_sum_eq_card_mul_upper T
    (fun w ↦ directCount G S w + internalInDegree G S w) S.card
    hIncident hSum v hv
  let U := CertificateBridge.internalFirstNeighbors G S v ∪
    (S.filter fun x ↦ G.Adj x v)
  have hDisjoint : Disjoint
      (CertificateBridge.internalFirstNeighbors G S v)
      (S.filter fun x ↦ G.Adj x v) := by
    rw [Finset.disjoint_left]
    intro x hxOut hxIn
    exact hG.2 (Finset.mem_filter.mp hxOut).2
      (Finset.mem_filter.mp hxIn).2
  have hCardU : U.card = S.card := by
    rw [show U = CertificateBridge.internalFirstNeighbors G S v ∪
      (S.filter fun x ↦ G.Adj x v) by rfl,
      Finset.card_union_of_disjoint hDisjoint]
    exact hvMax
  have hSubset : U ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxOut | hxIn
    · exact (Finset.mem_filter.mp hxOut).1
    · exact (Finset.mem_filter.mp hxIn).1
  have hEq : U = S := Finset.eq_of_subset_of_card_le hSubset (by omega)
  have huU : u ∈ U := by rw [hEq]; exact hu
  rcases Finset.mem_union.mp huU with huOut | huIn
  · exact Or.inr (Finset.mem_filter.mp huOut).2
  · exact Or.inl (Finset.mem_filter.mp huIn).2

theorem bool_true_of_full_count (n : Nat) (f : Nat → Bool)
    (hn : n < 256) (hCount : (count n f).toNat = n)
    {i : Nat} (hi : i < n) : f i = true := by
  by_contra hFalse
  have hfi : f i = false := Bool.eq_false_of_not_eq_true hFalse
  rw [toNat_count_eq_fin_sum n f hn] at hCount
  have hStrict : (∑ j : Fin n, if f j then 1 else 0) <
      ∑ _j : Fin n, 1 := by
    apply Finset.sum_lt_sum
    · intro j hj
      split <;> omega
    · exact ⟨⟨i, hi⟩, Finset.mem_univ _, by simp [hfi]⟩
  simp [hCount] at hStrict

theorem count_toNat_le (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat ≤ n := by
  rw [toNat_count n f hn]
  calc
    (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤
        ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases f i <;> decide
    _ = n := by simp

/-- In the `alpha = 0` rows the lower dual inequality and orientedness
force every `H-q` and every `H-P` pair to be present. -/
theorem alpha_zero_defects
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hAlpha : alpha 1 (graphArc G L) = 0) :
    hQDefect 1 (graphArc G L) = 0 ∧
      crossMissing (graphArc G L) = 0 ∧
      edgeCount G C.P C.H + edgeCount G C.H C.P = 42 := by
  have hDelta := aMissing_toNat_le_four G C L hG hACond
  have hQLe := hQDefect_toNat_le_seven (graphArc G L)
  have hPBound := two_aMissing_add_PToH_le_fifteen G C L hG hHCard
    hACond hDual
  have hAlphaNat : (alpha 1 (graphArc G L)).toNat = 0 := by
    rw [hAlpha]
    decide
  rw [alpha_toNat G C L hG hHCard hACond hDual] at hAlphaNat
  have hPToH : edgeCount G C.P C.H =
      15 - 2 * (aMissing (graphArc G L)).toNat := by omega
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true,
    BitVec.ule_eq_decide, decide_eq_true_eq] at hDualParts
  have hLower := hDualParts.1.1
  rw [totalHToP_toNat G C L hHCard] at hLower
  simp only [BitVec.toNat_add, BitVec.toNat_mul] at hLower
  norm_num [BitVec.toNat_ofNat] at hLower
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  rw [hTwo] at hLower
  have hRawSmall : 27 + 2 * (aMissing (graphArc G L)).toNat +
      (hQDefect 1 (graphArc G L)).toNat < 256 := by omega
  rw [Nat.mod_eq_of_lt hRawSmall] at hLower
  have hCrossBound := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hPCard, hHCard] at hCrossBound
  have hQNat : (hQDefect 1 (graphArc G L)).toNat = 0 := by omega
  have hCrossSum : edgeCount G C.P C.H + edgeCount G C.H C.P = 42 := by
    omega
  have hQ : hQDefect 1 (graphArc G L) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hQNat
  have hPLe : totalPToH (graphArc G L) ≤ (42 : BitVec 8) := by
    rw [BitVec.le_def, totalPToH_toNat G C L hG hHCard]
    have hFortyTwo : (42 : BitVec 8).toNat = 42 := by decide
    rw [hFortyTwo]
    omega
  have hFirstNat : ((42 : BitVec 8) - totalPToH (graphArc G L)).toNat =
      42 - edgeCount G C.P C.H := by
    rw [BitVec.toNat_sub_of_le hPLe,
      totalPToH_toNat G C L hG hHCard]
    have hFortyTwo : (42 : BitVec 8).toNat = 42 := by decide
    rw [hFortyTwo]
  have hHLe : totalHToP (graphArc G L) ≤
      (42 : BitVec 8) - totalPToH (graphArc G L) := by
    rw [BitVec.le_def, totalHToP_toNat G C L hHCard, hFirstNat]
    omega
  have hCrossNat : (crossMissing (graphArc G L)).toNat = 0 := by
    rw [crossMissing, BitVec.toNat_sub_of_le hHLe, hFirstNat,
      totalHToP_toNat G C L hHCard]
    omega
  have hCross : crossMissing (graphArc G L) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hCrossNat
  exact ⟨hQ, hCross, hCrossSum⟩

theorem hQComplete_true (L : Labels G 3 C)
    (hQ : hQDefect 1 (graphArc G L) = 0) :
    hQComplete (graphArc G L) = true := by
  have hTotalLe : totalHToQ (graphArc G L) ≤ (7 : BitVec 8) := by
    rw [BitVec.le_def, totalHToQ]
    have hSeven : (7 : BitVec 8).toNat = 7 := by decide
    rw [hSeven]
    exact count_toNat_le 7 _ (by omega)
  have hSubNat : ((7 : BitVec 8) - totalHToQ (graphArc G L)).toNat = 0 := by
    simpa [hQDefect] using congrArg BitVec.toNat hQ
  rw [BitVec.toNat_sub_of_le hTotalLe] at hSubNat
  have hSeven : (7 : BitVec 8).toNat = 7 := by decide
  rw [hSeven] at hSubNat
  have hTotalNatLe : (totalHToQ (graphArc G L)).toNat ≤ 7 := by
    rw [← hSeven]
    exact hTotalLe
  have hCount : (count 7 (fun h ↦ aToQ (graphArc G L) (1 + h))).toNat = 7 := by
    simpa [totalHToQ] using (show (totalHToQ (graphArc G L)).toNat = 7 by omega)
  rw [hQComplete, all_eq_true_iff]
  intro h hh
  exact bool_true_of_full_count 7
    (fun h ↦ aToQ (graphArc G L) (1 + h)) (by omega) hCount hh

theorem hpDirectionsComplete_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hMax : edgeCount G C.P C.H + edgeCount G C.H C.P = 42) :
    hpDirectionsComplete (graphArc G L) = true := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hpDirectionsComplete, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  have hMax' : edgeCount G C.P C.H + edgeCount G C.H C.P =
      C.P.card * C.H.card := by
    rw [hPCard, hHCard]
    norm_num
    exact hMax
  have hPair := cross_complete_of_max G C.P C.H hG hMax'
    (L.p ⟨p, hp⟩).2 ((hLabelEquiv G C L hHCard) ⟨h, hh⟩).2
  rw [hLabelEquiv_val] at hPair
  have hPair' :
      G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨1 + h, by omega⟩).1 ∨
        G.Adj (L.a ⟨1 + h, by omega⟩).1 (L.p ⟨p, hp⟩).1 := by
    simpa [Nat.add_comm] using hPair
  rw [pToA_graph G L p (1 + h) hp (by omega),
    aToP_graph G L (1 + h) p (by omega) hp]
  rcases hPair' with hForward | hReverse
  · have hNot := hG.2 hForward
    simp [hForward, hNot]
  · have hNot := hG.2 hReverse
    simp [hReverse, hNot]

theorem aDirectionsComplete_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMissing : aMissing (graphArc G L) = 0) :
    aDirectionsComplete (graphArc G L) = true := by
  have hMissingNat : (aMissing (graphArc G L)).toNat = 0 := by
    rw [hMissing]
    decide
  rw [aMissing_toNat G C L hG] at hMissingNat
  have hACard : C.A.card = 8 := by
    simpa using (Fintype.card_congr L.a).symm
  have hEdges : edgeCount G C.A C.A = C.A.card.choose 2 := by
    have hCap := internal_edgeCount_le_choose_two G C.A hG
    rw [hACard]
    norm_num [Nat.choose]
    rw [hACard] at hCap
    norm_num [Nat.choose] at hCap
    omega
  rw [aDirectionsComplete, all_eq_true_iff]
  intro i hi
  simp only [Bool.and_eq_true]
  constructor
  · rw [aArc_graph G L i i hi hi]
    simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, decide_false, Bool.false_or]
      have hPair :=
        SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
          G C.A hG hEdges
            (L.a ⟨i, hi⟩).2 (L.a ⟨j, hj⟩).2 (by
              intro hEq
              have hFin : (⟨i, hi⟩ : Fin 8) = ⟨j, hj⟩ :=
                L.a.injective (Subtype.ext hEq)
              exact hij (congrArg Fin.val hFin))
      rw [aArc_graph G L i j hi hj, aArc_graph G L j i hj hi]
      rcases hPair with hForward | hReverse
      · have hNot := hG.2 hForward
        simp [hForward, hNot]
      · have hNot := hG.2 hReverse
        simp [hReverse, hNot]

theorem alphaZeroArc_eq_of_agreement (arc : Nat → Nat → Bool)
    (h : alphaZeroAgreement arc = true) : alphaZeroArc arc = arc := by
  funext i j
  by_cases hi : i < 15
  · by_cases hj : j < 15
    · rw [alphaZeroAgreement, all_eq_true_iff] at h
      have hi' := h i hi
      rw [all_eq_true_iff] at hi'
      simpa using hi' j hj
    · simp only [alphaZeroArc]
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      rfl
  · simp only [alphaZeroArc]
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    rfl

theorem rigidArc_eq_of_agreement (arc : Nat → Nat → Bool)
    (h : rigidAgreement arc = true) : rigidArc arc = arc := by
  funext i j
  by_cases hi : i < 15
  · by_cases hj : j < 15
    · rw [rigidAgreement, all_eq_true_iff] at h
      have hi' := h i hi
      rw [all_eq_true_iff] at hi'
      simpa using hi' j hj
    · simp only [rigidArc]
      split <;> rename_i hBranch
      · omega
      simp only [alphaZeroArc]
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      rfl
  · simp only [rigidArc]
    split <;> rename_i hBranch
    · omega
    simp only [alphaZeroArc]
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    rfl

theorem aRigidArc_eq_of_agreement (arc : Nat → Nat → Bool)
    (h : aRigidAgreement arc = true) : aRigidArc arc = arc := by
  funext i j
  by_cases hi : i < 15
  · by_cases hj : j < 15
    · rw [aRigidAgreement, all_eq_true_iff] at h
      have hi' := h i hi
      rw [all_eq_true_iff] at hi'
      simpa using hi' j hj
    · simp only [aRigidArc]
      split <;> rename_i hBranch
      · omega
      simp only [fixedArc]
      split <;> rename_i hBranch
      · omega
      split <;> rename_i hBranch
      · omega
      rfl
  · simp only [aRigidArc]
    split <;> rename_i hBranch
    · omega
    simp only [fixedArc]
    split <;> rename_i hBranch
    · omega
    split <;> rename_i hBranch
    · omega
    rfl

theorem alphaZeroPremise_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hAlpha : alpha 1 (graphArc G L) = 0) :
    alphaZeroPremise (graphArc G L) = true := by
  have hDefects := alpha_zero_defects G C L hG hHCard hACond hDual hAlpha
  have hQ := hQComplete_true G L hDefects.1
  have hHP := hpDirectionsComplete_true G C L hG hHCard hDefects.2.2
  have hFixed := fixedAOne_true G C L hG
  have hNoP := noPToAOne_true G C L hG
  simp [alphaZeroPremise, hFixed, hNoP, hQ, hHP]

theorem alphaZeroArc_graph_eq (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hAlpha : alpha 1 (graphArc G L) = 0) :
    alphaZeroArc (graphArc G L) = graphArc G L := by
  apply alphaZeroArc_eq_of_agreement
  exact alphaZeroPremise_agrees _
    (alphaZeroPremise_true G C L hG hHCard hACond hDual hAlpha)

theorem rigidArc_graph_eq (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hAlpha : alpha 1 (graphArc G L) = 0)
    (hMissing : aMissing (graphArc G L) = 0) :
    rigidArc (graphArc G L) = graphArc G L := by
  apply rigidArc_eq_of_agreement
  apply rigidPremise_agrees
  simp [rigidPremise,
    alphaZeroPremise_true G C L hG hHCard hACond hDual hAlpha,
    aDirectionsComplete_true G C L hG hMissing]

theorem aRigidArc_graph_eq (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMissing : aMissing (graphArc G L) = 0) :
    aRigidArc (graphArc G L) = graphArc G L := by
  apply aRigidArc_eq_of_agreement
  apply aRigidPremise_agrees
  have hFixed := fixedAOne_true G C L hG
  have hNoP := noPToAOne_true G C L hG
  have hA := aDirectionsComplete_true G C L hG hMissing
  simp [aRigidPremise, fixedPremise, hFixed, hNoP, hA]

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.RigidBridge
