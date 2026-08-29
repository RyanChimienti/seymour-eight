import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.SharpAugmentedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.OrderingBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.EffectiveBridge
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.AnonCutDefs
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.Derived

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.SelectedAnonBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  AugmentedBridge SharpAugmentedBridge OrderingBridge EffectiveBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem qIn_toNat_le_internalInDegree_retained
    (C : G.LocalConfiguration) (L : Labels G 1 C) (q : Nat) (hq : q < 2) :
    (qIn (graphArc G L) q).toNat ≤
      internalInDegree G (retainedVertexSet G C) (L.q ⟨q, hq⟩).1 := by
  rw [qIn_toNat G C L q hq]
  unfold qInvariantKey
  rw [edgeCount_eq_sum_incoming]
  simp only [Finset.sum_singleton]
  unfold internalInDegree
  apply Finset.card_le_card
  intro v hv
  have hv' := Finset.mem_filter.mp hv
  apply Finset.mem_filter.mpr
  refine ⟨?_, hv'.2⟩
  rcases Finset.mem_union.mp hv'.1 with hvA | hvP
  · simp [retainedVertexSet, hvA]
  · simp [retainedVertexSet, hvP]

theorem retained_out_add_qIn_le_fifteen
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (q : Nat) (hq : q < 2) :
    directCount G (retainedVertexSet G C) (L.q ⟨q, hq⟩).1 +
      (qIn (graphArc G L) q).toNat ≤ 15 := by
  let qi := (L.q ⟨q, hq⟩).1
  have hqi : qi ∈ retainedVertexSet G C := by
    simp [qi, retainedVertexSet, (L.q ⟨q, hq⟩).2]
  have hCard : (retainedVertexSet G C).card = 16 := by
    simpa using (Fintype.card_congr (retainedLabelEquiv G C L hG)).symm
  have hIncident := internal_incident_subset_erase G
    (retainedVertexSet G C) qi hG
  have hDis := disjoint_internal_out_in G (retainedVertexSet G C) qi hG
  have hCap : directCount G (retainedVertexSet G C) qi +
      internalInDegree G (retainedVertexSet G C) qi ≤ 15 := by
    calc
      _ = (CertificateBridge.internalFirstNeighbors G (retainedVertexSet G C) qi ∪
          ((retainedVertexSet G C).filter fun u => G.Adj u qi)).card := by
            rw [Finset.card_union_of_disjoint hDis]
            rfl
      _ ≤ ((retainedVertexSet G C).erase qi).card :=
        Finset.card_le_card hIncident
      _ = 15 := by rw [Finset.card_erase_of_mem hqi, hCard]
  have hIn := qIn_toNat_le_internalInDegree_retained G C L q hq
  dsimp [qi] at hCap ⊢
  omega

theorem qIndividualAnonymousLower_le_directCount
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (q : Nat) (hq : q < 2) :
    (qIndividualAnonymousLower (graphArc G L) q).toNat ≤
      directCount G (qAnonymousSet G C) (L.q ⟨q, hq⟩).1 := by
  let qi := (L.q ⟨q, hq⟩).1
  have hSplit := q_outdegree_split G C qi (L.q ⟨q, hq⟩).2
  have hInc := retained_out_add_qIn_le_fifteen G C L hG q hq
  have hMinQ := hMin qi
  unfold qIndividualAnonymousLower
  split <;> rename_i hSeven
  · simp
  · simp only [BitVec.ule_eq_decide] at hSeven
    have hSevenNat : 7 ≤ (qIn (graphArc G L) q).toNat := by
      have hNot : ¬(qIn (graphArc G L) q).toNat ≤ 7 := by
        intro hLe
        apply hSeven
        exact decide_eq_true hLe
      omega
    have hSevenLe : (7 : BitVec 8) ≤ qIn (graphArc G L) q := by
      rw [BitVec.le_def]
      simpa using hSevenNat
    rw [BitVec.toNat_sub_of_le hSevenLe]
    have hSevenNat : (7 : BitVec 8).toNat = 7 := by decide
    rw [hSevenNat]
    dsimp [qi] at hSplit hMinQ ⊢
    omega

theorem qIndividualAnonymous_mem_second
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (a q : Nat) (ha : a < 8) (hq : q < 2)
    (hAdj : aToQ (graphArc G L) a q = true) :
    (qAnonymousSet G C).filter (G.Adj (L.q ⟨q, hq⟩).1) ⊆
      G.secondOutNeighborFinset (L.a ⟨a, ha⟩).1 := by
  intro v hv
  have hvParts := Finset.mem_filter.mp hv
  have hvOutside := (Finset.mem_sdiff.mp hvParts.1).2
  have haq : G.Adj (L.a ⟨a, ha⟩).1 (L.q ⟨q, hq⟩).1 := by
    rw [aToQ_graph G L a q ha hq] at hAdj
    exact of_decide_eq_true hAdj
  have hNot : ¬G.Adj (L.a ⟨a, ha⟩).1 v := by
    intro hav
    exact hvOutside (labelled_outgoing_retained G C L hG a (by omega)
      ((Digraph.mem_outNeighborFinset (G := G)).mpr (by
        simpa [labelledVertex, ha] using hav)))
  have hne : v ≠ (L.a ⟨a, ha⟩).1 := by
    intro heq
    apply hvOutside
    rw [heq]
    simp [retainedVertexSet, (L.a ⟨a, ha⟩).2]
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(L.q ⟨q, hq⟩).1, haq, hvParts.2⟩, hNot, hne⟩

theorem augmented_projected_individual_le_second
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (a q : Nat) (ha : a < 8) (hq : q < 2)
    (hAdj : aToQ (graphArc G L) a q = true) :
    (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat +
        (qIndividualAnonymousLower (graphArc G L) q).toNat ≤
      G.secondOutdegree (L.a ⟨a, ha⟩).1 := by
  let R := (retainedVertexSet G C).filter fun v =>
    v ∈ G.secondOutNeighborFinset (L.a ⟨a, ha⟩).1
  let U := (qAnonymousSet G C).filter (G.Adj (L.q ⟨q, hq⟩).1)
  have hProjected := projectedSecondCount_le_retained_second_card G C L hG
    (by omega) a (by omega)
  have hProjected' :
      (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat ≤
        ((retainedVertexSet G C).filter fun v =>
          v ∈ G.secondOutNeighborFinset (L.a ⟨a, ha⟩).1).card := by
    simpa [labelledVertex, ha] using hProjected
  have hLower := qIndividualAnonymousLower_le_directCount G C L hG hMin q hq
  have hDis : Disjoint R U := by
    rw [Finset.disjoint_left]
    intro v hvR hvU
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvU).1).2
      (Finset.mem_filter.mp hvR).1
  have hUnion : R ∪ U ⊆ G.secondOutNeighborFinset (L.a ⟨a, ha⟩).1 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvR | hvU
    · exact (Finset.mem_filter.mp hvR).2
    · exact qIndividualAnonymous_mem_second G C L hG a q ha hq hAdj hvU
  dsimp [R, U] at hProjected hLower hDis hUnion ⊢
  unfold directCount CertificateBridge.internalFirstNeighbors at hLower
  unfold Digraph.secondOutdegree
  calc
    _ ≤ ((retainedVertexSet G C).filter fun v =>
          v ∈ G.secondOutNeighborFinset (L.a ⟨a, ha⟩).1).card +
        ((qAnonymousSet G C).filter (G.Adj (L.q ⟨q, hq⟩).1)).card :=
      Nat.add_le_add hProjected' hLower
    _ = (((retainedVertexSet G C).filter fun v =>
          v ∈ G.secondOutNeighborFinset (L.a ⟨a, ha⟩).1) ∪
        (qAnonymousSet G C).filter (G.Adj (L.q ⟨q, hq⟩).1)).card :=
      (Finset.card_union_of_disjoint hDis).symm
    _ ≤ _ := Finset.card_le_card hUnion

theorem qIndividualAnonymousLower_toNat_le_six
    (arc : Nat → Nat → Bool) (q : Nat) :
    (qIndividualAnonymousLower arc q).toNat ≤ 6 := by
  unfold qIndividualAnonymousLower
  split <;> rename_i h
  · simp
  · simp only [BitVec.ule_eq_decide] at h
    have h7 : (7 : BitVec 8).toNat = 7 := by decide
    have hA := count_toNat_le 8 (fun a => aToQ arc a q) (by omega)
    have hP := count_toNat_le 5 (fun p => pToQ arc p q) (by omega)
    have hq : (qIn arc q).toNat ≤ 13 := by
      rw [qIn, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    have hSevenNat : 7 ≤ (qIn arc q).toNat := by
      by_contra hlt
      apply h
      exact decide_eq_true (by rw [h7]; omega)
    have hSeven : (7 : BitVec 8) ≤ qIn arc q := by
      rw [BitVec.le_def]
      simpa using hSevenNat
    rw [BitVec.toNat_sub_of_le hSeven]
    rw [h7]
    omega

theorem selectedAnonLower_toNat_le_six (arc : Nat → Nat → Bool)
    (a : Nat) : (selectedAnonLower arc a).toNat ≤ 6 := by
  by_cases h0 : aToQ arc a 0 = true
  · by_cases h1 : aToQ arc a 1 = true
    · simpa [selectedAnonLower, h0, h1] using
        qAnonymousSharpLower_toNat_le_six arc
    · simpa [selectedAnonLower, h0, h1] using
        qIndividualAnonymousLower_toNat_le_six arc 0
  · by_cases h1 : aToQ arc a 1 = true
    · simpa [selectedAnonLower, h0, h1] using
        qIndividualAnonymousLower_toNat_le_six arc 1
    · simp [selectedAnonLower, h0, h1]

theorem projected_add_selectedAnon_toNat (arc pToZ : Nat → Nat → Bool)
    (a : Nat) :
    (projectedSecondCount 1 arc pToZ a + selectedAnonLower arc a).toNat =
      (projectedSecondCount 1 arc pToZ a).toNat +
        (selectedAnonLower arc a).toNat := by
  have hp := count_toNat_le 16 (projectedSecond 1 arc pToZ a) (by omega)
  have hp' : (projectedSecondCount 1 arc pToZ a).toNat ≤ 16 := by
    simpa [projectedSecondCount] using hp
  have hq := selectedAnonLower_toNat_le_six arc a
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem augmented_projected_selected_le_second
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true)
    (a : Nat) (ha : a < 8) :
    (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat +
        (selectedAnonLower (graphArc G L) a).toNat ≤
      G.secondOutdegree (L.a ⟨a, ha⟩).1 := by
  by_cases h0 : aToQ (graphArc G L) a 0 = true
  · by_cases h1 : aToQ (graphArc G L) a 1 = true
    · have hBoth : reachesBothQFromA (graphArc G L) a = true := by
        simp [reachesBothQFromA, h0, h1]
      have hAug := augmented_projected_sharp_le_second G C L hG hMin
        hHCard hFixed a (by omega) (by simpa [ha] using hBoth)
      simpa [selectedAnonLower, h0, h1, labelledVertex, ha] using hAug
    · have hAug := augmented_projected_individual_le_second G C L hG hMin
        a 0 ha (by omega) h0
      simpa [selectedAnonLower, h0, h1] using hAug
  · by_cases h1 : aToQ (graphArc G L) a 1 = true
    · have hAug := augmented_projected_individual_le_second G C L hG hMin
        a 1 ha (by omega) h1
      simpa [selectedAnonLower, h0, h1] using hAug
    · have hProj := projectedSecondCount_le_graph_retained G C L hG
        (by omega) a (by omega)
      have hProj' :
          (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat ≤
            G.secondOutdegree (L.a ⟨a, ha⟩).1 := by
        simpa [labelledVertex, ha] using hProj
      simpa [selectedAnonLower, h0, h1] using hProj'

theorem aNonSeymourSelectedAnon_true
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 7) (hFixed : fixedAOne (graphArc G L) = true) :
    aNonSeymourSelectedAnon (graphArc G L) (graphPToZ G L) = true := by
  rw [aNonSeymourSelectedAnon, all_eq_true_iff]
  intro a ha
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hDegree := A_outdegree_eq_blocks G C L hG a ha
  have hAO := aOut_toNat G C L a ha
  have hBO := aBOut_toNat G C L a ha
  have hDegreeNat : (aDegree (graphArc G L) a).toNat =
      G.outdegree (L.a ⟨a, ha⟩).1 := by
    rw [aDegree, BitVec.toNat_add, hAO, hBO,
      Nat.mod_eq_of_lt (by
        have hA := Finset.card_le_card (Finset.filter_subset
          (G.Adj (L.a ⟨a, ha⟩).1) C.A)
        have hB := Finset.card_le_card (Finset.filter_subset
          (G.Adj (L.a ⟨a, ha⟩).1) C.B)
        have hACard : C.A.card = 8 := by
          simpa using (Fintype.card_congr L.a).symm
        have hBCard : C.B.card = 7 := by
          rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
          have hp : C.P.card = 5 := by
            simpa using (Fintype.card_congr L.p).symm
          have hq : C.Q.card = 2 := by
            simpa using (Fintype.card_congr L.q).symm
          change C.P.card + C.Q.card = 7
          omega
        change directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card at hA
        change directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card at hB
        omega), hDegree]
  have hAug := augmented_projected_selected_le_second G C L hG hMin
    hHCard hFixed a ha
  rw [projected_add_selectedAnon_toNat, hDegreeNat]
  exact hAug.trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h => hNoSeymour ⟨_, h⟩))

theorem selectedResidualCore_true
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hHCard : C.H.card = 7)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hk : C.k = 3) (hr : C.r = 5) (hyValue : BSevenKThree.y G C = 2)
    (hPOrder : ∀ q : Fin 4,
      pInvariantKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.p ⟨q.val, by omega⟩).1)
    (hAOneOrder : ∀ q : Fin 2,
      aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 3,
      aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1)
    (hQOrder : qInvariantKey G C (L.q 1).1 ≤
      qInvariantKey G C (L.q 0).1) :
    selectedResidualCore (graphArc G L) (graphPToZ G L) = true := by
  have hOrA := orientedA_true G C L hG
  have hOrP := orientedP_true G C L hG
  have hOrPH := orientedPH_true G C L hG
  have hFixed := fixedAOne_true G C L hG
  have hNoP := noPToAOne_true G C L hG
  have hQIn := qInB_true G C L
  have hQReach := qReachStatus_true G C L hA1Card 2 hyValue
  have hXReach := everyXReached_true G C L hA1Card
  have hACond := aConditions_true G C L hG hPivot hMin hk hr
  have hPCond := pConditions_true G C L hG hHCard (by omega) hMin
  have hAOutMinimum : ∀ a < 8,
      (3 : BitVec 8).ule (aOut (graphArc G L) a) = true := by
    rw [aConditions, all_eq_true_iff] at hACond
    intro a ha
    have hRow := hACond a ha
    simp only [Bool.and_eq_true] at hRow
    exact hRow.1.1
  have hDegreeThree := degreeThreeConsequences_true G C L hOrA hAOutMinimum
  have hDual := degreeAndDual_of_local 2 (graphArc G L) (Or.inr rfl)
    hOrA hOrPH hFixed hXReach hQReach hACond
  have hANon := aNonSeymourSelectedAnon_true G C L hG hMin hNoSeymour
    hHCard hFixed
  have hOrderedP := orderedP_true G C L hG hHCard hA1Card hXCard
    (by omega) hPOrder
  have hOrderedA := orderedAClasses_true G C L hAOneOrder hXOrder
  have hOrderedQ := orderedQ_true G C L hQOrder
  simp [selectedResidualCore, hOrA, hOrP, hOrPH, hFixed, hNoP, hQIn,
    hQReach, hXReach, hACond, hPCond, hDegreeThree.1, hDegreeThree.2,
    hDual, hANon, hOrderedP, hOrderedA, hOrderedQ]

theorem totalHOut_toNat (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (totalHOut (graphArc G L)).toNat = ∑ u ∈ C.H, G.outdegree u := by
  have hEach (i : Fin 7) :
      (aOut (graphArc G L) (1 + i) + hPOut (graphArc G L) i +
        count 2 (fun q => aToQ (graphArc G L) (1 + i) q)).toNat =
        G.outdegree (L.a ⟨1 + i, by omega⟩).1 := by
    have hA := aOut_toNat G C L (1 + i) (by omega)
    have hP : (hPOut (graphArc G L) i).toNat =
        directCount G C.P (L.a ⟨1 + i, by omega⟩).1 := by
      simpa [Nat.add_comm] using hPOut_toNat G C L i i.isLt
    have hQ := aQOut_toNat G C L (1 + i) (by omega)
    have hACap : directCount G C.A (L.a ⟨1 + i, by omega⟩).1 ≤ 8 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.a).symm)
    have hPCap : directCount G C.P (L.a ⟨1 + i, by omega⟩).1 ≤ 5 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.p).symm)
    have hQCap : directCount G C.Q (L.a ⟨1 + i, by omega⟩).1 ≤ 2 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.q).symm)
    have hCapture := BSixKThree.H_outgoingCaptured_general G C hG
      (L.a ⟨1 + i, by omega⟩).1
      (by simpa [hLabelEquiv_val, Nat.add_comm] using
        (hLabelEquiv G C L hHCard i).2)
    have hDegree : G.outdegree (L.a ⟨1 + i, by omega⟩).1 =
        directCount G C.A (L.a ⟨1 + i, by omega⟩).1 +
        directCount G C.P (L.a ⟨1 + i, by omega⟩).1 +
        directCount G C.Q (L.a ⟨1 + i, by omega⟩).1 := by
      rw [outdegree_eq_directCount_of_captured G (C.A ∪ C.B) _ hCapture,
        directCount_union_of_disjoint G C.A C.B _
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C),
        ← Digraph.LocalConfiguration.P_union_Q (G := G) C,
        directCount_union_of_disjoint G C.P C.Q _
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
      omega
    rw [BitVec.toNat_add, BitVec.toNat_add, hA, hP]
    change (count 2 (fun q => aToQ (graphArc G L) (1 + i) q)).toNat = _ at hQ
    rw [hQ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hDegree]
  rw [totalHOut, toNat_sumCount, ← Fin.sum_univ_eq_sum_range]
  have hBound : (∑ i : Fin 7,
      (aOut (graphArc G L) (1 + i) + hPOut (graphArc G L) i +
        count 2 (fun q => aToQ (graphArc G L) (1 + i) q)).toNat) < 256 := by
    calc
      _ ≤ ∑ _i : Fin 7, 15 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hEach i
        have hCaptured := BSixKThree.H_outgoingCaptured_general G C hG
          (L.a ⟨1 + i, by omega⟩).1 (by
            simpa [hLabelEquiv_val, Nat.add_comm] using
              (hLabelEquiv G C L hHCard i).2)
        have hCard : (C.A ∪ C.B).card = 15 := by
          rw [Finset.card_union_of_disjoint
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)]
          have hA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
          have hB : C.B.card = 7 := by
            have hP : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
            have hQ : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
            rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
              Finset.card_union_of_disjoint
                (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
            omega
          omega
        rw [hi]
        rw [outdegree_eq_directCount_of_captured G (C.A ∪ C.B) _ hCaptured]
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hCard
      _ = 105 := by simp
      _ < 256 := by omega
  rw [Nat.mod_eq_of_lt hBound]
  calc
    _ = ∑ i : Fin 7, G.outdegree (L.a ⟨1 + i, by omega⟩).1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hEach i
    _ = ∑ u ∈ C.H, G.outdegree u := by
      calc
        _ = edgeCount G C.H (C.A ∪ C.B) := by
          rw [edgeCount_eq_sum_fin G C.H (C.A ∪ C.B)
            (hLabelEquiv G C L hHCard)]
          apply Finset.sum_congr rfl
          intro i _
          rw [← outdegree_eq_directCount_of_captured G (C.A ∪ C.B) _
            (BSixKThree.H_outgoingCaptured_general G C hG _
              (hLabelEquiv G C L hHCard i).2)]
          simp [hLabelEquiv_val, Nat.add_comm]
        _ = ∑ u ∈ C.H, G.outdegree u := by
          unfold edgeCount
          apply Finset.sum_congr rfl
          intro u hu
          exact (outdegree_eq_directCount_of_captured G (C.A ∪ C.B) u
            (BSixKThree.H_outgoingCaptured_general G C hG u hu)).symm

theorem etaH_toNat (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) :
    (etaH (graphArc G L)).toNat =
      (∑ u ∈ C.H, G.outdegree u) - 56 := by
  have hLower : 56 ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      56 = ∑ _u ∈ C.H, 8 := by simp [hHCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hLe : (56 : BitVec 8) ≤ totalHOut (graphArc G L) := by
    rw [BitVec.le_def, totalHOut_toNat G C L hG hHCard]
    simpa using hLower
  have h56 : (56 : BitVec 8).toNat = 56 := by decide
  rw [etaH, BitVec.toNat_sub_of_le hLe, totalHOut_toNat G C L hG hHCard]
  rw [h56]

theorem hQDefect_two_toNat (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hHCard : C.H.card = 7) :
    (hQDefect 2 (graphArc G L)).toNat = 14 - edgeCount G C.H C.Q := by
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hCap := edgeCount_le_card_mul_card G C.H C.Q
  rw [hHCard, hQCard] at hCap
  have h14 : (14 : BitVec 8).toNat = 14 := by decide
  have hLe : totalHToQ (graphArc G L) ≤ (14 : BitVec 8) := by
    rw [BitVec.le_def, totalHToQ_toNat G C L hHCard, h14]
    omega
  change ((14 : BitVec 8) - totalHToQ (graphArc G L)).toNat = _
  rw [BitVec.toNat_sub_of_le hLe, h14, totalHToQ_toNat G C L hHCard]

theorem selected_aggregate_upper
    (C : G.LocalConfiguration) (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hx : C.x = 4) (hRCard : C.R.card = 0)
    (hy : BSevenKThree.y G C = 2) :
    (etaH (graphArc G L) + externalMissing 1 (graphArc G L) (graphPToZ G L) +
      hQDefect 2 (graphArc G L)).toNat ≤ 3 := by
  have hHSplit := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
  have hHA := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  rw [hHCard, hx, hRCard] at hHA
  norm_num [Nat.choose] at hHA
  have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hPCard] at hCross
  have hPSplit := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hPMin : 40 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      40 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hPP := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hPP
  norm_num [Nat.choose] at hPP
  have hReachedQ : BSevenKThree.reachedQ G C = C.Q := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
    have hReachedCard : (BSevenKThree.reachedQ G C).card = 2 := by
      simpa [BSevenKThree.y] using hy
    rw [hQCard]
    change 2 ≤ (BSevenKThree.reachedQ G C).card
    omega
  have hAux : edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [auxiliarySet, hReachedQ, edgeCount_union_of_disjoint G C.P C.Q
      (externalTargets G C)]
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  have hExt := externalMissing_toNat G C L hHCard (by omega) hy (by omega)
  have hEta := etaH_toNat G C L hG hMin hHCard
  have hQ := hQDefect_two_toNat G C L hHCard
  have hHMin : 56 ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      56 = ∑ _u ∈ C.H, 8 := by simp [hHCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hHQCap := edgeCount_le_card_mul_card G C.H C.Q
  rw [hHCard, hQCard] at hHQCap
  have hAuxCard := auxiliarySet_card G C L hy
  have hAuxCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  rw [hPCard, hAuxCard] at hAuxCap
  norm_num at hAuxCap
  have hNatural :
      (etaH (graphArc G L)).toNat +
        (externalMissing 1 (graphArc G L) (graphPToZ G L)).toNat +
        (hQDefect 2 (graphArc G L)).toNat ≤ 3 := by
    rw [hEta, hExt, hQ]
    omega
  rw [BitVec.toNat_add, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.SelectedAnonBridge
