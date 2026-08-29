import SeymourEight.Cases.BSixKThree.CoreGraphBridge

/-!
# Strengthened bridge for the largest `(6,3)` row

The largest Boolean certificate contains redundant consequences which make its
SAT refutation substantially smaller.  This file verifies those consequences
for the labelled graph model.
-/

namespace SeymourEight.BSixKThreeCoreGraphBridge

open BSixKThree BSixKThreeCore Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The strengthened `(r,x,w)=(6,4,4)` core is true for every corresponding
labelled graph configuration. -/
theorem xFourCore_of_graphData (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 6) (hk : C.k = 3)
    (hxEq : C.x = 4) (hrEq : C.r = 6)
    (hWCard : (externalTargets G C).card = 4)
    (hHP : 31 ≤ edgeCount G C.H C.P)
    (hPW : 22 ≤ edgeCount G C.P (externalTargets G C))
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X})
    (eR : Fin 0 ≃ {v : V // v ∈ C.R})
    (eP : Fin 6 ≃ {v : V // v ∈ C.P})
    (eQ : Fin 0 ≃ {v : V // v ∈ C.Q})
    (eW : Fin 4 ≃ {v : V // v ∈ externalTargets G C}) :
    let label := localLabel (by omega : 4 ≤ 4) (by omega : 6 ≤ 6)
      C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1)
    xFourCore (graphArc G label)
      (graphExternalArc G (fun j => (eP j).1) (fun j => (eW j).1)) = true := by
  dsimp only
  let label := localLabel (by omega : 4 ≤ 4) (by omega : 6 ≤ 6)
    C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
    (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1)
  let arc := graphArc G label
  let externalArc := graphExternalArc G (fun j => (eP j).1)
    (fun j => (eW j).1)
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hRCard : C.R.card = 0 := by
    have := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hQCard : C.Q.card = 0 := by
    have := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hHCard : C.H.card = 7 := by
    have := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  have hPB : C.P = C.B := BSixKThree.p_eq_B_of_r_six G C hBCard hrEq
  have hCore : core 6 4 4 arc externalArc = true := by
    exact core_of_graphData G C hG hMin hNoSeymour hPivot hRootDegree
      hBCard hk hxEq hrEq hWCard (by omega) (by omega)
      eA1 eX eR eP eQ eW
  have hLabelA (i : Nat) (hi : i < 8) :
      label ⟨i, by omega⟩ =
        aLabel (by omega : 4 ≤ 4) C.a1 (fun j => (eA1 j).1)
          (fun j => (eX j).1) (fun j => (eR j).1) ⟨i, hi⟩ := by
    exact localLabel_A (by omega : 4 ≤ 4) (by omega : 6 ≤ 6)
      C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelA1 (i : Nat) (hi : i < 3) :
      label ⟨1 + i, by omega⟩ = (eA1 ⟨i, hi⟩).1 := by
    exact localLabel_A1 (by omega) (by omega) C.a1
      (fun j => (eA1 j).1) (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelX (i : Nat) (hi : i < 4) :
      label ⟨4 + i, by omega⟩ = (eX ⟨i, hi⟩).1 := by
    exact localLabel_X (by omega) (by omega) C.a1
      (fun j => (eA1 j).1) (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelP (i : Nat) (hi : i < 6) :
      label ⟨8 + i, by omega⟩ = (eP ⟨i, hi⟩).1 := by
    exact localLabel_P (by omega) (by omega) C.a1
      (fun j => (eA1 j).1) (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  let eA := aLabelEquiv G C (by omega : 4 ≤ 4) hACard eA1 eX eR
  have hAMem (i : Nat) (hi : i < 8) : label ⟨i, by omega⟩ ∈ C.A := by
    have hm := (eA ⟨i, hi⟩).2
    rw [aLabelEquiv_apply] at hm
    rw [hLabelA i hi]
    exact hm
  have hPivotAll : (allN 8 fun i => pivotRow 6 arc i) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    have hp := hPivot _ (hAMem i hi)
    rw [pivotRow]
    simp only [Bool.and_eq_true, Bool.or_eq_true, BitVec.ule_eq_decide,
      BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [toNat_internalA G C (by omega) (by omega) hACard eA1 eX eR
      (fun j => (eP j).1) (fun j => (eQ j).1) i (by omega),
      toNat_outB G C (by omega) (by omega) hBCard C.a1
        (fun j => (eA1 j).1) (fun j => (eX j).1)
        (fun j => (eR j).1) eP eQ i (by omega)]
    have hA : 3 ≤ directCount G C.A (label ⟨i, by omega⟩) := by
      simpa [directCount, internalFirstNeighbors, hk] using hp.1
    constructor
    · simpa [BitVec.toNat_ofNat] using hA
    · by_cases hEq : directCount G C.A (label ⟨i, by omega⟩) = 3
      · right
        have hB := hp.2 (by
          simpa [directCount, internalFirstNeighbors, hk] using hEq)
        simpa [directCount, internalFirstNeighbors, hrEq,
          BitVec.toNat_ofNat] using hB
      · left
        have : 3 < directCount G C.A (label ⟨i, by omega⟩) := by omega
        simpa [BitVec.toNat_ofNat] using this
  have hDegreeAll : (allN 8 fun i =>
      (8 : BitVec 8).ule (localOut arc i)) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [toNat_localOut G C (by omega) (by omega) hACard hBCard
      eA1 eX eR eP eQ i (by omega)]
    have huA := hAMem i hi
    have hCaptured : G.outNeighborFinset (label ⟨i, by omega⟩) ⊆ C.A ∪ C.B := by
      intro v hv
      by_cases hui : label ⟨i, by omega⟩ = C.a1
      · rw [hui, Shared.outNeighborFinset_a1_eq_A1_union_P G C hG] at hv
        rcases Finset.mem_union.mp hv with hvA1 | hvP
        · exact Finset.mem_union_left C.B
            (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA1)
        · exact Finset.mem_union_right C.A
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
      · have huH : label ⟨i, by omega⟩ ∈ C.H := by
          have hParts : label ⟨i, by omega⟩ ∈
              (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R := by
            rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
            exact huA
          rcases Finset.mem_union.mp hParts with hLocal | hR
          · rcases Finset.mem_union.mp hLocal with hH | ha1
            · exact hH
            · exact False.elim (hui (Finset.mem_singleton.mp ha1))
          · have hREmpty : C.R = ∅ := Finset.card_eq_zero.mp hRCard
            simp [hREmpty] at hR
        exact BSixKThree.H_outgoingCaptured_general G C hG _ huH hv
    rw [← outdegree_eq_directCount_of_captured G _ _ hCaptured]
    exact hMin _
  have hReachX : (allN 4 fun j => anyN 3 (fun i => arc (1 + i) (4 + j)) ||
      anyN 6 (fun i => arc (8 + i) (4 + j))) = true := by
    rw [allN_eq_true_iff]
    intro j hj
    have hvX := (eX ⟨j, hj⟩).2
    rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_inter.mp hvX).1 with ⟨u, hu, huv⟩
    rcases Finset.mem_union.mp hu with huA1 | huP
    · rw [Bool.or_eq_true]
      left
      rw [anyN_eq_true_iff]
      obtain ⟨i, hiA1⟩ := eA1.surjective ⟨u, huA1⟩
      refine ⟨i, i.isLt, ?_⟩
      have huLabel : (eA1 i).1 = u := congrArg Subtype.val hiA1
      change decide (G.Adj (localAt label (1 + i.val))
        (localAt label (4 + j))) = true
      rw [decide_eq_true_eq, localAt_of_lt _ _ (by omega),
        localAt_of_lt _ _ (by omega), hLabelA1 i i.isLt,
        hLabelX j hj, huLabel]
      exact huv
    · rw [Bool.or_eq_true]
      right
      rw [anyN_eq_true_iff]
      obtain ⟨i, hiP⟩ := eP.surjective ⟨u, huP⟩
      refine ⟨i, i.isLt, ?_⟩
      have huLabel : (eP i).1 = u := congrArg Subtype.val hiP
      change decide (G.Adj (localAt label (8 + i.val))
        (localAt label (4 + j))) = true
      rw [decide_eq_true_eq, localAt_of_lt _ _ (by omega),
        localAt_of_lt _ _ (by omega), hLabelP i i.isLt,
        hLabelX j hj, huLabel]
      exact huv
  have hReachB : (allN 6 fun j => anyN 8 fun i => arc i (8 + j)) = true := by
    rw [allN_eq_true_iff]
    intro j hj
    have hvB : (eP ⟨j, hj⟩).1 ∈ C.B := by
      exact Digraph.LocalConfiguration.P_subset_B (G := G) C (eP ⟨j, hj⟩).2
    have hSecond := (Digraph.mem_secondOutNeighborFinset (G := G)).mp hvB
    rcases (Digraph.mem_secondOutNeighborSet (G := G)).mp hSecond with
      ⟨⟨u, hsu, huv⟩, _⟩
    have huA : u ∈ C.A := (Digraph.mem_outNeighborFinset (G := G)).mpr hsu
    obtain ⟨i, hiA⟩ := eA.surjective ⟨u, huA⟩
    rw [anyN_eq_true_iff]
    refine ⟨i, i.isLt, ?_⟩
    have hLocal : label ⟨i.val, by omega⟩ = u := by
      rw [hLabelA i i.isLt, ← aLabelEquiv_apply]
      exact congrArg Subtype.val hiA
    change decide (G.Adj (localAt label i.val) (localAt label (8 + j))) = true
    rw [decide_eq_true_eq, localAt_of_lt _ i.val (by omega),
      localAt_of_lt _ (8 + j) (by omega), hLocal, hLabelP j hj]
    exact huv
  have hReachW : (allN 4 fun j => anyN 6 fun i => externalArc i j) = true := by
    rw [allN_eq_true_iff]
    intro j hj
    have hvW := (eW ⟨j, hj⟩).2
    rcases Finset.mem_union.mp hvW with hvZ | hvRoot
    · rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
          (Finset.mem_sdiff.mp hvZ).1 with ⟨p, hp, hpv⟩
      obtain ⟨i, hiP⟩ := eP.surjective ⟨p, hp⟩
      rw [anyN_eq_true_iff]
      refine ⟨i, i.isLt, ?_⟩
      have hpLabel : (eP i).1 = p := congrArg Subtype.val hiP
      simp [externalArc, hpLabel, hpv, hj]
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : (eW ⟨j, hj⟩).1 = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        rcases hReach with ⟨p, hp, hps⟩
        obtain ⟨i, hiP⟩ := eP.surjective ⟨p, hp⟩
        rw [anyN_eq_true_iff]
        refine ⟨i, i.isLt, ?_⟩
        have hpLabel : (eP i).1 = p := congrArg Subtype.val hiP
        simp [externalArc, hpLabel, hvs, hps, hj]
      · simp [rootSecondFinset, hReach] at hvRoot
  have hHPDecode :
      (sumCountsN 7 fun i => outB arc (1 + i)).toNat = edgeCount G C.H C.P := by
    rw [hPB]
    rw [toNat_sumCountsN_of_le 7 6 _ (by omega) (by
      intro i hi
      rw [toNat_outB G C (by omega) (by omega) hBCard C.a1
        (fun j => (eA1 j).1) (fun j => (eX j).1)
        (fun j => (eR j).1) eP eQ (1 + i) (by omega)]
      unfold directCount internalFirstNeighbors
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hBCard)]
    rw [show 7 = 3 + 4 by omega, Finset.sum_range_add]
    calc
      _ = (∑ i : Fin 3, (outB arc (1 + i.val)).toNat) +
          ∑ i : Fin 4, (outB arc (1 + (3 + i.val))).toNat := by
        exact congrArg₂ (· + ·)
          (Fin.sum_univ_eq_sum_range (fun i => (outB arc (1 + i)).toNat) 3).symm
          (Fin.sum_univ_eq_sum_range
            (fun i => (outB arc (1 + (3 + i))).toNat) 4).symm
      _ = (∑ i : Fin 3, directCount G C.B (eA1 i).1) +
          ∑ i : Fin 4, directCount G C.B (eX i).1 := by
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i _hi
          rw [toNat_outB G C (by omega) (by omega) hBCard C.a1
            (fun j => (eA1 j).1) (fun j => (eX j).1)
            (fun j => (eR j).1) eP eQ (1 + i.val) (by omega),
            localLabel_A1 (by omega) (by omega) C.a1
              (fun j => (eA1 j).1) (fun j => (eX j).1)
              (fun j => (eR j).1) (fun j => (eP j).1)
              (fun j => (eQ j).1) i i.isLt]
        · apply Finset.sum_congr rfl
          intro i _hi
          rw [toNat_outB G C (by omega) (by omega) hBCard C.a1
            (fun j => (eA1 j).1) (fun j => (eX j).1)
            (fun j => (eR j).1) eP eQ (1 + (3 + i.val)) (by omega)]
          have hidx : (⟨1 + (3 + i), by omega⟩ : Fin 14) =
              ⟨4 + i, by omega⟩ := by
            apply Fin.ext
            change 1 + (3 + i.val) = 4 + i.val
            omega
          rw [hidx, localLabel_X (by omega) (by omega) C.a1
            (fun j => (eA1 j).1) (fun j => (eX j).1)
            (fun j => (eR j).1) (fun j => (eP j).1)
            (fun j => (eQ j).1) i i.isLt]
      _ = edgeCount G C.A1 C.B + edgeCount G C.X C.B := by
        rw [Shared.edgeCount_eq_sum_fin G C.A1 C.B eA1,
          Shared.edgeCount_eq_sum_fin G C.X C.B eX]
      _ = edgeCount G C.H C.B := by
        rw [Digraph.LocalConfiguration.H,
          BSixKThree.edgeCount_source_union G C.A1 C.X C.B
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)]
  have hPWDecode :
      (sumCountsN 6 fun i => sumN 4 (externalArc i)).toNat =
        edgeCount G C.P (externalTargets G C) := by
    rw [toNat_sumCountsN_of_le 6 4 _ (by omega) (by
      intro i hi
      rw [toNat_sumN_eq_trueCount 4 _ (by omega)]
      exact trueCount_le 4 _)]
    calc
      _ = ∑ i : Fin 6, (sumN 4 (externalArc i.val)).toNat := by
        exact (Fin.sum_univ_eq_sum_range
          (fun i => (sumN 4 (externalArc i)).toNat) 6).symm
      _ = ∑ i : Fin 6,
          directCount G (externalTargets G C) (eP i).1 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [toNat_externalRow G C.P (externalTargets G C) eP eW
          (by omega) i.val i.isLt (by omega)]
      _ = edgeCount G C.P (externalTargets G C) :=
        (Shared.edgeCount_eq_sum_fin G C.P (externalTargets G C) eP).symm
  have hHPAggregate : (31 : BitVec 8).ule
      (sumCountsN 7 fun i => outB arc (1 + i)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rwa [hHPDecode]
  have hPWAggregate : (22 : BitVec 8).ule
      (sumCountsN 6 fun i => sumN 4 (externalArc i)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rwa [hPWDecode]
  rw [xFourCore]
  simpa only [Bool.and_eq_true] using
    ⟨⟨⟨⟨⟨⟨⟨hCore, hPivotAll⟩, hDegreeAll⟩, hReachX⟩, hReachB⟩,
      hReachW⟩, hHPAggregate⟩, hPWAggregate⟩

end SeymourEight.BSixKThreeCoreGraphBridge
