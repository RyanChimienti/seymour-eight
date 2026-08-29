import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.CommonBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.DefectBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  EffectiveBridge CommonBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem totalAOut_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) :
    (totalAOut (graphArc G L)).toNat = edgeCount G C.A C.A := by
  rw [totalAOut, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 8, (aOut (graphArc G L) i).toNat) =
      edgeCount G C.A C.A := by
    rw [edgeCount_eq_sum_fin G C.A C.A L.a, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact aOut_toNat G C L i i.isLt
  rw [hSum]
  have hCap := internal_edgeCount_le_choose_two G C.A hG
  have hACard : C.A.card = 8 := by
    simpa using (Fintype.card_congr L.a).symm
  rw [hACard] at hCap
  norm_num [Nat.choose] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem aMissing_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) :
    (aMissing (graphArc G L)).toNat = 28 - edgeCount G C.A C.A := by
  rw [aMissing, BitVec.toNat_sub, totalAOut_toNat G C L hG]
  have hCap := internal_edgeCount_le_choose_two G C.A hG
  have hACard : C.A.card = 8 := by
    simpa using (Fintype.card_congr L.a).symm
  rw [hACard] at hCap
  norm_num [Nat.choose] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.A C.A + 28) % 256) = _
  have hRewrite : 256 - edgeCount G C.A C.A + 28 =
      256 + (28 - edgeCount G C.A C.A) := by omega
  rw [hRewrite, Nat.add_mod]
  have hSmall : 28 - edgeCount G C.A C.A < 256 :=
    (Nat.sub_le 28 _).trans_lt (by omega)
  simp [Nat.mod_eq_of_lt hSmall]

theorem aMissing_toNat_le_four (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hACond : aConditions (graphArc G L) = true) :
    (aMissing (graphArc G L)).toNat ≤ 4 := by
  have hEach : ∀ i : Fin 8, 3 ≤ directCount G C.A (L.a i).1 := by
    rw [aConditions, all_eq_true_iff] at hACond
    intro i
    have hi := hACond i i.isLt
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq] at hi
    rw [← aOut_toNat G C L i i.isLt]
    exact hi.1.1
  have hLower : 24 ≤ edgeCount G C.A C.A := by
    rw [edgeCount_eq_sum_fin G C.A C.A L.a]
    calc
      24 = ∑ _i : Fin 8, 3 := by simp
      _ ≤ ∑ i : Fin 8, directCount G C.A (L.a i).1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hEach i
  rw [aMissing_toNat G C L hG]
  omega

theorem totalPOut_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) :
    (totalPOut (graphArc G L)).toNat = edgeCount G C.P C.P := by
  rw [totalPOut, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 6, (pOut (graphArc G L) i).toNat) =
      edgeCount G C.P C.P := by
    rw [edgeCount_eq_sum_fin G C.P C.P L.p, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P L.p
    intro j
    rw [pArc_graph G L i j i.isLt j.isLt]
    simp
  rw [hSum]
  have hCap := internal_edgeCount_le_choose_two G C.P hG
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hPCard] at hCap
  norm_num [Nat.choose] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem internalMissing_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) :
    (internalMissing (graphArc G L)).toNat = 15 - edgeCount G C.P C.P := by
  rw [internalMissing, BitVec.toNat_sub, totalPOut_toNat G C L hG]
  have hCap := internal_edgeCount_le_choose_two G C.P hG
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hPCard] at hCap
  norm_num [Nat.choose] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.P C.P + 15) % 256) = _
  have hRewrite : 256 - edgeCount G C.P C.P + 15 =
      256 + (15 - edgeCount G C.P C.P) := by omega
  rw [hRewrite, Nat.add_mod]
  have hSmall : 15 - edgeCount G C.P C.P < 256 :=
    (Nat.sub_le 15 _).trans_lt (by omega)
  simp [Nat.mod_eq_of_lt hSmall]

theorem totalPToH_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (totalPToH (graphArc G L)).toNat = edgeCount G C.P C.H := by
  rw [totalPToH, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 6, (pHOut (graphArc G L) i).toNat) =
      edgeCount G C.P C.H := by
    rw [edgeCount_eq_sum_fin G C.P C.H L.p, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact (pBlockCounts G C L hG hHCard (by omega) i i.isLt).2.1
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hPCard, hHCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem totalHToP_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hHCard : C.H.card = 7) :
    (totalHToP (graphArc G L)).toNat = edgeCount G C.H C.P := by
  rw [totalHToP, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 7, (hPOut (graphArc G L) i).toNat) =
      edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hLabelEquiv G C L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hLabelEquiv_val]
    exact hPOut_toNat G C L i i.isLt
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hPCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem hQDefect_toNat_le_seven (arc : Nat → Nat → Bool) :
    (hQDefect 1 arc).toNat ≤ 7 := by
  have hCount : (totalHToQ arc).toNat ≤ 7 := by
    rw [totalHToQ, toNat_count_eq_fin_sum 7 _ (by omega)]
    calc
      _ ≤ ∑ _i : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> omega
      _ = 7 := by simp
  rw [hQDefect, BitVec.toNat_sub]
  norm_num [BitVec.toNat_ofNat]
  omega

theorem two_aMissing_add_PToH_le_fifteen
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    2 * (aMissing (graphArc G L)).toNat + edgeCount G C.P C.H ≤ 15 := by
  have hDualLower := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true,
    BitVec.ule_eq_decide, decide_eq_true_eq] at hDualLower
  have hLower := hDualLower.1.1
  rw [totalHToP_toNat G C L hHCard] at hLower
  have hDefect := hQDefect_toNat_le_seven (graphArc G L)
  have hDelta := aMissing_toNat_le_four G C L hG hACond
  simp only [BitVec.toNat_add, BitVec.toNat_mul] at hLower
  norm_num [BitVec.toNat_ofNat] at hLower
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  rw [hTwo] at hLower
  have hRawSmall : 27 + 2 * (aMissing (graphArc G L)).toNat +
      (hQDefect 1 (graphArc G L)).toNat < 256 := by omega
  rw [Nat.mod_eq_of_lt hRawSmall] at hLower
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hPCard, hHCard] at hCross
  omega

theorem alpha_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    (alpha 1 (graphArc G L)).toNat =
      15 - 2 * (aMissing (graphArc G L)).toNat - edgeCount G C.P C.H := by
  have hDelta := aMissing_toNat_le_four G C L hG hACond
  have hCapacity := two_aMissing_add_PToH_le_fifteen G C L hG hHCard
    hACond hDual
  have hPToH : edgeCount G C.P C.H ≤ 15 -
      2 * (aMissing (graphArc G L)).toNat := by omega
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hFifteen : (15 : BitVec 8).toNat = 15 := by decide
  have hTwice : (2 * aMissing (graphArc G L)).toNat =
      2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_mul]
    rw [hTwo]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hInnerBV : 2 * aMissing (graphArc G L) ≤ (15 : BitVec 8) := by
    rw [BitVec.le_def, hTwice, hFifteen]
    omega
  have hFirst : ((15 : BitVec 8) - 2 * aMissing (graphArc G L)).toNat =
      15 - 2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_sub_of_le hInnerBV, hTwice]
    rw [hFifteen]
  have hOuterNat : (totalPToH (graphArc G L)).toNat ≤
      ((15 : BitVec 8) - 2 * aMissing (graphArc G L)).toNat := by
    rw [totalPToH_toNat G C L hG hHCard, hFirst]
    exact hPToH
  have hOuterBV : totalPToH (graphArc G L) ≤
      (15 : BitVec 8) - 2 * aMissing (graphArc G L) := by
    rw [BitVec.le_def]
    exact hOuterNat
  change ((((15 : BitVec 8) - 2 * aMissing (graphArc G L)) -
    totalPToH (graphArc G L)).toNat) = _
  rw [BitVec.toNat_sub_of_le hOuterBV, hFirst,
    totalPToH_toNat G C L hG hHCard]

theorem defectCapacity_le_six (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat +
          (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat ≤ 6 := by
  have hAlpha := alpha_toNat G C L hG hHCard hACond hDual
  have hDelta := aMissing_toNat_le_four G C L hG hACond
  have hPToHCapacity := two_aMissing_add_PToH_le_fifteen G C L hG hHCard
    hACond hDual
  have hBeta := internalMissing_toNat G C L hG
  have hM := externalMissing_toNat G C L hG hHCard 1 hy
    (Or.inr rfl) (by omega)
  have hAlphaLe : (alpha 1 (graphArc G L)).toNat ≤ 15 := by omega
  have hBetaLe : (internalMissing (graphArc G L)).toNat ≤ 15 := by omega
  have hD : (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat =
      (alpha 1 (graphArc G L)).toNat +
        (internalMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hQ := qSingleton G C L
  have hAuxRaw := auxiliarySet_eq G C L 1 hy (Or.inr rfl)
  have hAux : auxiliarySet G C = C.Q ∪ (externalTargets G C) := by
    simpa [hQ] using hAuxRaw
  have hAccount := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hMinSum : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    have hPCard : C.P.card = 6 := by
      simpa using (Fintype.card_congr L.p).symm
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hDis : Disjoint C.Q (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvZ
  have hAuxCap := edgeCount_le_card_mul_card G C.P (C.Q ∪ (externalTargets G C))
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 1 := by
    simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = 3 := by
    simpa using (Fintype.card_congr L.z).symm
  rw [hPCard, Finset.card_union_of_disjoint hDis, hQCard, hZCard] at hAuxCap
  rw [edgeCount_union_of_disjoint G C.P C.Q (externalTargets G C) hDis] at hAuxCap
  have hPPcap := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hPPcap
  norm_num [Nat.choose] at hPPcap
  have hAlphaEq : (alpha 1 (graphArc G L)).toNat +
      2 * (aMissing (graphArc G L)).toNat + edgeCount G C.P C.H = 15 := by
    omega
  have hBetaEq : (internalMissing (graphArc G L)).toNat +
      edgeCount G C.P C.P = 15 := by
    omega
  rw [hAux, edgeCount_union_of_disjoint G C.P C.Q (externalTargets G C) hDis] at hM
  have hMEq :
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) = 24 := by
    omega
  rw [hD]
  omega

theorem capacityDefect_le_six_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    (capacityDefect (graphArc G L) (graphPToZ G L)).ule 6 = true := by
  have hCap := defectCapacity_le_six G C L hG hMin hHCard hy hACond hDual
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hTwice : (2 * aMissing (graphArc G L)).toNat =
      2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_mul, hTwo, Nat.mod_eq_of_lt (by omega)]
  have hFirst :
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
        2 * aMissing (graphArc G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_add, hTwice, Nat.mod_eq_of_lt (by omega)]
  have hTotal :
      (capacityDefect (graphArc G L) (graphPToZ G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat +
          (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat := by
    unfold capacityDefect
    rw [BitVec.toNat_add, hFirst, Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  have hSix : (6 : BitVec 8).toNat = 6 := by decide
  rw [hTotal, hSix]
  exact hCap

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.DefectBridge
