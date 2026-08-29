import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.CommonBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ProbeReachedTwo

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ReachedCountsBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  EffectiveBridge CommonBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem totalAOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    (totalAOut (graphArc G L)).toNat = edgeCount G C.A C.A := by
  rw [totalAOut, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 8, (aOut (graphArc G L) i).toNat) =
      edgeCount G C.A C.A := by
    rw [edgeCount_eq_sum_fin G C.A C.A L.a,
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact aOut_toNat G C L i i.isLt
  rw [hSum]
  have hCap := internal_edgeCount_le_choose_two G C.A hG
  have hACard : C.A.card = 8 := by
    simpa using (Fintype.card_congr L.a).symm
  rw [hACard] at hCap
  norm_num [Nat.choose] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem aMissing_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
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
  have hSmall : 28 - edgeCount G C.A C.A < 256 := by omega
  simp [Nat.mod_eq_of_lt hSmall]

theorem aMissing_toNat_le_four {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hACond : aConditions (graphArc G L) = true) :
    (aMissing (graphArc G L)).toNat ≤ 4 := by
  have hEach : ∀ i : Fin 8, 3 ≤ directCount G C.A (L.a i).1 := by
    rw [aConditions, all_eq_true_iff] at hACond
    intro i
    have hi := hACond i i.isLt
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide,
      decide_eq_true_eq] at hi
    rw [← aOut_toNat G C L i i.isLt]
    exact hi.1.1
  have hLower : 24 ≤ edgeCount G C.A C.A := by
    rw [edgeCount_eq_sum_fin G C.A C.A L.a]
    calc
      24 = ∑ _i : Fin 8, 3 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        exact hEach i
  rw [aMissing_toNat G C L hG]
  omega

theorem totalPToH_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hHCard : C.H.card = 7) (hzSmall : zCount < 256) :
    (totalPToH (graphArc G L)).toNat = edgeCount G C.P C.H := by
  rw [totalPToH, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 6,
      (pHOut (graphArc G L) i).toNat) = edgeCount G C.P C.H := by
    rw [edgeCount_eq_sum_fin G C.P C.H L.p,
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact (pBlockCounts G C L hG hHCard hzSmall i i.isLt).2.1
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hPCard, hHCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem totalHToP_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7) :
    (totalHToP (graphArc G L)).toNat = edgeCount G C.H C.P := by
  rw [totalHToP, EffectiveBridge.toNat_sumCount]
  have hSum : (∑ i ∈ Finset.range 7,
      (hPOut (graphArc G L) i).toNat) = edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hLabelEquiv G C L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
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
        intro i _
        split <;> omega
      _ = 7 := by simp
  rw [hQDefect, BitVec.toNat_sub]
  norm_num [BitVec.toNat_ofNat]
  omega

theorem reached_counts (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hy : BSevenKThree.y G C = 1)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    externalMissing 1 2 (graphArc G L) (graphPToZ G L) = 0 ∧
      totalPToH (graphArc G L) = 15 ∧
      totalHToP (graphArc G L) = 27 := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hAuxCard := auxiliarySet_card G C L 1 hy (Or.inr rfl)
  have hAuxCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  rw [hPCard, hAuxCard] at hAuxCap
  have hPLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hInternal := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hInternal
  norm_num [Nat.choose] at hInternal
  have hAuxEq := edgeCount_P_auxiliary_eq G C
  have hPHLower : 15 ≤ edgeCount G C.P C.H := by omega
  have hDelta := aMissing_toNat_le_four G C L hG hACond
  have hQLe := hQDefect_toNat_le_seven (graphArc G L)
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true,
    BitVec.ule_eq_decide, decide_eq_true_eq] at hDualParts
  have hHPLower := hDualParts.1.1
  rw [totalHToP_toNat G C L hHCard] at hHPLower
  simp only [BitVec.toNat_add, BitVec.toNat_mul] at hHPLower
  norm_num [BitVec.toNat_ofNat] at hHPLower
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  rw [hTwo] at hHPLower
  have hRawSmall : 27 + 2 * (aMissing (graphArc G L)).toNat +
      (hQDefect 1 (graphArc G L)).toNat < 256 := by omega
  rw [Nat.mod_eq_of_lt hRawSmall] at hHPLower
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPH : edgeCount G C.P C.H = 15 := by omega
  have hHP : edgeCount G C.H C.P = 27 := by omega
  have hAux : edgeCount G C.P (auxiliarySet G C) = 18 := by omega
  have hExtNat := externalMissing_toNat G C L hG hHCard 1 hy
    (Or.inr rfl) (by omega)
  have hExtValue :
      (externalMissing 1 2 (graphArc G L) (graphPToZ G L)).toNat = 0 := by
    omega
  have hExt : externalMissing 1 2 (graphArc G L) (graphPToZ G L) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hExtValue
  have hPHBV : totalPToH (graphArc G L) = 15 := by
    apply BitVec.eq_of_toNat_eq
    rw [totalPToH_toNat G C L hG hHCard (by omega), hPH]
    decide
  have hHPBV : totalHToP (graphArc G L) = 27 := by
    apply BitVec.eq_of_toNat_eq
    rw [totalHToP_toNat G C L hHCard, hHP]
    decide
  exact ⟨hExt, hPHBV, hHPBV⟩

theorem reachedTwoDirectCore_true_of_common
    (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hy : BSevenKThree.y G C = 1)
    (hCommon : commonCore 1 2 (graphArc G L) (graphPToZ G L) = true) :
    reachedTwoDirectCore (graphArc G L) (graphPToZ G L) = true := by
  have hParts := hCommon
  simp only [commonCore, Bool.and_eq_true] at hParts
  have hChain22 := hParts.1
  have hOrderedA := hChain22.2
  have hChain21 := hChain22.1
  have hChain20 := hChain21.1
  have hChain19 := hChain20.1
  have hChain18 := hChain19.1
  have hChain17 := hChain18.1
  have hDegreeDual := hChain17.2
  have hChain16 := hChain17.1
  have hChain15 := hChain16.1
  have hChain14 := hChain15.1
  have hChain13 := hChain14.1
  have hANonSeymour := hChain13.2
  have hChain12 := hChain13.1
  have hPConditions := hChain12.2
  have hChain11 := hChain12.1
  have hAConditions := hChain11.2
  have hChain10 := hChain11.1
  have hQReach := hChain10.2
  have hChain9 := hChain10.1
  have hChain8 := hChain9.1
  have hEveryZ := hChain8.2
  have hChain7 := hChain8.1
  have hChain6 := hChain7.1
  have hChain5 := hChain6.1
  have hNoP := hChain5.2
  have hChain4 := hChain5.1
  have hFixed := hChain4.2
  have hChain3 := hChain4.1
  have hOPH := hChain3.2
  have hChain2 := hChain3.1
  have hOP := hChain2.2
  have hOA := hChain2.1
  have hCounts := reached_counts G C L hG hMin hHCard hy hAConditions
    hDegreeDual
  have hRow :
      (projectedSecondCount 2 (graphArc G L) (graphPToZ G L) 7).ult
        (aDegree (graphArc G L) 7) = true := by
    simp only [aNonSeymour, all_eq_true_iff] at hANonSeymour
    exact hANonSeymour 7 (by omega)
  rcases hCounts with ⟨hExt, hPToH, hHToP⟩
  simp only [reachedTwoDirectCore, Bool.and_eq_true]
  aesop

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ReachedCountsBridge
