import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.FixedA

set_option linter.style.header false

/-! Label-independent accounting fields for `CompatibleRowData`. -/

namespace SeymourEight.FourZExactSevenAccounting

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge
  FiveZExactGlobalBridge FiveZExactPBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem missing_le_one (C : G.LocalConfiguration) (missing : Nat)
    (hMissing : missing = 28 - edgeCount G C.P C.Z)
    (hBound : 28 - edgeCount G C.P C.Z ≤ 1) : missing ≤ 1 := by omega

theorem pz_count (C : G.LocalConfiguration) (missing : Nat)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hMissing : missing = 28 - edgeCount G C.P C.Z) :
    edgeCount G C.P C.Z + missing = 28 := by
  have hUpper := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hUpper
  omega

theorem degreeSum_eq (C : G.LocalConfiguration) (degreeSum : Nat) :
    (∑ u ∈ C.P, G.outdegree u = degreeSum) ↔
      degreeSum = ∑ u ∈ C.P, G.outdegree u := by omega

private def missingPairIndicator (p : Fin 7 → V) (i j : Fin 7) : Nat :=
  if ¬G.Adj (p i) (p j) ∧ ¬G.Adj (p j) (p i) then 1 else 0

private def arcIndicator (p : Fin 7 → V) (i j : Fin 7) : Nat :=
  if G.Adj (p i) (p j) then 1 else 0

private def pairTotal (p : Fin 7 → V) (i j : Fin 7) : Nat :=
  missingPairIndicator G p i j + arcIndicator G p i j +
    arcIndicator G p j i

omit [Fintype V] [DecidableEq V] in
private theorem pairTotal_eq_one (hG : G.IsOriented) (p : Fin 7 → V)
    (i j : Fin 7) : pairTotal G p i j = 1 := by
  classical
  by_cases hf : G.Adj (p i) (p j)
  · have hr : ¬G.Adj (p j) (p i) := hG.2 hf
    simp [pairTotal, missingPairIndicator, arcIndicator, hf, hr]
  · by_cases hr : G.Adj (p j) (p i) <;>
      simp [pairTotal, missingPairIndicator, arcIndicator, hf, hr]

private theorem sum_fin49_eq_blocks (f : Fin 49 → Nat) :
    (∑ q, f q) = ∑ i : Fin 7, ∑ j : Fin 7,
      f ⟨i * 7 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 7 × Fin 7 ≃ Fin 49).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

set_option maxHeartbeats 4000000 in
theorem totalMissingPPairs_toNat_add_edges (C : G.LocalConfiguration)
    (hG : G.IsOriented) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V) :
    (FourZExactSeven.totalMissingPPairs
      (coreBits G.Adj (fun j ↦ (p j).1) h a z w)).toNat +
      edgeCount G C.P C.P = 21 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h a z w
  let pv : Fin 7 → V := fun i ↦ (p i).1
  have hMissing : (FourZExactSeven.totalMissingPPairs bits).toNat =
      missingPairIndicator G pv 0 1 + missingPairIndicator G pv 0 2 +
      missingPairIndicator G pv 0 3 + missingPairIndicator G pv 0 4 +
      missingPairIndicator G pv 0 5 + missingPairIndicator G pv 0 6 +
      missingPairIndicator G pv 1 2 + missingPairIndicator G pv 1 3 +
      missingPairIndicator G pv 1 4 + missingPairIndicator G pv 1 5 +
      missingPairIndicator G pv 1 6 + missingPairIndicator G pv 2 3 +
      missingPairIndicator G pv 2 4 + missingPairIndicator G pv 2 5 +
      missingPairIndicator G pv 2 6 + missingPairIndicator G pv 3 4 +
      missingPairIndicator G pv 3 5 + missingPairIndicator G pv 3 6 +
      missingPairIndicator G pv 4 5 + missingPairIndicator G pv 4 6 +
      missingPairIndicator G pv 5 6 := by
    rw [FourZExactSeven.totalMissingPPairs,
      toNat_count_eq_fin_sum 49 _ (by omega)]
    rw [sum_fin49_eq_blocks]
    simp only [Fin.sum_univ_succ]
    simp [bits, pv, FourZExactSevenBridge.pArc_coreBits,
      missingPairIndicator, Bool.and_eq_true,
      decide_eq_false_iff_not,
      Nat.add_assoc]
  have hl0 : ¬G.Adj (p 0).1 (p 0).1 := hG.1 _
  have hl1 : ¬G.Adj (p 1).1 (p 1).1 := hG.1 _
  have hl2 : ¬G.Adj (p 2).1 (p 2).1 := hG.1 _
  have hl3 : ¬G.Adj (p 3).1 (p 3).1 := hG.1 _
  have hl4 : ¬G.Adj (p 4).1 (p 4).1 := hG.1 _
  have hl5 : ¬G.Adj (p 5).1 (p 5).1 := hG.1 _
  have hl6 : ¬G.Adj (p 6).1 (p 6).1 := hG.1 _
  have hEdges : edgeCount G C.P C.P =
      arcIndicator G pv 0 1 + arcIndicator G pv 0 2 +
      arcIndicator G pv 0 3 + arcIndicator G pv 0 4 +
      arcIndicator G pv 0 5 + arcIndicator G pv 0 6 +
      arcIndicator G pv 1 0 + arcIndicator G pv 1 2 +
      arcIndicator G pv 1 3 + arcIndicator G pv 1 4 +
      arcIndicator G pv 1 5 + arcIndicator G pv 1 6 +
      arcIndicator G pv 2 0 + arcIndicator G pv 2 1 +
      arcIndicator G pv 2 3 + arcIndicator G pv 2 4 +
      arcIndicator G pv 2 5 + arcIndicator G pv 2 6 +
      arcIndicator G pv 3 0 + arcIndicator G pv 3 1 +
      arcIndicator G pv 3 2 + arcIndicator G pv 3 4 +
      arcIndicator G pv 3 5 + arcIndicator G pv 3 6 +
      arcIndicator G pv 4 0 + arcIndicator G pv 4 1 +
      arcIndicator G pv 4 2 + arcIndicator G pv 4 3 +
      arcIndicator G pv 4 5 + arcIndicator G pv 4 6 +
      arcIndicator G pv 5 0 + arcIndicator G pv 5 1 +
      arcIndicator G pv 5 2 + arcIndicator G pv 5 3 +
      arcIndicator G pv 5 4 + arcIndicator G pv 5 6 +
      arcIndicator G pv 6 0 + arcIndicator G pv 6 1 +
      arcIndicator G pv 6 2 + arcIndicator G pv 6 3 +
      arcIndicator G pv 6 4 + arcIndicator G pv 6 5 := by
    rw [edgeCount_eq_sum_fin G C.P C.P p]
    simp_rw [directCount_eq_sum_fin G C.P p]
    simp only [Fin.sum_univ_succ]
    simp [pv, arcIndicator, hl0, hl1, hl2, hl3, hl4, hl5, hl6,
      Nat.add_assoc]
  have h01 := pairTotal_eq_one G hG pv 0 1
  have h02 := pairTotal_eq_one G hG pv 0 2
  have h03 := pairTotal_eq_one G hG pv 0 3
  have h04 := pairTotal_eq_one G hG pv 0 4
  have h05 := pairTotal_eq_one G hG pv 0 5
  have h06 := pairTotal_eq_one G hG pv 0 6
  have h12 := pairTotal_eq_one G hG pv 1 2
  have h13 := pairTotal_eq_one G hG pv 1 3
  have h14 := pairTotal_eq_one G hG pv 1 4
  have h15 := pairTotal_eq_one G hG pv 1 5
  have h16 := pairTotal_eq_one G hG pv 1 6
  have h23 := pairTotal_eq_one G hG pv 2 3
  have h24 := pairTotal_eq_one G hG pv 2 4
  have h25 := pairTotal_eq_one G hG pv 2 5
  have h26 := pairTotal_eq_one G hG pv 2 6
  have h34 := pairTotal_eq_one G hG pv 3 4
  have h35 := pairTotal_eq_one G hG pv 3 5
  have h36 := pairTotal_eq_one G hG pv 3 6
  have h45 := pairTotal_eq_one G hG pv 4 5
  have h46 := pairTotal_eq_one G hG pv 4 6
  have h56 := pairTotal_eq_one G hG pv 5 6
  simp only [pairTotal] at h01 h02 h03 h04 h05 h06 h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
  rw [hMissing, hEdges]
  omega

theorem defectIdentity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 3)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing degreeSum : Nat)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (hPZCount : edgeCount G C.P C.Z + missing = 28)
    (hDegreeSum : ∑ u ∈ C.P, G.outdegree u = degreeSum) :
    totalMissingPPairs (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) a z w) +
      (14 - totalPToH (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) a z w)) =
      BitVec.ofNat 8 (63 - missing - degreeSum) := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
  have hPTotalNat := totalPToH_toNat G C p h a z w
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hHTotalLower : 14 ≤ edgeCount G C.H C.P := by
    have hc := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB
      hRootDegree hk
    simpa [hx, Nat.choose] using hc
  have hPTotalUpper : edgeCount G C.P C.H ≤ 14 := by
    have hc := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hc
    omega
  have hMissingNat := totalMissingPPairs_toNat_add_edges G C hG p
    (fun j ↦ (h j).1) a z w
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ u ∈ C.P, epsilonAt G u C.s = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [epsilonAt, no_P_to_s_of_epsilonS_zero G C hEpsilon u hu]
  rw [hNoRoot, hDegreeSum] at hAccounting
  have hmLe : (totalMissingPPairs bits).toNat ≤ 21 := by
    change (totalMissingPPairs bits).toNat + edgeCount G C.P C.P = 21
      at hMissingNat
    omega
  have hDegreeUpper : missing + degreeSum ≤ 63 := by
    omega
  have hMissingEquation :
      (totalMissingPPairs bits).toNat + edgeCount G C.P C.P = 21 := by
    exact hMissingNat
  have hNatIdentity : (totalMissingPPairs bits).toNat +
      (14 - edgeCount G C.P C.H) = 63 - missing - degreeSum := by
    omega
  apply BitVec.eq_of_toNat_eq
  have hSubNat : (14 - totalPToH bits).toNat =
      14 - edgeCount G C.P C.H := by
    have hle : (totalPToH bits).toNat ≤ 14 := by
      rw [hPTotalNat]
      exact hPTotalUpper
    have hleBV : totalPToH bits ≤ (14 : BitVec 8) := by
      rw [BitVec.le_def]
      simpa using hle
    rw [BitVec.toNat_sub_of_le hleBV, hPTotalNat]
    rfl
  rw [BitVec.toNat_add, hSubNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hNatIdentity

theorem degreeBytes (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (missing degreeSum : Nat)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (hPZRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hDegreeSum : ∑ u ∈ C.P, G.outdegree u = degreeSum) :
    sumCount 7 (pDegree missing (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) a z w)) = BitVec.ofNat 8 degreeSum := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
  have hPoint : ∀ i : Nat, (hi : i < 7) →
      (pDegree missing bits i).toNat = G.outdegree (p ⟨i, hi⟩).1 := by
    intro i hi
    exact pDegree_toNat G C hG hPB hEpsilon missing p h a z w hPZRows i hi
  have hDegreeCap : ∀ i < 7, (pDegree missing bits i).toNat ≤ 15 := by
    intro i hi
    rw [hPoint i hi]
    rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon _
      (p ⟨i, hi⟩).2]
    have hZ : directCount G C.Z (p ⟨i, hi⟩).1 ≤ 4 := by
      rw [hPZRows i hi]
      split <;> omega
    have hH : directCount G C.H (p ⟨i, hi⟩).1 ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr h).symm)
    have hP : directCount G C.P (p ⟨i, hi⟩).1 ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr p).symm)
    omega
  have hDegreeSmall : degreeSum < 256 := by
    rw [← hDegreeSum, sum_finset_eq_sum_fin C.P p G.outdegree]
    calc
      (∑ i : Fin 7, G.outdegree (p i).1) ≤ ∑ _i : Fin 7, 15 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← hPoint i i.isLt]
        exact hDegreeCap i i.isLt
      _ = 105 := by simp
      _ < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sumCount_of_le 7 15 _ (by omega) hDegreeCap]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin 7, (pDegree missing bits i).toNat) =
        ∑ i : Fin 7, G.outdegree (p i).1 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hPoint i i.isLt
    _ = ∑ u ∈ C.P, G.outdegree u :=
      (sum_finset_eq_sum_fin C.P p G.outdegree).symm
    _ = degreeSum := hDegreeSum
    _ = (BitVec.ofNat 8 degreeSum).toNat := by
      simp only [BitVec.toNat_ofNat]
      symm
      exact Nat.mod_eq_of_lt hDegreeSmall

end SeymourEight.FourZExactSevenAccounting
