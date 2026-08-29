import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.HighDefect.NonSeymour
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGlobalBridge
import SeymourEight.Cases.BSevenKOne.Counting

set_option linter.style.header false

namespace SeymourEight.ThreeZHighDefectGraphBridge

open ThreeZHighDefect ThreeZHighDefectBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZExactGlobalBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem orientedSquare_coreBits_true
    (hG : G.IsOriented)
    (p : Fin 7 → V) (h : Fin 5 → V) (r : Fin 2 → V)
    (z : Fin 3 → V) (a : Fin 8 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0) (p i))
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i) (a 0))
    (hAH : ∀ i : Fin 5, a ⟨i + 1, by omega⟩ = h i)
    (hAR : ∀ i : Fin 2, a ⟨i + 6, by omega⟩ = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 2, ¬G.Adj (p i) (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 3, ¬G.Adj (a i) (z j)) :
    orientedSquare 18 (coreArc (coreBits G.Adj p h r z a)) = true := by
  classical
  unfold orientedSquare
  rw [all_eq_true_iff]
  intro i hi
  simp only [Bool.and_eq_true]
  constructor
  · by_cases hi15 : i < 15
    · rw [coreArc_coreBits G p h r z a hA0P hP0 hAH hAR hPR hAZ i i hi15 hi]
      simpa using hG.1 (labelledVertex a p z i)
    · simp [coreArc, hi15, show ¬i < 8 by omega]
  · rw [all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    simp only [hij]
    by_cases hi15 : i < 15
    · by_cases hj15 : j < 15
      · rw [coreArc_coreBits G p h r z a hA0P hP0 hAH hAR hPR hAZ
          i j hi15 hj,
          coreArc_coreBits G p h r z a hA0P hP0 hAH hAR hPR hAZ
          j i hj15 hi]
        by_cases hijArc : G.Adj (labelledVertex a p z i) (labelledVertex a p z j)
        · simp [hijArc, hG.2 hijArc]
        · simp [hijArc]
      · simp [coreArc, hj15, show ¬j < 8 by omega]
    · simp [coreArc, hi15, show ¬i < 8 by omega]

theorem totalHToP_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (r : Fin 2 → V) (z : Fin 3 → V) (a : Fin 8 → V) :
    (ThreeZHighDefect.totalHToP (coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      r z a)).toNat = edgeCount G C.H C.P := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1) r z a
  rw [ThreeZHighDefect.totalHToP,
    FiveZExactGraphBridge.toNat_count_eq_fin_sum 35 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.H C.P h]
  simp_rw [directCount_eq_sum_fin G C.P p]
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_succ]
  simp [hToP_coreBits, Nat.add_assoc]

theorem totalPToH_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (r : Fin 2 → V) (z : Fin 3 → V) (a : Fin 8 → V) :
    (ThreeZHighDefect.totalPToH
      (coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1) r z a)).toNat =
      edgeCount G C.P C.H := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1) r z a
  rw [ThreeZHighDefect.totalPToH,
    FiveZExactGraphBridge.toNat_count_eq_fin_sum 35 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.P C.H p]
  simp_rw [directCount_eq_sum_fin G C.H h]
  simp only [Fin.sum_univ_succ]
  simp [pToH_coreBits, Nat.add_assoc]

theorem totalPOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 → V) (r : Fin 2 → V) (z : Fin 3 → V) (a : Fin 8 → V) :
    (ThreeZHighDefect.totalPOut
      (coreBits G.Adj (fun i ↦ (p i).1) h r z a)).toNat =
      edgeCount G C.P C.P := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r z a
  rw [ThreeZHighDefect.totalPOut,
    FiveZExactGraphBridge.toNat_count_eq_fin_sum 49 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.P C.P p]
  simp_rw [directCount_eq_sum_fin G C.P p]
  simp only [Fin.sum_univ_succ]
  simp [pArc_coreBits, Nat.add_assoc]

omit [Fintype V] [DecidableEq V] in
theorem orientedP_coreBits_true (hG : G.IsOriented)
    (p : Fin 7 → V) (h : Fin 5 → V) (r : Fin 2 → V)
    (z : Fin 3 → V) (a : Fin 8 → V) :
    orientedP (coreBits G.Adj p h r z a) = true := by
  classical
  rw [orientedP, orientedSquare, all_eq_true_iff]
  intro i hi
  simp only [Bool.and_eq_true]
  constructor
  · rw [pArc_coreBits G.Adj p h r z a i i (by omega) (by omega)]
    simpa using hG.1 (p ⟨i, by omega⟩)
  · rw [all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    rw [pArc_coreBits G.Adj p h r z a i j (by omega) (by omega),
      pArc_coreBits G.Adj p h r z a j i (by omega) (by omega)]
    by_cases ha : G.Adj (p ⟨i, by omega⟩) (p ⟨j, by omega⟩)
    · simp [hij, ha, hG.2 ha]
    · simp [hij, ha]

omit [Fintype V] [DecidableEq V] in
theorem orientedPH_coreBits_true (hG : G.IsOriented)
    (p : Fin 7 → V) (h : Fin 5 → V) (r : Fin 2 → V)
    (z : Fin 3 → V) (a : Fin 8 → V) :
    ThreeZHighDefect.orientedPH (coreBits G.Adj p h r z a) = true := by
  classical
  rw [ThreeZHighDefect.orientedPH, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [pToH_coreBits G.Adj p h r z a i j hi hj,
    hToP_coreBits G.Adj p h r z a j i hj hi]
  by_cases ha : G.Adj (p ⟨i, hi⟩) (h ⟨j, hj⟩)
  · simp [ha, hG.2 ha]
  · simp [ha]

set_option maxHeartbeats 1000000 in
theorem totalMissingPZ_eq_rowSum (bits : BitVec 218) :
    ThreeZHighDefect.totalMissingPZ bits =
      sumCount 7 (fun i => count 3 fun j => !ThreeZHighDefect.pToZ bits i j) := by
  simp only [ThreeZHighDefect.totalMissingPZ, sumCount, count, bitCount,
    ThreeZHighDefect.pToZ]
  bv_decide

theorem totalMissingPZ_toNat_rows (bits : BitVec 218) :
    (ThreeZHighDefect.totalMissingPZ bits).toNat =
      ∑ i : Fin 7, ∑ j : Fin 3,
        if !ThreeZHighDefect.pToZ bits i j then 1 else 0 := by
  rw [totalMissingPZ_eq_rowSum,
    FiveZExactGlobalBridge.toNat_sumCount_of_le 7 3 _ (by omega) (by
      intro i hi
      rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 3 _ (by omega)]
      calc
        _ ≤ ∑ _j : Fin 3, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          split <;> omega
        _ = 3 := by simp)]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 3 _ (by omega)]

theorem totalMissingPZ_coreBits_toNat_add_edges (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 3 ≃ {v : V // v ∈ C.Z})
    (h : Fin 5 → V) (r : Fin 2 → V) (a : Fin 8 → V) :
    (ThreeZHighDefect.totalMissingPZ (coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) a)).toNat + edgeCount G C.P C.Z = 21 := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r (fun i ↦ (z i).1) a
  have hMissing : (ThreeZHighDefect.totalMissingPZ bits).toNat =
      ∑ i : Fin 7, ∑ j : Fin 3,
        if !ThreeZHighDefect.pToZ bits i j then 1 else 0 := by
    exact totalMissingPZ_toNat_rows bits
  rw [hMissing, edgeCount_eq_sum_fin G C.P C.Z p]
  simp_rw [directCount_eq_sum_fin G C.Z z]
  have hDecode : ∀ i : Fin 7, ∀ j : Fin 3,
      ThreeZHighDefect.pToZ bits i j = decide (G.Adj (p i).1 (z j).1) := by
    intro i j
    exact pToZ_coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) a i j i.isLt j.isLt
  simp_rw [hDecode]
  rw [← Finset.sum_add_distrib]
  have hComplement (b : Bool) :
      (if !b then 1 else 0) + (if b then 1 else 0) = 1 := by
    cases b <;> rfl
  calc
    (∑ i : Fin 7, ((∑ j : Fin 3,
          if !decide (G.Adj (p i).1 (z j).1) then 1 else 0) +
        ∑ j : Fin 3, if decide (G.Adj (p i).1 (z j).1) then 1 else 0)) =
        ∑ _i : Fin 7, 3 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      simp_rw [hComplement]
      simp
    _ = 21 := by simp

theorem every_Z_reached_from_P (C : G.LocalConfiguration)
    (z : V) (hz : z ∈ C.Z) : ∃ p ∈ C.P, G.Adj p z := by
  rcases Finset.mem_sdiff.mp hz with ⟨hzReach, _⟩
  exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp hzReach

end SeymourEight.ThreeZHighDefectGraphBridge
