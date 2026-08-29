import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.HighDefect.NonSeymour
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGlobalBridge
import SeymourEight.Cases.BSevenKOne.Counting

set_option linter.style.header false

namespace SeymourEight.FourZHighDefectGraphBridge

open FourZHighDefect FourZHighDefectBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZExactGlobalBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem orientedSquare_coreBits_true
    (hG : G.IsOriented)
    (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0) (p i))
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i) (a 0))
    (hAH : ∀ i : Fin 4, a ⟨i + 1, by omega⟩ = h i)
    (hAR : ∀ i : Fin 3, a ⟨i + 5, by omega⟩ = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i) (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i) (z j)) :
    orientedSquare 19 (coreArc (coreBits G.Adj p h r z a)) = true := by
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
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (r : Fin 3 → V) (z : Fin 4 → V) (a : Fin 8 → V) :
    (FourZHighDefect.totalHToP (coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      r z a)).toNat = edgeCount G C.H C.P := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1) r z a
  rw [FourZHighDefect.totalHToP,
    FiveZExactGraphBridge.toNat_count_eq_fin_sum 28 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.H C.P h]
  simp_rw [directCount_eq_sum_fin G C.P p]
  simp only [Fin.sum_univ_succ]
  simp [aToP, hToP_coreBits, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
theorem totalMissingPZ_eq_rowSum (bits : BitVec 218) :
    FourZHighDefect.totalMissingPZ bits =
      sumCount 7 (fun i => count 4 fun j => !FourZHighDefect.pToZ bits i j) := by
  simp only [FourZHighDefect.totalMissingPZ, sumCount, count, bitCount,
    FourZHighDefect.pToZ]
  bv_decide

theorem totalMissingPZ_toNat_rows (bits : BitVec 218) :
    (FourZHighDefect.totalMissingPZ bits).toNat =
      ∑ i : Fin 7, ∑ j : Fin 4,
        if !FourZHighDefect.pToZ bits i j then 1 else 0 := by
  rw [totalMissingPZ_eq_rowSum,
    FiveZExactGlobalBridge.toNat_sumCount_of_le 7 4 _ (by omega) (by
      intro i hi
      rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 4 _ (by omega)]
      calc
        _ ≤ ∑ _j : Fin 4, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          split <;> omega
        _ = 4 := by simp)]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 4 _ (by omega)]

theorem totalMissingPZ_coreBits_toNat_add_edges (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (h : Fin 4 → V) (r : Fin 3 → V) (a : Fin 8 → V) :
    (FourZHighDefect.totalMissingPZ (coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) a)).toNat + edgeCount G C.P C.Z = 28 := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r (fun i ↦ (z i).1) a
  have hMissing : (FourZHighDefect.totalMissingPZ bits).toNat =
      ∑ i : Fin 7, ∑ j : Fin 4,
        if !FourZHighDefect.pToZ bits i j then 1 else 0 := by
    exact totalMissingPZ_toNat_rows bits
  rw [hMissing, edgeCount_eq_sum_fin G C.P C.Z p]
  simp_rw [directCount_eq_sum_fin G C.Z z]
  have hDecode : ∀ i : Fin 7, ∀ j : Fin 4,
      FourZHighDefect.pToZ bits i j = decide (G.Adj (p i).1 (z j).1) := by
    intro i j
    exact pToZ_coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) a i j i.isLt j.isLt
  simp_rw [hDecode]
  rw [← Finset.sum_add_distrib]
  have hComplement (b : Bool) :
      (if !b then 1 else 0) + (if b then 1 else 0) = 1 := by
    cases b <;> rfl
  calc
    (∑ i : Fin 7, ((∑ j : Fin 4,
          if !decide (G.Adj (p i).1 (z j).1) then 1 else 0) +
        ∑ j : Fin 4, if decide (G.Adj (p i).1 (z j).1) then 1 else 0)) =
        ∑ _i : Fin 7, 4 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      simp_rw [hComplement]
      simp
    _ = 28 := by simp

theorem every_Z_reached_from_P (C : G.LocalConfiguration)
    (z : V) (hz : z ∈ C.Z) : ∃ p ∈ C.P, G.Adj p z := by
  rcases Finset.mem_sdiff.mp hz with ⟨hzReach, _⟩
  exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp hzReach

end SeymourEight.FourZHighDefectGraphBridge
