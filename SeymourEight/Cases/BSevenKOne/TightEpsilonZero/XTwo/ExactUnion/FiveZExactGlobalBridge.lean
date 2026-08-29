import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactPBridge
import SeymourEight.Cases.BSevenKOne.Counting

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Global constraints for the exact five-`Z` certificate

This module handles the constraints which are not individual non-Seymour
rows: orientation, the structural eight-vertex graph on `A`, coverage of the
exact external union, and the forced outgoing `H → P` arcs.
-/

namespace SeymourEight.FiveZExactGlobalBridge

open FiveZExactRisk FiveZExactCoreBridge FiveZExactGraphBridge
  FiveZExactHBridge FiveZExactPBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hBefore, hLast⟩ i hi
        by_cases hin : i < n
        · exact hBefore i hin
        · have : i = n := by omega
          exact this ▸ hLast
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

omit [Fintype V] [DecidableEq V] in
theorem orientedSquare_coreBits_true
    (R : V → V → Prop) [DecidableRel R]
    (hLoopless : ∀ v, ¬R v v)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V) :
    orientedSquare 7 (pArc (coreBits R p h z w a)) = true ∧
      orientedSquare 5 (zArc (coreBits R p h z w a)) = true ∧
        orientedSquare 8 (aArc (coreBits R p h z w a)) = true := by
  classical
  have square (n : Nat) (hn : n = 7 ∨ n = 5 ∨ n = 8)
      (label : Fin n → V) (arc : Nat → Nat → Bool)
      (hArc : ∀ i j : Nat, (hi : i < n) → (hj : j < n) →
        arc i j = decide (R (label ⟨i, hi⟩) (label ⟨j, hj⟩))) :
      orientedSquare n arc = true := by
    rw [orientedSquare, all_eq_true_iff]
    intro i hi
    simp only [Bool.and_eq_true]
    constructor
    · rw [hArc i i hi hi]
      simp [hLoopless]
    · rw [all_eq_true_iff]
      intro j hj
      rw [hArc i j hi hj, hArc j i hj hi]
      by_cases hij : i = j
      · simp [hij]
      · by_cases hForward : R (label ⟨i, hi⟩) (label ⟨j, hj⟩)
        · have hReverse : ¬R (label ⟨j, hj⟩) (label ⟨i, hi⟩) :=
            hAnti _ _ hForward
          simp [hij, hForward, hReverse]
        · simp [hij, hForward]
  exact ⟨
    square 7 (Or.inl rfl) p _ (pArc_coreBits R p h z w a),
    square 5 (Or.inr (Or.inl rfl)) z _ (zArc_coreBits R p h z w a),
    square 8 (Or.inr (Or.inr rfl)) a _ (aArc_coreBits R p h z w a)⟩

omit [Fintype V] [DecidableEq V] in
theorem orientedCross_coreBits_true
    (R : V → V → Prop) [DecidableRel R]
    (hAnti : ∀ u v, R u v → ¬R v u)
    (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V) :
    orientedPH (coreBits R p h z w a) = true ∧
      orientedPZ (coreBits R p h z w a) = true := by
  classical
  constructor
  · rw [orientedPH, all_eq_true_iff]
    intro i hi
    rw [all_eq_true_iff]
    intro j hj
    rw [pToH_coreBits R p h z w a i j hi hj,
      hToP_coreBits R p h z w a j i hj hi]
    by_cases hForward : R (p ⟨i, hi⟩) (h ⟨j, hj⟩)
    · have hReverse : ¬R (h ⟨j, hj⟩) (p ⟨i, hi⟩) :=
        hAnti _ _ hForward
      simp [hForward, hReverse]
    · simp [hForward]
  · rw [orientedPZ, all_eq_true_iff]
    intro i hi
    rw [all_eq_true_iff]
    intro j hj
    rw [pToZ_coreBits R p h z w a i j hi hj,
      zToP_coreBits R p h z w a j i hj hi]
    by_cases hForward : R (p ⟨i, hi⟩) (z ⟨j, hj⟩)
    · have hReverse : ¬R (z ⟨j, hj⟩) (p ⟨i, hi⟩) :=
        hAnti _ _ hForward
      simp [hForward, hReverse]
    · simp [hForward]

theorem exactWCoverage_coreBits_true (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) :
    all 6 (fun wi => any 5 fun zi =>
      zToW (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) zi wi) = true := by
  rw [all_eq_true_iff]
  intro wi hwi
  have hwUnion := (Finset.mem_sdiff.mp (w ⟨wi, hwi⟩).2).1
  obtain ⟨zv, hz, hAdj⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwUnion
  obtain ⟨zi, hzi⟩ := z.surjective ⟨zv, hz⟩
  rw [any_eq_true_iff]
  refine ⟨zi, zi.isLt, ?_⟩
  rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a zi wi zi.isLt hwi]
  have : (z zi).1 = zv := congrArg Subtype.val hzi
  simpa [this] using hAdj

theorem hPOut_positive_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hACard : C.A.card = 8) :
    all 3 (fun hi => (1 : BitVec 8).ule
      (hPOut (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        z w a) hi)) = true := by
  rw [all_eq_true_iff]
  intro i hi
  have hPNat :
      (hPOut (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        z w a) i).toNat = directCount G C.P (h ⟨i, hi⟩).1 := by
    rw [hPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P p
    intro j
    rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a i j hi j.isLt]
    simp
  have hDegree := H_outdegree_eq_A_add_P G C hG hPB
    (h ⟨i, hi⟩).1 (h ⟨i, hi⟩).2
  have hALe : directCount G C.A (h ⟨i, hi⟩).1 ≤ 7 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    calc
      (C.A.filter (G.Adj (h ⟨i, hi⟩).1)).card ≤
          (C.A.erase (h ⟨i, hi⟩).1).card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvA, huv⟩
        exact Finset.mem_erase.mpr
          ⟨fun hvu ↦ hG.1 _ (hvu ▸ huv), hvA⟩
      _ = 7 := by
        rw [Finset.card_erase_of_mem
          (Digraph.LocalConfiguration.H_subset_A (G := G) C
            (h ⟨i, hi⟩).2), hACard]
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hPNat]
  change 1 ≤ directCount G C.P (h ⟨i, hi⟩).1
  have := hMin (h ⟨i, hi⟩).1
  omega

omit [DecidableEq V] in
theorem aOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V) (w : Fin 6 → V)
    (a : Fin 8 ≃ {v : V // v ∈ C.A}) (source : Nat) (hs : source < 8) :
    (aOut (coreBits G.Adj p h z w (fun j ↦ (a j).1)) source).toNat =
      directCount G C.A (a ⟨source, hs⟩).1 := by
  classical
  rw [aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A a
  intro j
  rw [aArc_coreBits G.Adj p h z w (fun j ↦ (a j).1)
    source j hs j.isLt]
  simp

theorem totalHToP_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (z : Fin 5 → V) (w : Fin 6 → V) (a : Fin 8 → V) :
    (totalHToP (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a)).toNat = edgeCount G C.H C.P := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) z w a
  rw [totalHToP, toNat_count_eq_fin_sum 21 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.H C.P h]
  simp_rw [directCount_eq_sum_fin G C.P p]
  simp only [Fin.sum_univ_succ]
  simp [hToP_coreBits, Nat.add_assoc]

theorem toNat_sumCount_of_le (n cap : Nat) (f : Nat → BitVec 8)
    (hTotal : n * cap < 256) (hf : ∀ i < n, (f i).toNat ≤ cap) :
    (sumCount n f).toNat = ∑ i ∈ Finset.range n, (f i).toNat := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [Nat.succ_mul] at hTotal
      have hnTotal : n * cap < 256 := by omega
      have hSumLe : (∑ i ∈ Finset.range n, (f i).toNat) ≤ n * cap := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, cap := by
            apply Finset.sum_le_sum
            intro i hi
            exact hf i (by
              have := Finset.mem_range.mp hi
              omega)
          _ = n * cap := by simp
      rw [sumCount, BitVec.toNat_add,
        ih hnTotal (fun i hi ↦ hf i (by omega)), Finset.sum_range_succ]
      apply Nat.mod_eq_of_lt
      have := hf n (by omega)
      omega

set_option maxHeartbeats 1000000 in
-- Bit-blasting this representation identity can exceed the default budget.
theorem totalMissingPZ_eq_rowSum (bits : BitVec 280) :
    totalMissingPZ bits =
      sumCount 7 (fun i => count 5 fun z => !pToZ bits i z) := by
  simp only [totalMissingPZ, sumCount, count, bitCount, pToZ]
  bv_decide

theorem totalMissingPZ_toNat_rows (bits : BitVec 280) :
    (totalMissingPZ bits).toNat =
      ∑ i : Fin 7, ∑ j : Fin 5, if !pToZ bits i j then 1 else 0 := by
  rw [totalMissingPZ_eq_rowSum, toNat_sumCount_of_le 7 5 _ (by omega) (by
    intro i hi
    rw [toNat_count_eq_fin_sum 5 _ (by omega)]
    calc
      _ ≤ ∑ _j : Fin 5, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        split <;> omega
      _ = 5 := by simp)]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [toNat_count_eq_fin_sum 5 _ (by omega)]

theorem totalMissingPZ_coreBits_toNat_add_edges (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (h : Fin 3 → V) (w : Fin 6 → V) (a : Fin 8 → V) :
    (totalMissingPZ (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a)).toNat + edgeCount G C.P C.Z = 35 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) w a
  change (totalMissingPZ bits).toNat + edgeCount G C.P C.Z = 35
  rw [totalMissingPZ_toNat_rows]
  rw [edgeCount_eq_sum_fin G C.P C.Z p]
  simp_rw [directCount_eq_sum_fin G C.Z z]
  have hDecode : ∀ i : Fin 7, ∀ j : Fin 5,
      pToZ bits i j = decide (G.Adj (p i).1 (z j).1) := by
    intro i j
    exact pToZ_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a i j i.isLt j.isLt
  simp_rw [hDecode]
  rw [← Finset.sum_add_distrib]
  have hComplement (b : Bool) :
      (if !b then 1 else 0) + (if b then 1 else 0) = 1 := by
    cases b <;> rfl
  calc
    (∑ i : Fin 7, ((∑ j : Fin 5,
          if !decide (G.Adj (p i).1 (z j).1) then 1 else 0) +
        ∑ j : Fin 5, if decide (G.Adj (p i).1 (z j).1) then 1 else 0)) =
        ∑ _i : Fin 7, 5 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      simp_rw [hComplement]
      simp
    _ = 35 := by simp

/-- Five `Z` vertices and at most three missing `P → Z` incidences force
at least six distinct external `Z`-outneighbors. -/
theorem six_le_zExternalUnion_card (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hPZ : 32 ≤ edgeCount G C.P C.Z) :
    6 ≤ (zExternalUnion G C).card := by
  have hInternal := internal_edgeCount_le_choose_two G C.Z hG
  have hCross := cross_edgeCount_add_reverse_le G C.P C.Z hG
  have hExternal := edgeCount_le_card_mul_card
    G C.Z (zExternalUnion G C)
  have hReverse : edgeCount G C.Z C.P ≤ 3 := by
    rw [hPCard, hZCard] at hCross
    omega
  have hInternal' : edgeCount G C.Z C.Z ≤ 10 := by
    rw [hZCard] at hInternal
    simpa [Nat.choose] using hInternal
  have hDegreeSum :
      ∑ z ∈ C.Z, G.outdegree z =
        edgeCount G C.Z C.Z +
          edgeCount G C.Z (zExternalUnion G C) + edgeCount G C.Z C.P := by
    calc
      (∑ z ∈ C.Z, G.outdegree z) =
          ∑ z ∈ C.Z, (directCount G C.Z z +
            directCount G (zExternalUnion G C) z + directCount G C.P z) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact z_outdegree_eq_retainedCounts G C z hz
      _ = edgeCount G C.Z C.Z +
          edgeCount G C.Z (zExternalUnion G C) + edgeCount G C.Z C.P := by
        unfold edgeCount
        simp only [Finset.sum_add_distrib]
  have hDegreeLower : 40 ≤ ∑ z ∈ C.Z, G.outdegree z := by
    calc
      40 = ∑ _z ∈ C.Z, 8 := by simp [hZCard]
      _ ≤ ∑ z ∈ C.Z, G.outdegree z := by
        apply Finset.sum_le_sum
        intro z hz
        exact hMin z
  by_contra hNot
  have hWLe : (zExternalUnion G C).card ≤ 5 := by omega
  have hExternal' : edgeCount G C.Z (zExternalUnion G C) ≤ 25 := by
    calc
      _ ≤ C.Z.card * (zExternalUnion G C).card := hExternal
      _ ≤ 25 := by rw [hZCard]; omega
  omega

/-- A five-by-seven `P → Z` rectangle with defect at most three contains at
least 32 arcs. -/
theorem thirtyTwo_le_PZ_of_missing_le_three (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hMissing : 35 - edgeCount G C.P C.Z ≤ 3) :
    32 ≤ edgeCount G C.P C.Z := by
  have hUpper := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hUpper
  omega

theorem fixedAStructure_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C) (hk : C.k = 1)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hAR : ∀ q : Nat, (hq : q < 4) → (a ⟨q + 4, by omega⟩).1 ∈ C.R) :
    fixedAStructure
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) z w
        (fun j ↦ (a j).1)) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    z w (fun j ↦ (a j).1)
  have hSquares := orientedSquare_coreBits_true G.Adj hG.1
    (fun u v huv ↦ hG.2 huv) (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1)
  have hAOriented : orientedSquare 8 (aArc bits) = true := hSquares.2.2
  have hA0' : (a ⟨0, by omega⟩).1 = C.a1 := by simpa using hA0
  have hA1' : (a ⟨1, by omega⟩).1 = (h 0).1 := by
    have hh := hAH (0 : Fin 3)
    have hIndex : (⟨1, by omega⟩ : Fin 8) =
        ⟨(0 : Fin 3).val + 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hIndex]
    exact hh
  have hA01 : aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1) 0 1 (by omega) (by omega)]
    have hAdj : G.Adj C.a1 (h 0).1 := (Finset.mem_filter.mp hH0A1).2
    simp only [decide_eq_true_eq]
    rw [hA0', hA1']
    exact hAdj
  have hA0Tail : all 6 (fun q => !aArc bits 0 (q + 2)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1) 0 (q + 2) (by omega) (by omega)]
    have hNotA1 : (a ⟨q + 2, by omega⟩).1 ∉ C.A1 := by
      intro hMem
      have hEq : (a ⟨q + 2, by omega⟩).1 = (h 0).1 := by
        have hCard : C.A1.card = 1 := hk
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hCard
        have h0eq : (h 0).1 = u := by simpa [hu] using hH0A1
        have hteq : (a ⟨q + 2, by omega⟩).1 = u := by simpa [hu] using hMem
        exact hteq.trans h0eq.symm
      have hIndex : (⟨q + 2, by omega⟩ : Fin 8) = 1 := by
        apply a.injective
        apply Subtype.ext
        exact hEq.trans hA1'.symm
      have hVal : q + 2 = 1 := congrArg Fin.val hIndex
      omega
    have hNotAdj : ¬G.Adj C.a1 (a ⟨q + 2, by omega⟩).1 := by
      intro hAdj
      exact hNotA1 (Finset.mem_filter.mpr ⟨(a ⟨q + 2, by omega⟩).2, hAdj⟩)
    simp [hA0, hNotAdj]
  have hA1R : all 4 (fun q => !aArc bits 1 (q + 4)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1) 1 (q + 4) (by omega) (by omega)]
    have hSource : (a 1).1 = (h 0).1 := by simpa using hAH 0
    have hNotAdj : ¬G.Adj (h 0).1 (a ⟨q + 4, by omega⟩).1 := by
      intro hAdj
      have hr := hAR q hq
      have hrX : (a ⟨q + 4, by omega⟩).1 ∈ C.X := by
        apply Finset.mem_inter.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          exact ⟨(h 0).1, Finset.mem_union_left C.P hH0A1, hAdj⟩
        · apply Finset.mem_sdiff.mpr
          refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
          intro hParts
          apply (Finset.mem_sdiff.mp hr).2
          rcases Finset.mem_union.mp hParts with hA1 | ha1
          · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1)
          · exact Finset.mem_union_right (C.A1 ∪ C.X) ha1
      exact (Finset.mem_sdiff.mp hr).2
        (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))
    simp [hSource, hNotAdj]
  have hXReach (target : Nat) (ht : target = 2 ∨ target = 3)
      (hTargetX : (a ⟨target, by omega⟩).1 ∈ C.X) :
      (aArc bits 1 target || any 7 (fun i =>
        pToH bits i (target - 1))) = true := by
    rcases Finset.mem_inter.mp hTargetX with ⟨hReached, _hOutside⟩
    obtain ⟨u, huParts, huTarget⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReached
    rcases Finset.mem_union.mp huParts with huA1 | huP
    · have hCard : C.A1.card = 1 := hk
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hCard
      have huEq : u = (h 0).1 := by
        have huV : u = v := by simpa [hv] using huA1
        have hhV : (h 0).1 = v := by simpa [hv] using hH0A1
        exact huV.trans hhV.symm
      rw [Bool.or_eq_true]
      left
      rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        z w (fun j ↦ (a j).1) 1 target (by omega) (by omega)]
      have hSource : (a 1).1 = (h 0).1 := by simpa using hAH 0
      simpa [hSource, huEq] using huTarget
    · obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
      rw [Bool.or_eq_true]
      right
      rw [any_eq_true_iff]
      refine ⟨i, i.isLt, ?_⟩
      rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        z w (fun j ↦ (a j).1) i (target - 1) i.isLt (by omega)]
      have hTargetH : (a ⟨target, by omega⟩).1 =
          (h ⟨target - 1, by omega⟩).1 := by
        have := hAH ⟨target - 1, by omega⟩
        simpa [show target - 1 + 1 = target by omega] using this
      have huEq : (p i).1 = u := congrArg Subtype.val hi
      simpa [huEq, hTargetH] using huTarget
  have hX1 : (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) = true := by
    apply hXReach 2 (Or.inl rfl)
    have hEq : (a 2).1 = (h 1).1 := by simpa using hAH 1
    simpa [hEq] using hH1X
  have hX2 : (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) = true := by
    apply hXReach 3 (Or.inr rfl)
    have hEq : (a 3).1 = (h 2).1 := by simpa using hAH 2
    simpa [hEq] using hH2X
  have hHDegrees : all 3 (fun hi =>
      (8 : BitVec 8).ule (hDegree bits hi)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    have hDegreeEq : (hDegree bits i).toNat = G.outdegree (h ⟨i, hi⟩).1 := by
      have hDirect := hDegree_coreBits_toNat G C p z w h a hAH i hi
      rw [hDirect, H_outdegree_eq_A_add_P G C hG hPB
        (h ⟨i, hi⟩).1 (h ⟨i, hi⟩).2]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegreeEq]
    exact hMin _
  have hRDegrees : all 4 (fun q =>
      (1 : BitVec 8).ule (aOut bits (q + 4))) = true := by
    rw [all_eq_true_iff]
    intro q hq
    have hOut := aOut_coreBits_toNat G C (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) z w a (q + 4) (by omega)
    have hMinA := (hPivot (a ⟨q + 4, by omega⟩).1
      (a ⟨q + 4, by omega⟩).2).1
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hOut]
    change 1 ≤ directCount G C.A (a ⟨q + 4, by omega⟩).1
    change 1 ≤ (C.A.filter (G.Adj (a ⟨q + 4, by omega⟩).1)).card
    rw [hk] at hMinA
    exact hMinA
  rw [fixedAStructure]
  simpa only [Bool.and_eq_true] using
    ⟨⟨⟨⟨⟨⟨⟨hAOriented, hA01⟩, hA0Tail⟩, hA1R⟩, hX1⟩, hX2⟩,
      hHDegrees⟩, hRDegrees⟩

end SeymourEight.FiveZExactGlobalBridge
