import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeEncoding
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.BroadFourAssembly
import SeymourEight.Shared.SameStatusKing

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Graph facts for the projected three-`Z` core

These lemmas deliberately use arbitrary equivalences.  Canonical relabeling
is layered on top, so adjacency decoding and graph counting are proved only
once.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeBridge

open CertificateBridge Shared ZThreeCore
open FiveZExactGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (p : Fin 7 → V) (h : Fin 6 → V)
    (z : Fin 3 → V) : Encoding := coreBits G.Adj p h z

theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hLe : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [count, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      cases hf : f n
      · simpa [bitCount, hf] using Nat.mod_eq_of_lt (by omega :
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) < 256)
      · simpa [bitCount, hf] using Nat.mod_eq_of_lt (by omega :
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) + 1 < 256)

theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ (bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [bitCount]

theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · simpa [show i = n by omega] using hn
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [any]
  | succ n ih =>
      simp only [any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hf⟩ | hf)
        · exact ⟨i, by omega, hf⟩
        · exact ⟨n, by omega, hf⟩
      · rintro ⟨i, hi, hf⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hf⟩
        · exact Or.inr (show i = n by omega ▸ hf)

theorem count_mono {n : Nat} (f g : Nat → Bool) (hn : n < 256)
    (hfg : ∀ i < n, f i = true → g i = true) :
    (count n f).toNat ≤ (count n g).toNat := by
  rw [toNat_count_eq_fin_sum n f hn, toNat_count_eq_fin_sum n g hn]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hf : f i = true
  · have hg := hfg i i.isLt hf
    simp [hf, hg]
  · have hf' := Bool.eq_false_of_not_eq_true hf
    simp [hf']

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (count n b).toNat ≤ (S.filter Q).card := by
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · simp [hb, hGood j hb]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

omit [Fintype V] [DecidableEq V] in
theorem pBlockCounts (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z})
    (hG : G.IsOriented) (i : Nat) (hi : i < 7) :
    (pOut (graphBits G (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)
      (fun j ↦ (eZ j).1)) i).toNat = directCount G P (eP ⟨i, hi⟩).1 ∧
    (pHOut (graphBits G (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)
      (fun j ↦ (eZ j).1)) i).toNat = directCount G H (eP ⟨i, hi⟩).1 ∧
    (pZOut (graphBits G (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)
      (fun j ↦ (eZ j).1)) i).toNat = directCount G Z (eP ⟨i, hi⟩).1 := by
  classical
  let bits := graphBits G (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)
    (fun j ↦ (eZ j).1)
  have hP : (pOut bits i).toNat = directCount G P (eP ⟨i, hi⟩).1 := by
    rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G P eP _
    intro j
    rw [pArc_coreBits G.Adj _ _ _ i j hi j.isLt]
    by_cases hij : i = j
    · simp only [hij, ne_eq, not_true_eq_false, false_and, decide_false,
        Bool.false_eq_true, false_iff]
      intro ha
      apply hG.1 (eP j).1
      simpa using ha
    · simp [hij]
  have hH : (pHOut bits i).toNat = directCount G H (eP ⟨i, hi⟩).1 := by
    rw [pHOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G H eH _
    intro j
    rw [pToH_coreBits G.Adj _ _ _ i j hi j.isLt]
    simp
  have hZ : (pZOut bits i).toNat = directCount G Z (eP ⟨i, hi⟩).1 := by
    rw [pZOut, toNat_count_eq_fin_sum 3 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G Z eZ _
    intro j
    rw [pToZ_coreBits G.Adj _ _ _ i j hi j.isLt]
    simp
  exact ⟨hP, hH, hZ⟩

private theorem sum_fin42_eq_blocks (f : Fin 42 → Nat) :
    (∑ q, f q) = ∑ i : Fin 7, ∑ j : Fin 6,
      f ⟨i * 6 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 7 × Fin 6 ≃ Fin 42).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

omit [Fintype V] [DecidableEq V] in
theorem totalPOut_toNat (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z})
    (hG : G.IsOriented) :
    (totalPOut (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1))).toNat = edgeCount G P P := by
  classical
  let bits := graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
    (fun i ↦ (eZ i).1)
  rw [totalPOut, toNat_count_eq_fin_sum 42 _ (by omega),
    sum_fin42_eq_blocks]
  have hEach : ∀ i : Fin 7,
      (pOut bits i).toNat = directCount G P (eP i).1 := by
    intro i
    exact (pBlockCounts G P H Z eP eH eZ hG i i.isLt).1
  rw [edgeCount_eq_sum_fin G P P eP]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hEach i, pOut, toNat_count_eq_fin_sum 7 _ (by omega),
    Fin.sum_univ_succAbove
      (fun k : Fin 7 => if pArc bits i k then 1 else 0) i]
  rw [show (if pArc bits i i then 1 else 0) = 0 by simp [pArc], zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hDiv : (i.val * 6 + j.val) / 6 = i.val := by omega
  have hMod : (i.val * 6 + j.val) % 6 = j.val := by
    simp
  have hTarget : i.succAbove j =
      ⟨if j.val < i.val then j.val else j.val + 1, by split <;> omega⟩ := by
    apply Fin.ext
    by_cases hji : j.val < i.val
    · rw [Fin.succAbove_of_castSucc_lt]
      · simp [hji]
      · exact hji
    · rw [Fin.succAbove_of_le_castSucc]
      · simp [hji]
      · exact Fin.mk_le_mk.mpr (Nat.le_of_not_gt hji)
  simp only [hDiv, hMod]
  rw [hTarget]

private theorem sum_fin42_eq_h_blocks (f : Fin 42 → Nat) :
    (∑ q, f q) = ∑ i : Fin 6, ∑ j : Fin 7,
      f ⟨i * 7 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 7 ≃ Fin 42).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

private theorem sum_fin21_eq_blocks (f : Fin 21 → Nat) :
    (∑ q, f q) = ∑ i : Fin 7, ∑ j : Fin 3,
      f ⟨i * 3 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

omit [Fintype V] [DecidableEq V] in
theorem totalPToH_toNat (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z})
    (hG : G.IsOriented) :
    (totalPToH (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1))).toNat = edgeCount G P H := by
  classical
  let bits := graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
    (fun i ↦ (eZ i).1)
  rw [totalPToH, toNat_count_eq_fin_sum 42 _ (by omega),
    sum_fin42_eq_blocks, edgeCount_eq_sum_fin G P H eP]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (pBlockCounts G P H Z eP eH eZ hG i i.isLt).2.1,
    pHOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  have hDiv : (i.val * 6 + j.val) / 6 = i.val := by omega
  have hMod : (i.val * 6 + j.val) % 6 = j.val := by
    simp
  simp only [hDiv, hMod]

omit [Fintype V] [DecidableEq V] in
theorem totalHToP_toNat (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z}) :
    (totalHToP (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1))).toNat = edgeCount G H P := by
  classical
  let bits := graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
    (fun i ↦ (eZ i).1)
  rw [totalHToP, toNat_count_eq_fin_sum 42 _ (by omega),
    sum_fin42_eq_h_blocks, edgeCount_eq_sum_fin G H P eH]
  apply Finset.sum_congr rfl
  intro i hi
  rw [directCount_eq_sum_fin G P eP]
  apply Finset.sum_congr rfl
  intro j hj
  have hDiv : (i.val * 7 + j.val) / 7 = i.val := by omega
  have hMod : (i.val * 7 + j.val) % 7 = j.val := by
    simp
  simp only [hDiv, hMod]
  rw [hToP_coreBits G.Adj _ _ _ i j i.isLt j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem totalPToZ_toNat (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z})
    (hG : G.IsOriented) :
    (totalPToZ (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1))).toNat = edgeCount G P Z := by
  classical
  let bits := graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
    (fun i ↦ (eZ i).1)
  rw [totalPToZ, toNat_count_eq_fin_sum 21 _ (by omega),
    sum_fin21_eq_blocks, edgeCount_eq_sum_fin G P Z eP]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (pBlockCounts G P H Z eP eH eZ hG i i.isLt).2.2,
    pZOut, toNat_count_eq_fin_sum 3 _ (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  have hDiv : (i.val * 3 + j.val) / 3 = i.val := by omega
  have hMod : (i.val * 3 + j.val) % 3 = j.val := by
    simp
  simp only [hDiv, hMod]

omit [Fintype V] [DecidableEq V] in
theorem orientedP_true (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z}) (hG : G.IsOriented) :
    orientedP (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1)) = true := by
  classical
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [pArc_coreBits G.Adj _ _ _ i j hi hj,
    pArc_coreBits G.Adj _ _ _ j i hj hi]
  by_cases hij : i = j
  · simp [hij]
  · by_cases ha : G.Adj (eP ⟨i, hi⟩).1 (eP ⟨j, hj⟩).1
    · simp [hij, ha, hG.2 ha]
    · simp [hij, ha]

omit [Fintype V] [DecidableEq V] in
theorem orientedPH_true (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z}) (hG : G.IsOriented) :
    orientedPH (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1)) = true := by
  classical
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  rw [pToH_coreBits G.Adj _ _ _ p h hp hh,
    hToP_coreBits G.Adj _ _ _ h p hh hp]
  by_cases ha : G.Adj (eP ⟨p, hp⟩).1 (eH ⟨h, hh⟩).1
  · simp [ha, hG.2 ha]
  · simp [ha]

theorem allZReached_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ C.Z}) :
    allZReached (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1)) = true := by
  rw [allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := (eZ ⟨z, hz⟩).2
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
  obtain ⟨i, hi⟩ := eP.surjective ⟨p, hp⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt hz]
  simpa [congrArg Subtype.val hi] using hpz

theorem pSecond_true_mem (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z})
    (p q : Nat) (hp : p < 7) (hq : q < 7)
    (hs : pSecond (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1)) p q = true) :
    (eP ⟨q, hq⟩).1 ∈ G.secondOutNeighborFinset (eP ⟨p, hp⟩).1 := by
  let bits := graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
    (fun i ↦ (eZ i).1)
  simp only [pSecond, Bool.and_eq_true, decide_eq_true_eq] at hs
  rcases hs with ⟨⟨hpq, hNot⟩, hReach⟩
  have hNotAdj : ¬G.Adj (eP ⟨p, hp⟩).1 (eP ⟨q, hq⟩).1 := by
    intro ha
    have hArc : pArc bits p q = true := by
      rw [pArc_coreBits G.Adj _ _ _ p q hp hq]
      simp [hpq, ha]
    simp [bits, hArc] at hNot
  have hNe : (eP ⟨q, hq⟩).1 ≠ (eP ⟨p, hp⟩).1 := by
    intro heq
    have hfin : (⟨q, hq⟩ : Fin 7) = ⟨p, hp⟩ := by
      apply eP.injective
      exact Subtype.ext heq
    exact hpq (Fin.ext_iff.mp hfin).symm
  have hPath : ∃ w, G.Adj (eP ⟨p, hp⟩).1 w ∧
      G.Adj w (eP ⟨q, hq⟩).1 := by
    rw [pReached] at hReach
    simp only [Bool.or_eq_true] at hReach
    rcases hReach with hPPart | hViaH
    · rcases hPPart with hDirect | hViaP
      · exact (hNotAdj (by
          rw [pArc_coreBits G.Adj _ _ _ p q hp hq] at hDirect
          simpa [hpq] using of_decide_eq_true hDirect)).elim
      · obtain ⟨middle, hm, hMiddle⟩ := (any_eq_true_iff 7 _).mp hViaP
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hMiddle
        rcases hMiddle with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
        rw [pArc_coreBits G.Adj _ _ _ p middle hp hm] at hFirst
        rw [pArc_coreBits G.Adj _ _ _ middle q hm hq] at hLast
        exact ⟨(eP ⟨middle, hm⟩).1,
          (of_decide_eq_true hFirst).2, (of_decide_eq_true hLast).2⟩
    · obtain ⟨middle, hm, hMiddle⟩ := (any_eq_true_iff 6 _).mp hViaH
      simp only [Bool.and_eq_true] at hMiddle
      rcases hMiddle with ⟨hFirst, hLast⟩
      rw [pToH_coreBits G.Adj _ _ _ p middle hp hm] at hFirst
      rw [hToP_coreBits G.Adj _ _ _ middle q hm hq] at hLast
      exact ⟨(eH ⟨middle, hm⟩).1,
        of_decide_eq_true hFirst, of_decide_eq_true hLast⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hPath, hNotAdj, hNe⟩

theorem pSecondCount_le_graph (P H Z : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eZ : Fin 3 ≃ {v : V // v ∈ Z})
    (p : Nat) (hp : p < 7) :
    (pSecondCount (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1)) p).toNat ≤
      (P.filter fun v ↦ v ∈ G.secondOutNeighborFinset (eP ⟨p, hp⟩).1).card := by
  apply count_le_filterCard P eP
    (pSecond (graphBits G (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
      (fun i ↦ (eZ i).1)) p)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (eP ⟨p, hp⟩).1)
    (by omega)
  intro j hj
  exact pSecond_true_mem G P H Z eP eH eZ p j hp j.isLt hj

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeBridge
