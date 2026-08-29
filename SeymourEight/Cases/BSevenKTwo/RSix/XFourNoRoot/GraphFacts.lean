import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Encoding
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeGraphFacts

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Bridge

open CertificateBridge Shared Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) : Encoding := coreBits G.Adj p h e

theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (Shared.FiniteCore.count n f).toNat =
      ∑ i ∈ Finset.range n, (Shared.FiniteCore.bitCount (f i)).toNat := by
  induction n with
  | zero => simp [Shared.FiniteCore.count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hLe : (∑ i ∈ Finset.range n,
          (Shared.FiniteCore.bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i _
            cases f i <;> decide
          _ = n := by simp
      rw [Shared.FiniteCore.count, BitVec.toNat_add, ih hn',
        Finset.sum_range_succ]
      cases hf : f n
      · simpa [Shared.FiniteCore.bitCount, hf] using Nat.mod_eq_of_lt
          (by omega : (∑ i ∈ Finset.range n,
            (Shared.FiniteCore.bitCount (f i)).toNat) < 256)
      · simpa [Shared.FiniteCore.bitCount, hf] using Nat.mod_eq_of_lt
          (by omega : (∑ i ∈ Finset.range n,
            (Shared.FiniteCore.bitCount (f i)).toNat) + 1 < 256)

theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (Shared.FiniteCore.count n f).toNat =
      ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn,
    ← Fin.sum_univ_eq_sum_range
      (fun i => (Shared.FiniteCore.bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> simp [Shared.FiniteCore.bitCount]

theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    Shared.FiniteCore.all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [Shared.FiniteCore.all]
  | succ n ih =>
      simp only [Shared.FiniteCore.all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · simpa [show i = n by omega] using hn
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    Shared.FiniteCore.any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [Shared.FiniteCore.any]
  | succ n ih =>
      simp only [Shared.FiniteCore.any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hf⟩ | hf)
        · exact ⟨i, by omega, hf⟩
        · exact ⟨n, by omega, hf⟩
      · rintro ⟨i, hi, hf⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hf⟩
        · exact Or.inr (show i = n by omega ▸ hf)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (Shared.FiniteCore.count n b).toNat ≤ (S.filter Q).card := by
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j _
  by_cases hb : b j = true
  · simp [hb, hGood j hb]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

omit [Fintype V] [DecidableEq V] in
theorem pBlockCounts (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E})
    (hG : G.IsOriented) (i : Nat) (hi : i < 6) :
    (pOut (graphBits G (fun j => (eP j).1) (fun j => (eH j).1)
      (fun j => (eE j).1)) i).toNat = directCount G P (eP ⟨i, hi⟩).1 ∧
    (pHOut (graphBits G (fun j => (eP j).1) (fun j => (eH j).1)
      (fun j => (eE j).1)) i).toNat = directCount G H (eP ⟨i, hi⟩).1 ∧
    (pEOut (graphBits G (fun j => (eP j).1) (fun j => (eH j).1)
      (fun j => (eE j).1)) i).toNat = directCount G E (eP ⟨i, hi⟩).1 := by
  classical
  let bits := graphBits G (fun j => (eP j).1) (fun j => (eH j).1)
    (fun j => (eE j).1)
  have hP : (pOut bits i).toNat = directCount G P (eP ⟨i, hi⟩).1 := by
    rw [pOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G P eP
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
    apply directCount_eq_sum_bool G H eH
    intro j
    rw [pToH_coreBits G.Adj _ _ _ i j hi j.isLt]
    simp
  have hE : (pEOut bits i).toNat = directCount G E (eP ⟨i, hi⟩).1 := by
    rw [pEOut, toNat_count_eq_fin_sum 3 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G E eE
    intro j
    rw [pToE_coreBits G.Adj _ _ _ i j hi j.isLt]
    simp
  exact ⟨hP, hH, hE⟩

private theorem sum_fin36_eq_blocks (f : Fin 36 → Nat) :
    (∑ q, f q) = ∑ i : Fin 6, ∑ j : Fin 6,
      f ⟨i * 6 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin 36).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp [finProdFinEquiv]
  omega

private theorem sum_fin18_eq_blocks (f : Fin 18 → Nat) :
    (∑ q, f q) = ∑ i : Fin 6, ∑ j : Fin 3,
      f ⟨i * 3 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 3 ≃ Fin 18).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp [finProdFinEquiv]
  omega

omit [Fintype V] [DecidableEq V] in
theorem totalPH_toNat (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E}) (hG : G.IsOriented) :
    (totalPH (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1))).toNat = edgeCount G P H := by
  classical
  let bits := graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
    (fun i => (eE i).1)
  rw [totalPH, toNat_count_eq_fin_sum 36 _ (by omega),
    sum_fin36_eq_blocks, edgeCount_eq_sum_fin G P H eP]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (pBlockCounts G P H E eP eH eE hG i i.isLt).2.1,
    pHOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  apply Finset.sum_congr rfl
  intro j _
  have hd : (i.val * 6 + j.val) / 6 = i.val := by omega
  have hm : (i.val * 6 + j.val) % 6 = j.val := by
    simp
  simp [hd, hm]

omit [Fintype V] [DecidableEq V] in
theorem totalHP_toNat (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E}) :
    (totalHP (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1))).toNat = edgeCount G H P := by
  classical
  rw [totalHP, toNat_count_eq_fin_sum 36 _ (by omega),
    sum_fin36_eq_blocks, edgeCount_eq_sum_fin G H P eH]
  apply Finset.sum_congr rfl
  intro i _
  rw [directCount_eq_sum_fin G P eP]
  apply Finset.sum_congr rfl
  intro j _
  have hd : (i.val * 6 + j.val) / 6 = i.val := by omega
  have hm : (i.val * 6 + j.val) % 6 = j.val := by
    simp
  simp only [hd, hm]
  rw [hToP_coreBits G.Adj _ _ _ i j i.isLt j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem totalPE_toNat (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E}) (hG : G.IsOriented) :
    (totalPE (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1))).toNat = edgeCount G P E := by
  classical
  rw [totalPE, toNat_count_eq_fin_sum 18 _ (by omega),
    sum_fin18_eq_blocks, edgeCount_eq_sum_fin G P E eP]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (pBlockCounts G P H E eP eH eE hG i i.isLt).2.2,
    pEOut, toNat_count_eq_fin_sum 3 _ (by omega)]
  apply Finset.sum_congr rfl
  intro j _
  have hd : (i.val * 3 + j.val) / 3 = i.val := by omega
  have hm : (i.val * 3 + j.val) % 3 = j.val := by
    simp
  simp [hd, hm]

omit [Fintype V] [DecidableEq V] in
theorem totalPP_toNat (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E}) (hG : G.IsOriented) :
    (totalPP (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1))).toNat = edgeCount G P P := by
  classical
  let bits := graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
    (fun i => (eE i).1)
  rw [edgeCount_eq_sum_fin G P P eP]
  have hRows : (∑ i : Fin 6, directCount G P (eP i).1) =
      ∑ i : Fin 6, (pOut bits i).toNat := by
    apply Finset.sum_congr rfl
    intro i _
    exact (pBlockCounts G P H E eP eH eE hG i i.isLt).1.symm
  rw [hRows, totalPP, toNat_count_eq_fin_sum 30 _ (by omega)]
  rw [← (finProdFinEquiv : Fin 6 × Fin 5 ≃ Fin 30).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [pOut, toNat_count_eq_fin_sum 6 _ (by omega),
    Fin.sum_univ_succAbove (fun j : Fin 6 => if pArc bits i j then 1 else 0) i]
  rw [show (if pArc bits i i then 1 else 0) = 0 by simp [pArc], zero_add]
  apply Finset.sum_congr rfl
  intro j _
  have hd : (i.val * 5 + j.val) / 5 = i.val := by omega
  have hm : (i.val * 5 + j.val) % 5 = j.val := by
    simp
  have ht : i.succAbove j =
      ⟨if j.val < i.val then j.val else j.val + 1, by split <;> omega⟩ := by
    apply Fin.ext
    by_cases hji : j.val < i.val
    · rw [Fin.succAbove_of_castSucc_lt]
      · simp [hji]
      · exact hji
    · rw [Fin.succAbove_of_le_castSucc]
      · simp [hji]
      · exact Fin.mk_le_mk.mpr (Nat.le_of_not_gt hji)
  have hprod : (finProdFinEquiv (i, j)).val = i.val * 5 + j.val := by
    simp [finProdFinEquiv]
    omega
  rw [hprod]
  simp only [hd, hm]
  rw [ht]

omit [Fintype V] [DecidableEq V] in
theorem orientedBasic_true (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E}) (hG : G.IsOriented) :
    orientedBasic (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1)) = true := by
  classical
  simp only [orientedBasic, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [all_eq_true_iff]
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
  · rw [all_eq_true_iff]
    intro p hp
    rw [all_eq_true_iff]
    intro h hh
    rw [pToH_coreBits G.Adj _ _ _ p h hp hh,
      hToP_coreBits G.Adj _ _ _ h p hh hp]
    by_cases ha : G.Adj (eP ⟨p, hp⟩).1 (eH ⟨h, hh⟩).1
    · simp [ha, hG.2 ha]
    · simp [ha]

theorem pSecond_true_mem (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E})
    (p q : Nat) (hp : p < 6) (hq : q < 6)
    (hs : pSecond (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1)) p q = true) :
    (eP ⟨q, hq⟩).1 ∈ G.secondOutNeighborFinset (eP ⟨p, hp⟩).1 := by
  let bits := graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
    (fun i => (eE i).1)
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
    have hf : (⟨q, hq⟩ : Fin 6) = ⟨p, hp⟩ := by
      apply eP.injective
      exact Subtype.ext heq
    exact hpq (Fin.ext_iff.mp hf).symm
  rw [pReached, Bool.or_eq_true] at hReach
  have hPath : ∃ w, G.Adj (eP ⟨p, hp⟩).1 w ∧
      G.Adj w (eP ⟨q, hq⟩).1 := by
    rcases hReach with hViaP | hViaH
    · obtain ⟨m, hm, hM⟩ := (any_eq_true_iff 6 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hM
      rcases hM with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
      rw [pArc_coreBits G.Adj _ _ _ p m hp hm] at hFirst
      rw [pArc_coreBits G.Adj _ _ _ m q hm hq] at hLast
      exact ⟨(eP ⟨m, hm⟩).1, (of_decide_eq_true hFirst).2,
        (of_decide_eq_true hLast).2⟩
    · obtain ⟨m, hm, hM⟩ := (any_eq_true_iff 6 _).mp hViaH
      simp only [Bool.and_eq_true] at hM
      rcases hM with ⟨hFirst, hLast⟩
      rw [pToH_coreBits G.Adj _ _ _ p m hp hm] at hFirst
      rw [hToP_coreBits G.Adj _ _ _ m q hm hq] at hLast
      exact ⟨(eH ⟨m, hm⟩).1, of_decide_eq_true hFirst,
        of_decide_eq_true hLast⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hPath, hNotAdj, hNe⟩

theorem pSecondCount_le_graph (P H E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (eH : Fin 6 ≃ {v : V // v ∈ H})
    (eE : Fin 3 ≃ {v : V // v ∈ E}) (p : Nat) (hp : p < 6) :
    (pSecondCount (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1)) p).toNat ≤
      (P.filter fun v => v ∈ G.secondOutNeighborFinset (eP ⟨p, hp⟩).1).card := by
  apply count_le_filterCard P eP
    (pSecond (graphBits G (fun i => (eP i).1) (fun i => (eH i).1)
      (fun i => (eE i).1)) p)
    (fun v => v ∈ G.secondOutNeighborFinset (eP ⟨p, hp⟩).1) (by omega)
  intro j hj
  exact pSecond_true_mem G P H E eP eH eE p j hp j.isLt hj

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Bridge
