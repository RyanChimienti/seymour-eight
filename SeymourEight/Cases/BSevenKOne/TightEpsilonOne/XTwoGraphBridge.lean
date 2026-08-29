import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.XTwoCore
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XOne
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactLabels
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge
import SeymourEight.Cases.BSixKThree.CoreGraphBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.EpsilonOneXTwoGraphBridge

open BSevenKOne BSevenKOneCounting CertificateBridge
  EpsilonOneXTwoCore EpsilonOneRootCoreGraphBridge Shared
  TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def coreBitAt (p : Fin 7 → V) (h : Fin 3 → V) (e : Fin 5 → V)
    (a : Fin 8 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (G.Adj (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 70 then
    let q := n - 49
    decide (G.Adj (p ⟨q / 3, by omega⟩) (h ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 91 then
    let q := n - 70
    decide (G.Adj (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPE : n < 126 then
    let q := n - 91
    decide (G.Adj (p ⟨q / 5, by omega⟩) (e ⟨q % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnHA : n < 150 then
    let q := n - 126
    decide (G.Adj (h ⟨q / 8, by omega⟩) (a ⟨q % 8, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 7 → V) (h : Fin 3 → V) (e : Fin 5 → V)
    (a : Fin 8 → V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 150 => coreBitAt G p h e a n))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (n : Nat) (hn : n < 150) :
    (coreBits G p h e a).getLsbD n = coreBitAt G p h e a n := by
  classical
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa using hn) false, List.getElem_ofFn]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits G p h e a) i j = decide (G.Adj (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  classical
  have hd : (i * 7 + j) / 7 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hm : (i * 7 + j) % 7 = j := Nat.mul_add_mod_of_lt hj
  rw [pArc, getLsbD_coreBits G p h e a _ (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega, hd, hm]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (i j : Nat) (hi : i < 7) (hj : j < 3) :
    pToH (coreBits G p h e a) i j = decide (G.Adj (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  classical
  have hd : (i * 3 + j) / 3 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hm : (i * 3 + j) % 3 = j := Nat.mul_add_mod_of_lt hj
  rw [pToH, getLsbD_coreBits G p h e a _ (by omega)]
  simp [coreBitAt, show ¬49 + i * 3 + j < 49 by omega,
    show 49 + i * 3 + j < 70 by omega, show 49 + i * 3 + j - 49 = i * 3 + j by omega,
    hd, hm]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (i j : Nat) (hi : i < 3) (hj : j < 7) :
    hToP (coreBits G p h e a) i j = decide (G.Adj (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  classical
  have hd : (i * 7 + j) / 7 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hm : (i * 7 + j) % 7 = j := Nat.mul_add_mod_of_lt hj
  rw [hToP, getLsbD_coreBits G p h e a _ (by omega)]
  simp [coreBitAt, show ¬70 + i * 7 + j < 49 by omega,
    show ¬70 + i * 7 + j < 70 by omega, show 70 + i * 7 + j < 91 by omega,
    show 70 + i * 7 + j - 70 = i * 7 + j by omega, hd, hm]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pToE_coreBits (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (i j : Nat) (hi : i < 7) (hj : j < 5) :
    pToE (coreBits G p h e a) i j = decide (G.Adj (p ⟨i, hi⟩) (e ⟨j, hj⟩)) := by
  classical
  have hd : (i * 5 + j) / 5 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hm : (i * 5 + j) % 5 = j := Nat.mul_add_mod_of_lt hj
  rw [pToE, getLsbD_coreBits G p h e a _ (by omega)]
  simp [coreBitAt, show ¬91 + i * 5 + j < 49 by omega,
    show ¬91 + i * 5 + j < 70 by omega, show ¬91 + i * 5 + j < 91 by omega,
    show 91 + i * 5 + j < 126 by omega,
    show 91 + i * 5 + j - 91 = i * 5 + j by omega, hd, hm]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem hToA_coreBits (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (i j : Nat) (hi : i < 3) (hj : j < 8) :
    hToA (coreBits G p h e a) i j = decide (G.Adj (h ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  classical
  have hd : (i * 8 + j) / 8 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hm : (i * 8 + j) % 8 = j := Nat.mul_add_mod_of_lt hj
  rw [hToA, getLsbD_coreBits G p h e a _ (by omega)]
  simp [coreBitAt, show ¬126 + i * 8 + j < 49 by omega,
    show ¬126 + i * 8 + j < 70 by omega, show ¬126 + i * 8 + j < 91 by omega,
    show ¬126 + i * 8 + j < 126 by omega, show 126 + i * 8 + j < 150 by omega,
    show 126 + i * 8 + j - 126 = i * 8 + j by omega, hd, hm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hs : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [count, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      have hlt0 : (∑ i ∈ Finset.range n,
          (if f i then (1 : BitVec 8) else 0).toNat) < 256 := by
        simpa [bitCount] using (show
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) < 256 by omega)
      have hlt1 : (∑ i ∈ Finset.range n,
          (if f i then (1 : BitVec 8) else 0).toNat) + 1 < 256 := by
        simpa [bitCount] using (show
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) + 1 < 256 by omega)
      cases hfn : f n
      · simp only [bitCount]
        exact Nat.mod_eq_of_lt hlt0
      · simp only [bitCount]
        exact Nat.mod_eq_of_lt hlt1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn, ← Fin.sum_univ_eq_sum_range
    (fun i => (bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [bitCount]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8)
    (hlt : ∑ i ∈ Finset.range n, (f i).toNat < 256) :
    (sumCount n f).toNat = ∑ i ∈ Finset.range n, (f i).toNat := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      have hprefix : ∑ i ∈ Finset.range n, (f i).toNat < 256 := by
        rw [Finset.sum_range_succ] at hlt
        omega
      rw [sumCount, BitVec.toNat_add, ih hprefix, Finset.sum_range_succ]
      simp only [Nat.reducePow]
      apply Nat.mod_eq_of_lt
      simpa [Finset.sum_range_succ] using hlt

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_toNat_eq_trueCount (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = BSixKTwoCoreBridge.trueCount n f := by
  rw [toNat_count_eq_fin_sum n f hn,
    BSixKTwoCoreBridge.trueCount_eq_filter_fin]
  rw [Finset.card_filter]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [any]
  | succ n ih =>
      simp only [any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hlast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hlast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · exact Or.inr (show i = n by omega ▸ hfi)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        by_cases hin : i < n
        · exact hprev i hin
        · simpa [show i = n by omega] using hlast
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

omit [Fintype V] [DecidableEq V] in
theorem pOut_toNat (P : Finset V) (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 3 → V) (e : Fin 5 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 7) :
    (pOut (coreBits G (fun j => (p j).1) h e a) i).toNat =
      directCount G P (p ⟨i, hi⟩).1 := by
  classical
  rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega),
    Shared.directCount_eq_sum_fin G P p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pArc_coreBits G (fun k => (p k).1) h e a i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem pHOut_toNat (H : Finset V) (p : Fin 7 → V)
    (h : Fin 3 ≃ {v : V // v ∈ H}) (e : Fin 5 → V) (a : Fin 8 → V)
    (i : Nat) (hi : i < 7) :
    (pHOut (coreBits G p (fun j => (h j).1) e a) i).toNat =
      directCount G H (p ⟨i, hi⟩) := by
  classical
  rw [pHOut, toNat_count_eq_fin_sum 3 _ (by omega),
    Shared.directCount_eq_sum_fin G H h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pToH_coreBits G p (fun k => (h k).1) e a i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem pEOut_toNat (E : Finset V) (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 ≃ {v : V // v ∈ E}) (a : Fin 8 → V)
    (i : Nat) (hi : i < 7) :
    (pEOut (coreBits G p h (fun j => (e j).1) a) i).toNat =
      directCount G E (p ⟨i, hi⟩) := by
  classical
  rw [pEOut, toNat_count_eq_fin_sum 5 _ (by omega),
    Shared.directCount_eq_sum_fin G E e]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pToE_coreBits G p h (fun k => (e k).1) a i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem hPOut_toNat (P : Finset V) (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 3 → V) (e : Fin 5 → V) (a : Fin 8 → V)
    (i : Nat) (hi : i < 3) :
    (hPOut (coreBits G (fun j => (p j).1) h e a) i).toNat =
      directCount G P (h ⟨i, hi⟩) := by
  classical
  rw [hPOut, toNat_count_eq_fin_sum 7 _ (by omega),
    Shared.directCount_eq_sum_fin G P p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hToP_coreBits G (fun k => (p k).1) h e a i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem hAOut_toNat (A : Finset V) (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 ≃ {v : V // v ∈ A})
    (i : Nat) (hi : i < 3) :
    (hAOut (coreBits G p h e (fun j => (a j).1)) i).toNat =
      directCount G A (h ⟨i, hi⟩) := by
  classical
  rw [hAOut, toNat_count_eq_fin_sum 8 _ (by omega),
    Shared.directCount_eq_sum_fin G A a]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hToA_coreBits G p h e (fun k => (a k).1) i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem orientedOnP_true (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (hG : G.IsOriented) :
    orientedOnP (coreBits G p h e a) = true := by
  classical
  have hLoop : ∀ i : Fin 7, ¬G.Adj (p i) (p i) := fun i => hG.1 _
  have hOr : ∀ i j : Fin 7, ¬G.Adj (p i) (p j) ∨ ¬G.Adj (p j) (p i) := by
    intro i j
    by_cases hij : G.Adj (p i) (p j)
    · exact Or.inr (fun hji => hG.2 hij hji)
    · exact Or.inl hij
  simp [orientedOnP, all, pArc_coreBits, hLoop, hOr]

omit [Fintype V] [DecidableEq V] in
theorem orientedPH_true (p : Fin 7 → V) (h : Fin 3 → V)
    (e : Fin 5 → V) (a : Fin 8 → V) (hG : G.IsOriented) :
    orientedPH (coreBits G p h e a) = true := by
  classical
  have hOr : ∀ i : Fin 7, ∀ j : Fin 3,
      ¬G.Adj (p i) (h j) ∨ ¬G.Adj (h j) (p i) := by
    intro i j
    by_cases hij : G.Adj (p i) (h j)
    · exact Or.inr (fun hji => hG.2 hij hji)
    · exact Or.inl hij
  simp [orientedPH, all, pToH_coreBits, hToP_coreBits, hOr]

theorem A1_not_adj_R (C : G.LocalConfiguration) (u r : V)
    (hu : u ∈ C.A1) (hr : r ∈ C.R) : ¬G.Adj u r := by
  intro hur
  have hrX : r ∈ C.X := by
    apply Finset.mem_inter.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨u, Finset.mem_union_left C.P hu, hur⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
      intro hp
      apply (Finset.mem_sdiff.mp hr).2
      rcases Finset.mem_union.mp hp with hA1 | ha1
      · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1)
      · exact Finset.mem_union_right (C.A1 ∪ C.X) ha1
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))

theorem H_degree_eq_A_add_P (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPB : C.P = C.B) (u : V) (hu : u ∈ C.H) :
    G.outdegree u = directCount G C.A u + directCount G C.P u := by
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  have hCaptured := Shared.H_outgoingCaptured G C hG hPB u hu
  have hEq : G.outNeighborFinset u = (C.A ∪ C.P).filter (G.Adj u) := by
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro huv
      exact ⟨by simpa only [Finset.mem_union] using
        hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩
    · exact fun hv => hv.2
  rw [hEq, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter (p := G.Adj u) (q := G.Adj u) (by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP))

set_option linter.flexible false in
theorem fixedHStructure_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPivot : IsMinimalPivot G C) (hPB : C.P = C.B) (hk : C.k = 1)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 → V) (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0 : (h 0).1 ∈ C.A1)
    (hH1 : (h 1).1 ∈ C.X) (hH2 : (h 2).1 ∈ C.X)
    (hAR : ∀ q : Nat, (hq : q < 4) → (a ⟨q + 4, by omega⟩).1 ∈ C.R) :
    fixedHStructure (coreBits G (fun i => (p i).1) (fun i => (h i).1) e
      (fun i => (a i).1)) = true := by
  let bits := coreBits G (fun i => (p i).1) (fun i => (h i).1) e
    (fun i => (a i).1)
  have hDiag : all 3 (fun i => !hToA bits i (i + 1)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    have hb : hToA bits i (i + 1) = false := by
      rw [hToA_coreBits G _ _ _ _ i (i + 1) hi (by omega),
        hAH ⟨i, hi⟩]
      simp only [decide_eq_false_iff_not]
      exact hG.1 _
    simp [hb]
  have hOriented : all 3 (fun i => all 3 (fun j =>
      decide (i = j) || !(hToA bits i (j + 1) && hToA bits j (i + 1)))) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · have hanti : ¬(G.Adj (h ⟨i, hi⟩).1 (h ⟨j, hj⟩).1 ∧
          G.Adj (h ⟨j, hj⟩).1 (h ⟨i, hi⟩).1) :=
        fun hb => hG.2 hb.1 hb.2
      rw [hToA_coreBits G _ _ _ _ i (j + 1) hi (by omega),
        hToA_coreBits G _ _ _ _ j (i + 1) hj (by omega),
        hAH ⟨i, hi⟩, hAH ⟨j, hj⟩]
      have hor : ¬G.Adj (h ⟨i, hi⟩).1 (h ⟨j, hj⟩).1 ∨
          ¬G.Adj (h ⟨j, hj⟩).1 (h ⟨i, hi⟩).1 := by
        by_cases hx : G.Adj (h ⟨i, hi⟩).1 (h ⟨j, hj⟩).1
        · exact Or.inr (fun hy => hanti ⟨hx, hy⟩)
        · exact Or.inl hx
      simp [hij, hor]
  have hBack : Bool.not (hToA bits 0 0) = true := by
    have hb : hToA bits 0 0 = false := by
      rw [hToA_coreBits G _ _ _ _ 0 0 (by omega) (by omega)]
      rw [show (a ⟨0, by omega⟩).1 = (a 0).1 by rfl, hA0]
      simp [hG.2 (Finset.mem_filter.mp hH0).2]
    simp [hb]
  have hNoR : all 4 (fun q => !hToA bits 0 (q + 4)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    have hb : hToA bits 0 (q + 4) = false := by
      rw [hToA_coreBits G _ _ _ _ 0 (q + 4) (by omega) (by omega)]
      simp [A1_not_adj_R G C _ _ hH0 (hAR q hq)]
    simp [hb]
  have hRows : all 3 (fun i =>
      (1 : BitVec 8).ule (hAOut bits i) &&
      (8 : BitVec 8).ule (hDegree bits i) &&
      (!(hAOut bits i == 1) || hPOut bits i == 7)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    have hiH := (h ⟨i, hi⟩).2
    have hiA := Digraph.LocalConfiguration.H_subset_A (G := G) C hiH
    have hANat := hAOut_toNat G C.A (fun j => (p j).1) (fun j => (h j).1)
      e a i hi
    have hPNat := hPOut_toNat G C.P p (fun j => (h j).1) e
      (fun j => (a j).1) i hi
    have hDegreeEq := H_degree_eq_A_add_P G C hG hPB (h ⟨i, hi⟩).1 hiH
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hANat]
      have hMinA := (hPivot (h ⟨i, hi⟩).1 hiA).1
      simpa [hk, directCount, internalFirstNeighbors] using hMinA
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hDegree]
      have hALe : directCount G C.A (h ⟨i, hi⟩).1 ≤ 8 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr a).symm)
      have hPLe : directCount G C.P (h ⟨i, hi⟩).1 ≤ 7 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr p).symm)
      have hDegNat : (hDegree bits i).toNat =
          G.outdegree (h ⟨i, hi⟩).1 := by
        change (hAOut bits i + hPOut bits i).toNat = _
        rw [BitVec.toNat_add]
        change (hAOut bits i).toNat = _ at hANat
        change (hPOut bits i).toNat = _ at hPNat
        rw [hANat, hPNat, Nat.mod_eq_of_lt (by omega)]
        exact hDegreeEq.symm
      have hDegNat' : (hAOut bits i + hPOut bits i).toNat =
          G.outdegree (h ⟨i, hi⟩).1 := by
        simpa [hDegree] using hDegNat
      rw [hDegNat']
      have := hMin (h ⟨i, hi⟩).1
      simpa using this
    · by_cases hTie : directCount G C.A (h ⟨i, hi⟩).1 = 1
      · rw [Bool.or_eq_true]
        apply Or.inr
        apply beq_iff_eq.mpr
        apply BitVec.eq_of_toNat_eq
        rw [hPNat]
        have hBLower := (hPivot (h ⟨i, hi⟩).1 hiA).2 (by
          simpa [hk, directCount, internalFirstNeighbors] using hTie)
        have hPLe : directCount G C.P (h ⟨i, hi⟩).1 ≤ 7 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
            simpa using (Fintype.card_congr p).symm)
        simp
        rw [← hPB] at hBLower
        change C.r ≤ directCount G C.P (h ⟨i, hi⟩).1 at hBLower
        have hr : C.r = 7 := by
          change C.P.card = 7
          simpa using (Fintype.card_congr p).symm
        omega
      · rw [Bool.or_eq_true]
        apply Or.inl
        simp only [Bool.not_eq_true']
        apply Bool.eq_false_iff.mpr
        intro hb
        have heq := beq_iff_eq.mp hb
        have := congrArg BitVec.toNat heq
        rw [hANat] at this
        simp at this
        exact hTie this
  have hCoverage : all 2 (fun q => hToA bits 0 (q + 2) ||
      any 7 (fun i => pToH bits i (q + 1))) = true := by
    rw [all_eq_true_iff]
    intro q hq
    have hqX : (h ⟨q + 1, by omega⟩).1 ∈ C.X := by
      have : q = 0 ∨ q = 1 := by omega
      rcases this with rfl | rfl
      · exact hH1
      · exact hH2
    rcases Finset.mem_inter.mp hqX with ⟨hReach, _⟩
    obtain ⟨middle, hm, hmX⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReach
    rcases Finset.mem_union.mp hm with hmA1 | hmP
    · rw [Bool.or_eq_true]
      apply Or.inl
      rw [hToA_coreBits G _ _ _ _ 0 (q + 2) (by omega) (by omega),
        decide_eq_true_eq, hAH ⟨q + 1, by omega⟩]
      have hmEq : middle = (h 0).1 := by
        have hCard : C.A1.card = 1 := hk
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hCard
        have hmV : middle = v := by simpa [hv] using hmA1
        have h0V : (h 0).1 = v := by simpa [hv] using hH0
        exact hmV.trans h0V.symm
      simpa [hmEq] using hmX
    · rw [Bool.or_eq_true]
      apply Or.inr
      rw [any_eq_true_iff]
      obtain ⟨j, hj⟩ := p.surjective ⟨middle, hmP⟩
      refine ⟨j, j.isLt, ?_⟩
      rw [pToH_coreBits G _ _ _ _ j (q + 1) j.isLt (by omega),
        decide_eq_true_eq]
      simpa [Subtype.ext_iff.mp hj] using hmX
  change fixedHStructure bits = true
  rw [fixedHStructure]
  simpa only [Bool.and_eq_true] using
    (⟨⟨⟨⟨⟨hDiag, hOriented⟩, hBack⟩, hNoR⟩, hRows⟩, hCoverage⟩)

theorem external_has_P_predecessor (C : G.LocalConfiguration)
    (v : V) (hv : v ∈ externalTargets G C) :
    ∃ u ∈ C.P, G.Adj u v := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hvZ).1
  · by_cases hReach : ∃ u ∈ C.P, G.Adj u C.s
    · have hvs : v = C.s := by
        simpa [rootSecondFinset, hReach] using hvRoot
      simpa [hvs] using hReach
    · simp [rootSecondFinset, hReach] at hvRoot

theorem externalCoverage_true (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 → V) (e : Fin 5 ≃ {v : V // v ∈ externalTargets G C})
    (a : Fin 8 → V) :
    all 5 (fun t => any 7 (fun i => pToE
      (coreBits G (fun j => (p j).1) h (fun j => (e j).1) a) i t)) = true := by
  rw [all_eq_true_iff]
  intro t ht
  rw [any_eq_true_iff]
  obtain ⟨u, huP, hut⟩ := external_has_P_predecessor G C (e ⟨t, ht⟩).1
    (e ⟨t, ht⟩).2
  obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pToE_coreBits G _ _ _ _ i t i.isLt ht, decide_eq_true_eq]
  simpa [Subtype.ext_iff.mp hi] using hut

theorem targetCovered_true (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 ≃ {v : V // v ∈ externalTargets G C})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (_hH0 : (h 0).1 ∈ C.A1)
    (hH1 : (h 1).1 ∈ C.X) (hH2 : (h 2).1 ∈ C.X) :
    targetCovered (coreBits G (fun i => (p i).1) (fun i => (h i).1)
      (fun i => (e i).1) (fun i => (a i).1)) = true := by
  let bits := coreBits G (fun i => (p i).1) (fun i => (h i).1)
    (fun i => (e i).1) (fun i => (a i).1)
  rw [targetCovered, all_eq_true_iff]
  intro t ht
  rw [any_eq_true_iff]
  by_cases htx : t < 2
  · have hxH : (h ⟨t + 1, by omega⟩).1 ∈ C.X := by
      have htCases : t = 0 ∨ t = 1 := by omega
      rcases htCases with rfl | rfl
      · exact hH1
      · exact hH2
    rcases Finset.mem_inter.mp hxH with ⟨hReach, _⟩
    obtain ⟨u, hu, hut⟩ := (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReach
    rcases Finset.mem_union.mp hu with huA1 | huP
    · refine ⟨0, by omega, ?_⟩
      simp only [predecessor, htx, if_pos]
      rw [hToA_coreBits G _ _ _ _ 0 (t + 2) (by omega) (by omega),
        decide_eq_true_eq]
      have huEq : u = (h 0).1 := by
        have huH : u ∈ C.H := Finset.mem_union_left C.X huA1
        obtain ⟨j, hj⟩ := h.surjective ⟨u, huH⟩
        have hjVal : (h j).1 = u := congrArg Subtype.val hj
        have hjCases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
        rcases hjCases with hj0 | hj1 | hj2
        · have : j = 0 := Fin.ext hj0
          simpa [this] using hjVal.symm
        · have : j = 1 := Fin.ext hj1
          exfalso
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) huA1
              (hjVal ▸ this ▸ hH1)
        · have : j = 2 := Fin.ext hj2
          exfalso
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) huA1
              (hjVal ▸ this ▸ hH2)
      have hh : (a ⟨t + 2, by omega⟩).1 = (h ⟨t + 1, by omega⟩).1 := by
        simpa using hAH ⟨t + 1, by omega⟩
      simpa [huEq, hh] using hut
    · obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
      refine ⟨i + 1, by omega, ?_⟩
      simp only [predecessor, htx, if_pos, show i.val + 1 ≠ 0 by omega,
        if_false, show i.val + 1 - 1 = i.val by omega]
      rw [pToH_coreBits G _ _ _ _ i (t + 1) i.isLt (by omega),
        decide_eq_true_eq]
      simpa [Subtype.ext_iff.mp hi] using hut
  · have ht2 : 2 ≤ t := by omega
    obtain ⟨u, huP, hut⟩ := external_has_P_predecessor G C
      (e ⟨t - 2, by omega⟩).1 (e ⟨t - 2, by omega⟩).2
    obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
    refine ⟨i + 1, by omega, ?_⟩
    simp only [predecessor, if_neg htx, show i.val + 1 ≠ 0 by omega,
      if_false, show i.val + 1 - 1 = i.val by omega]
    rw [pToE_coreBits G _ _ _ _ i (t - 2) i.isLt (by omega),
      decide_eq_true_eq]
    simpa [Subtype.ext_iff.mp hi] using hut

omit [Fintype V] in
theorem secondP_true_mem (P H : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 3 ≃ {v : V // v ∈ H})
    (e : Fin 5 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7)
    (hSecond : (decide (j ≠ i) &&
      !pArc (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i j &&
      reachedP (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i j) = true) :
    (p ⟨j, hj⟩).1 ∈ secondNeighborsThrough G P (P ∪ H) (p ⟨i, hi⟩).1 := by
  classical
  let bits := coreBits G (fun k => (p k).1) (fun k => (h k).1) e a
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hji, hNotArcBool⟩, hReach⟩
  have hNotArc : ¬G.Adj (p ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 := by
    have hFalse := Bool.eq_false_of_not_eq_true' hNotArcBool
    rw [pArc_coreBits G _ _ _ _ i j hi hj] at hFalse
    simpa only [decide_eq_false_iff_not] using hFalse
  have hTargetNe : (p ⟨j, hj⟩).1 ≠ (p ⟨i, hi⟩).1 := by
    intro hEq
    have hFin : (⟨j, hj⟩ : Fin 7) = ⟨i, hi⟩ := by
      apply p.injective
      exact Subtype.ext hEq
    exact hji (Fin.ext_iff.mp hFin)
  have hWitness : ∃ w ∈ P ∪ H,
      G.Adj (p ⟨i, hi⟩).1 w ∧ G.Adj w (p ⟨j, hj⟩).1 := by
    simp only [reachedP, Bool.or_eq_true] at hReach
    rcases hReach with hViaP | hViaH
    · rw [any_eq_true_iff] at hViaP
      obtain ⟨m, hm, hPath⟩ := hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmi, _hmj⟩, hFirst⟩, hLast⟩
      rw [pArc_coreBits G _ _ _ _ i m hi hm, decide_eq_true_eq] at hFirst
      rw [pArc_coreBits G _ _ _ _ m j hm hj, decide_eq_true_eq] at hLast
      exact ⟨(p ⟨m, hm⟩).1, Finset.mem_union_left H (p ⟨m, hm⟩).2,
        hFirst, hLast⟩
    · rw [any_eq_true_iff] at hViaH
      obtain ⟨m, hm, hPath⟩ := hViaH
      simp only [Bool.and_eq_true] at hPath
      rw [pToH_coreBits G _ _ _ _ i m hi hm, decide_eq_true_eq] at hPath
      rw [hToP_coreBits G _ _ _ _ m j hm hj, decide_eq_true_eq] at hPath
      exact ⟨(h ⟨m, hm⟩).1, Finset.mem_union_right P (h ⟨m, hm⟩).2,
        hPath.1, hPath.2⟩
  unfold secondNeighborsThrough
  apply Finset.mem_filter.mpr
  exact ⟨(p ⟨j, hj⟩).2, hNotArc, hTargetNe, hWitness⟩

omit [Fintype V] in
theorem secondP_toNat_le_qCount (P H : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 3 ≃ {v : V // v ∈ H})
    (e : Fin 5 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 7) :
    (secondP (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i).toNat ≤
      qCount G P H (p ⟨i, hi⟩).1 := by
  classical
  rw [secondP, toNat_count_eq_fin_sum 7 _ (by omega)]
  unfold qCount secondNeighborsThrough
  rw [filterCard_eq_sum_fin P p]
  let b : Nat → Bool := fun j => decide (j ≠ i) &&
    !pArc (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i j &&
    reachedP (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i j
  let Q : V → Prop := fun v =>
    ¬G.Adj (p ⟨i, hi⟩).1 v ∧ v ≠ (p ⟨i, hi⟩).1 ∧
      ∃ w ∈ P ∪ H, G.Adj (p ⟨i, hi⟩).1 w ∧ G.Adj w v
  change (∑ j : Fin 7, if b j then 1 else 0) ≤
    ∑ j : Fin 7, if Q (p j).1 then 1 else 0
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · have hb' : (decide (j.val ≠ i) &&
        !pArc (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i j.val &&
        reachedP (coreBits G (fun k => (p k).1) (fun k => (h k).1) e a) i j.val) = true := by
      exact hb
    have hmem := secondP_true_mem G P H p h e a i j hi j.isLt hb'
    have hpred := (Finset.mem_filter.mp hmem).2
    have hQ : Q (p j).1 := hpred
    simp [hb, hQ]
  · have hbf : b j = false := Bool.eq_false_of_not_eq_true hb
    simp [hbf]

theorem pDegree_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 ≃ {v : V // v ∈ externalTargets G C})
    (a : Fin 8 → V) (i : Nat) (hi : i < 7) :
    (pDegree (coreBits G (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) a) i).toNat = G.outdegree (p ⟨i, hi⟩).1 := by
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) a
  let u := (p ⟨i, hi⟩).1
  have hPP := pOut_toNat G C.P p (fun j => (h j).1) (fun j => (e j).1) a i hi
  have hPH := pHOut_toNat G C.H (fun j => (p j).1) h
    (fun j => (e j).1) a i hi
  have hPE := pEOut_toNat G (externalTargets G C) (fun j => (p j).1)
    (fun j => (h j).1) e a i hi
  change (pOut bits i).toNat = directCount G C.P u at hPP
  change (pHOut bits i).toNat = directCount G C.H u at hPH
  change (pEOut bits i).toNat = directCount G (externalTargets G C) u at hPE
  have hGraph := BSixKTwoCoreGraphBridge.outdegree_P_eq_blocks
    G C hG hPB u (p ⟨i, hi⟩).2
  change G.outdegree u = directCount G (externalTargets G C) u +
    directCount G C.A1 u + directCount G C.X u + directCount G C.P u at hGraph
  have hH : directCount G C.H u =
      directCount G C.A1 u + directCount G C.X u := by
    rw [Digraph.LocalConfiguration.H,
      directCount_union_of_disjoint G C.A1 C.X u
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)]
  have hPPLe : directCount G C.P u ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr p).symm)
  have hPHLe : directCount G C.H u ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr h).symm)
  have hPELe : directCount G (externalTargets G C) u ≤ 5 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr e).symm)
  change (pOut bits i + pHOut bits i + pEOut bits i).toNat = G.outdegree u
  simp only [BitVec.toNat_add, Nat.reducePow, hPP, hPH, hPE]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem rootEquation_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 ≃ {v : V // v ∈ externalTargets G C})
    (a : Fin 8 → V) (hE0 : (e 0).1 = C.s)
    (i : Nat) (hi : i < 7) :
    rootEquation (coreBits G (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) a) i = true := by
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) a
  let u := (p ⟨i, hi⟩).1
  have hRootBit : pToE bits i 0 = decide (G.Adj u C.s) := by
    rw [pToE_coreBits G _ _ _ _ i 0 hi (by omega)]
    rw [show (e ⟨0, by omega⟩).1 = (e 0).1 by rfl, hE0]
  by_cases hps : G.Adj u C.s
  · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
      G C hG hPB hNoSeymour hRootDegree u (p ⟨i, hi⟩).2 hps
    have hSecond := secondP_toNat_le_qCount G C.P C.H p h
      (fun j => (e j).1) a i hi
    have hPP := pOut_toNat G C.P p (fun j => (h j).1)
      (fun j => (e j).1) a i hi
    have hPH := pHOut_toNat G C.H (fun j => (p j).1) h
      (fun j => (e j).1) a i hi
    have hPE := pEOut_toNat G (externalTargets G C) (fun j => (p j).1)
      (fun j => (h j).1) e a i hi
    change (secondP bits i).toNat ≤ qCount G C.P C.H u at hSecond
    change (pOut bits i).toNat = directCount G C.P u at hPP
    change (pHOut bits i).toNat = directCount G C.H u at hPH
    change (pEOut bits i).toNat = directCount G (externalTargets G C) u at hPE
    have hExternal := BSixKTwoCoreGraphBridge.directCount_externalTargets
      G C u (p ⟨i, hi⟩).2
    have hEpsilon : epsilonAt G u C.s = 1 := by simp [epsilonAt, hps]
    have hQLe : qCount G C.P C.H u ≤ 7 := by
      unfold qCount secondNeighborsThrough
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr p).symm)
    have hPPLe : directCount G C.P u ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr p).symm)
    have hPHLe : directCount G C.H u ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr h).symm)
    have hPELe : directCount G (externalTargets G C) u ≤ 5 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr e).symm)
    have hLeft : (secondP bits i + 9).toNat = (secondP bits i).toNat + 9 := by
      simp only [BitVec.toNat_add, Nat.reducePow]
      rw [show (9 : BitVec 8).toNat = 9 by decide]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hMul : (2 * pHOut bits i).toNat = 2 * (pHOut bits i).toNat := by
      simp only [BitVec.toNat_mul, Nat.reducePow]
      rw [show (2 : BitVec 8).toNat = 2 by decide,
        Nat.mod_eq_of_lt (by omega)]
    have hRight : (pEOut bits i + 2 * pHOut bits i + pOut bits i).toNat =
        (pEOut bits i).toNat + 2 * (pHOut bits i).toNat +
          (pOut bits i).toNat := by
      simp only [BitVec.toNat_add, Nat.reducePow, hMul]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    change rootEquation bits i = true
    simp only [rootEquation, hRootBit, hps, decide_true, Bool.not_true,
      Bool.false_or, BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hLeft, hRight, hPE, hPH, hPP, hExternal]
    rw [hEpsilon] at hEquation
    omega
  · change rootEquation bits i = true
    simp [rootEquation, hRootBit, hps]

theorem totalPToH_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (e : Fin 5 → V) (a : Fin 8 → V) :
    (sumCount 7 (pHOut (coreBits G (fun j => (p j).1)
      (fun j => (h j).1) e a))).toNat = edgeCount G C.P C.H := by
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1) e a
  have hSum : (∑ i ∈ Finset.range 7, (pHOut bits i).toNat) =
      edgeCount G C.P C.H := by
    rw [← Fin.sum_univ_eq_sum_range, edgeCount_eq_sum_fin G C.P C.H p]
    apply Finset.sum_congr rfl
    intro i hi
    exact pHOut_toNat G C.H (fun j => (p j).1) h e a i i.isLt
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 3 := by simpa using (Fintype.card_congr h).symm
  have hlt : ∑ i ∈ Finset.range 7, (pHOut bits i).toNat < 256 := by
    rw [hSum]
    rw [hPCard, hHCard] at hCap
    omega
  rw [toNat_sumCount 7 _ hlt, hSum]

theorem totalHToP_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (e : Fin 5 → V) (a : Fin 8 → V) :
    (sumCount 3 (hPOut (coreBits G (fun j => (p j).1)
      (fun j => (h j).1) e a))).toNat = edgeCount G C.H C.P := by
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1) e a
  have hSum : (∑ i ∈ Finset.range 3, (hPOut bits i).toNat) =
      edgeCount G C.H C.P := by
    rw [← Fin.sum_univ_eq_sum_range, edgeCount_eq_sum_fin G C.H C.P h]
    apply Finset.sum_congr rfl
    intro i hi
    exact hPOut_toNat G C.P p (fun j => (h j).1) e a i i.isLt
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 3 := by simpa using (Fintype.card_congr h).symm
  have hlt : ∑ i ∈ Finset.range 3, (hPOut bits i).toNat < 256 := by
    rw [hSum]
    rw [hPCard, hHCard] at hCap
    omega
  rw [toNat_sumCount 3 _ hlt, hSum]

theorem aggregateRows_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPB : C.P = C.B) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 1) (hx : C.x = 2)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (e : Fin 5 → V) (a : Fin 8 → V) :
    (11 : BitVec 8).ule (sumCount 3 (hPOut (coreBits G
      (fun j => (p j).1) (fun j => (h j).1) e a))) = true ∧
    (sumCount 7 (pHOut (coreBits G (fun j => (p j).1)
      (fun j => (h j).1) e a))).ule 10 = true := by
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1) e a
  have hHP := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB
    hRootDegree hk
  rw [hx] at hHP
  norm_num [Nat.choose] at hHP
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 3 := by simpa using (Fintype.card_congr h).symm
  rw [hPCard, hHCard] at hCross
  have hPH : edgeCount G C.P C.H ≤ 10 := by omega
  have hHPNat := totalHToP_toNat G C p h e a
  have hPHNat := totalPToH_toNat G C p h e a
  change (sumCount 3 (hPOut bits)).toNat = _ at hHPNat
  change (sumCount 7 (pHOut bits)).toNat = _ at hPHNat
  constructor
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHPNat]
    exact hHP
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hPHNat]
    exact hPH

theorem uSecondA_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 → V) (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (target : Fin 8)
    (hb : (decide (target.val ≠ 1) &&
      !hToA (coreBits G p (fun j => (h j).1) e (fun j => (a j).1)) 0 target.val &&
      any 2 (fun q =>
        hToA (coreBits G p (fun j => (h j).1) e (fun j => (a j).1)) 0 (q + 2) &&
        hToA (coreBits G p (fun j => (h j).1) e (fun j => (a j).1)) (q + 1)
          target.val)) = true) :
    (a target).1 ∈ G.secondOutNeighborFinset (h 0).1 := by
  let bits := coreBits G p (fun j => (h j).1) e (fun j => (a j).1)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with ⟨⟨htNe, hNotBool⟩, hReach⟩
  have hNot : ¬G.Adj (h 0).1 (a target).1 := by
    have hf := Bool.eq_false_of_not_eq_true' hNotBool
    rw [hToA_coreBits G _ _ _ _ 0 target.val (by omega) target.isLt] at hf
    have h0 : (⟨0, by omega⟩ : Fin 3) = 0 := Fin.ext rfl
    have ht : (⟨target.val, target.isLt⟩ : Fin 8) = target := Fin.ext rfl
    rw [h0, ht] at hf
    simpa only [decide_eq_false_iff_not] using hf
  rw [any_eq_true_iff] at hReach
  obtain ⟨q, hq, hPath⟩ := hReach
  simp only [Bool.and_eq_true] at hPath
  rw [hToA_coreBits G _ _ _ _ 0 (q + 2) (by omega) (by omega),
    decide_eq_true_eq] at hPath
  rw [hToA_coreBits G _ _ _ _ (q + 1) target.val (by omega) target.isLt,
    decide_eq_true_eq] at hPath
  have hh : (a ⟨q + 2, by omega⟩).1 = (h ⟨q + 1, by omega⟩).1 := by
    simpa using hAH ⟨q + 1, by omega⟩
  have hFirst : G.Adj (h 0).1 (h ⟨q + 1, by omega⟩).1 := by
    simpa [hh] using hPath.1
  have hTargetNe : (a target).1 ≠ (h 0).1 := by
    intro heq
    have hIndex : target = (1 : Fin 8) := by
      apply a.injective
      apply Subtype.ext
      have ha1h0 : (a (1 : Fin 8)).1 = (h 0).1 := by
        simpa using hAH 0
      exact heq.trans ha1h0.symm
    exact htNe (Fin.ext_iff.mp hIndex)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(h ⟨q + 1, by omega⟩).1, hFirst, hPath.2⟩, hNot, hTargetNe⟩

theorem uSecondP_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 → V) (a : Fin 8 → V)
    (hAH : ∀ i : Fin 3, a ⟨i + 1, by omega⟩ = (h i).1)
    (target : Fin 7)
    (hb : (!hToP (coreBits G (fun j => (p j).1) (fun j => (h j).1) e a)
        0 target.val &&
      (any 7 (fun i => decide (i ≠ target.val) &&
        hToP (coreBits G (fun j => (p j).1) (fun j => (h j).1) e a) 0 i &&
        pArc (coreBits G (fun j => (p j).1) (fun j => (h j).1) e a) i target.val) ||
       any 2 (fun q =>
        hToA (coreBits G (fun j => (p j).1) (fun j => (h j).1) e a) 0 (q + 2) &&
        hToP (coreBits G (fun j => (p j).1) (fun j => (h j).1) e a) (q + 1)
          target.val))) = true) :
    (p target).1 ∈ G.secondOutNeighborFinset (h 0).1 := by
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1) e a
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hb
  rcases hb with ⟨hNotBool, hViaP | hViaH⟩
  all_goals
    have hNot : ¬G.Adj (h 0).1 (p target).1 := by
      have hf := Bool.eq_false_of_not_eq_true' hNotBool
      rw [hToP_coreBits G _ _ _ _ 0 target.val (by omega) target.isLt] at hf
      have h0 : (⟨0, by omega⟩ : Fin 3) = 0 := Fin.ext rfl
      have ht : (⟨target.val, target.isLt⟩ : Fin 7) = target := Fin.ext rfl
      rw [h0, ht] at hf
      simpa only [decide_eq_false_iff_not] using hf
    have hTargetNe : (p target).1 ≠ (h 0).1 := by
      intro heq
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) (h 0).2
          (heq ▸ (p target).2)
  · rw [any_eq_true_iff] at hViaP
    obtain ⟨m, hm, hPath⟩ := hViaP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
    rcases hPath with ⟨⟨_hne, hFirst⟩, hLast⟩
    rw [hToP_coreBits G _ _ _ _ 0 m (by omega) hm,
      decide_eq_true_eq] at hFirst
    rw [pArc_coreBits G _ _ _ _ m target.val hm target.isLt,
      decide_eq_true_eq] at hLast
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨(p ⟨m, hm⟩).1, hFirst, hLast⟩, hNot, hTargetNe⟩
  · rw [any_eq_true_iff] at hViaH
    obtain ⟨q, hq, hPath⟩ := hViaH
    simp only [Bool.and_eq_true] at hPath
    rw [hToA_coreBits G _ _ _ _ 0 (q + 2) (by omega) (by omega),
      decide_eq_true_eq] at hPath
    rw [hToP_coreBits G _ _ _ _ (q + 1) target.val (by omega) target.isLt,
      decide_eq_true_eq] at hPath
    have hh : (a ⟨q + 2, by omega⟩) = (h ⟨q + 1, by omega⟩).1 := by
      simpa using hAH ⟨q + 1, by omega⟩
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨(h ⟨q + 1, by omega⟩).1, hh ▸ hPath.1, hPath.2⟩,
      hNot, hTargetNe⟩

theorem uSecondE_true_mem (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 ≃ {v : V // v ∈ externalTargets G C})
    (a : Fin 8 → V) (target : Fin 5)
    (hb : any 7 (fun i =>
      hToP (coreBits G (fun j => (p j).1) (fun j => (h j).1)
        (fun j => (e j).1) a) 0 i &&
      pToE (coreBits G (fun j => (p j).1) (fun j => (h j).1)
        (fun j => (e j).1) a) i target.val) = true) :
    (e target).1 ∈ G.secondOutNeighborFinset (h 0).1 := by
  rw [any_eq_true_iff] at hb
  obtain ⟨m, hm, hPath⟩ := hb
  simp only [Bool.and_eq_true] at hPath
  rw [hToP_coreBits G _ _ _ _ 0 m (by omega) hm,
    decide_eq_true_eq] at hPath
  rw [pToE_coreBits G _ _ _ _ m target.val hm target.isLt,
    decide_eq_true_eq] at hPath
  have hCaptured := H_outgoingCaptured G C hG hPB (h 0).1 (h 0).2
  have hDisjoint := BSixKThreeCoreGraphBridge.disjoint_local_external G C hG
  have hNot : ¬G.Adj (h 0).1 (e target).1 := by
    intro hue
    have hLocal := hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr hue)
    have hLocalB : (e target).1 ∈ C.A ∪ C.B := by simpa [← hPB] using hLocal
    exact (Finset.disjoint_left.mp hDisjoint) hLocalB (e target).2
  have hTargetNe : (e target).1 ≠ (h 0).1 := by
    intro heq
    apply (Finset.disjoint_left.mp hDisjoint)
      (Finset.mem_union_left C.B
        (Digraph.LocalConfiguration.H_subset_A (G := G) C (h 0).2))
      (heq ▸ (e target).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨m, hm⟩).1, hPath.1, hPath.2⟩, hNot, hTargetNe⟩

theorem uNonSeymour_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (e : Fin 5 ≃ {v : V // v ∈ externalTargets G C})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = (h i).1) :
    uNonSeymour (coreBits G (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) (fun j => (a j).1)) = true := by
  classical
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (a j).1)
  let fA : Nat → Bool := fun target => decide (target ≠ 1) &&
    !hToA bits 0 target && any 2 (fun q =>
      hToA bits 0 (q + 2) && hToA bits (q + 1) target)
  let fP : Nat → Bool := fun target => !hToP bits 0 target &&
    (any 7 (fun i => decide (i ≠ target) && hToP bits 0 i &&
      pArc bits i target) ||
     any 2 (fun q => hToA bits 0 (q + 2) && hToP bits (q + 1) target))
  let fE : Nat → Bool := fun target =>
    any 7 (fun i => hToP bits 0 i && pToE bits i target)
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hLocalE := BSixKThreeCoreGraphBridge.disjoint_local_external G C hG
  have hInjective : Function.Injective (Sum.elim (fun i : Fin 8 => (a i).1)
      (Sum.elim (fun i : Fin 7 => (p i).1) (fun i : Fin 5 => (e i).1)) :
      Fin 8 ⊕ (Fin 7 ⊕ Fin 5) → V) := by
    intro x y hxy
    rcases x with i | (i | i) <;> rcases y with j | (j | j)
    · have hij : i = j := a.injective (Subtype.ext hxy)
      simp [hij]
    · exfalso
      change (a i).1 = (p j).1 at hxy
      exact (Finset.disjoint_left.mp hAP) (a i).2 (hxy ▸ (p j).2)
    · exfalso
      change (a i).1 = (e j).1 at hxy
      exact (Finset.disjoint_left.mp hLocalE)
        (Finset.mem_union_left C.B (a i).2) (hxy ▸ (e j).2)
    · exfalso
      change (p i).1 = (a j).1 at hxy
      exact (Finset.disjoint_left.mp hAP) (a j).2 (hxy.symm ▸ (p i).2)
    · have hij : i = j := p.injective (Subtype.ext hxy)
      simp [hij]
    · exfalso
      change (p i).1 = (e j).1 at hxy
      exact (Finset.disjoint_left.mp hLocalE)
        (Finset.mem_union_right C.A
          (Digraph.LocalConfiguration.P_subset_B (G := G) C (p i).2))
        (hxy ▸ (e j).2)
    · exfalso
      change (e i).1 = (a j).1 at hxy
      exact (Finset.disjoint_left.mp hLocalE)
        (Finset.mem_union_left C.B (a j).2) (hxy.symm ▸ (e i).2)
    · exfalso
      change (e i).1 = (p j).1 at hxy
      exact (Finset.disjoint_left.mp hLocalE)
        (Finset.mem_union_right C.A
          (Digraph.LocalConfiguration.P_subset_B (G := G) C (p j).2))
        (hxy.symm ▸ (e i).2)
    · have hij : i = j := e.injective (Subtype.ext hxy)
      simp [hij]
  have hRepresented := BSixKTwoCoreGraphBridge.three_trueCounts_le_card
    fA fP fE (fun i : Fin 8 => (a i).1) (fun i : Fin 7 => (p i).1)
      (fun i : Fin 5 => (e i).1) (G.secondOutNeighborFinset (h 0).1)
      hInjective
      (fun i hb => uSecondA_true_mem G C (fun j => (p j).1) h
        (fun j => (e j).1) a hAH i hb)
      (fun i hb => uSecondP_true_mem G C p h (fun j => (e j).1)
        (fun j => (a j).1) (fun q => hAH q) i hb)
      (fun i hb => uSecondE_true_mem G C hG hPB p h e
        (fun j => (a j).1) i hb)
  have hANat : (uSecondA bits).toNat = BSixKTwoCoreBridge.trueCount 8 fA := by
    change (count 8 fA).toNat = _
    exact count_toNat_eq_trueCount 8 fA (by omega)
  have hPNat : (uSecondP bits).toNat = BSixKTwoCoreBridge.trueCount 7 fP := by
    change (count 7 fP).toNat = _
    exact count_toNat_eq_trueCount 7 fP (by omega)
  have hENat : (uSecondE bits).toNat = BSixKTwoCoreBridge.trueCount 5 fE := by
    change (count 5 fE).toNat = _
    exact count_toNat_eq_trueCount 5 fE (by omega)
  have hSecond : (uSecondA bits).toNat + (uSecondP bits).toNat +
      (uSecondE bits).toNat ≤ G.secondOutdegree (h 0).1 := by
    rw [hANat, hPNat, hENat]
    exact hRepresented
  have hNo : G.secondOutdegree (h 0).1 + 1 ≤ G.outdegree (h 0).1 := by
    have hn : ¬G.IsSeymourVertex (h 0).1 := by
      intro hs
      exact hNoSeymour ⟨_, hs⟩
    unfold Digraph.IsSeymourVertex at hn
    omega
  have hH0 : (h 0).1 ∈ C.H := (h 0).2
  have hDegEq := H_degree_eq_A_add_P G C hG hPB (h 0).1 hH0
  have hDA := hAOut_toNat G C.A (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) a 0 (by omega)
  have hDP := hPOut_toNat G C.P p (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (a j).1) 0 (by omega)
  change (hAOut bits 0).toNat = directCount G C.A (h 0).1 at hDA
  change (hPOut bits 0).toNat = directCount G C.P (h 0).1 at hDP
  have hALe : directCount G C.A (h 0).1 ≤ 8 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr a).symm)
  have hPLe : directCount G C.P (h 0).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr p).symm)
  have hDegreeNat : (hDegree bits 0).toNat = G.outdegree (h 0).1 := by
    change (hAOut bits 0 + hPOut bits 0).toNat = _
    simp only [BitVec.toNat_add, Nat.reducePow, hDA, hDP]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hDegEq.symm
  have hALe8 : (uSecondA bits).toNat ≤ 8 := by rw [hANat]; exact BSixKTwoCoreBridge.trueCount_le 8 fA
  have hPLe7 : (uSecondP bits).toNat ≤ 7 := by rw [hPNat]; exact BSixKTwoCoreBridge.trueCount_le 7 fP
  have hELe5 : (uSecondE bits).toNat ≤ 5 := by rw [hENat]; exact BSixKTwoCoreBridge.trueCount_le 5 fE
  have hLeft : (uSecondA bits + uSecondP bits + uSecondE bits + 1).toNat =
      (uSecondA bits).toNat + (uSecondP bits).toNat +
        (uSecondE bits).toNat + 1 := by
    simp only [BitVec.toNat_add, Nat.reducePow]
    rw [show (1 : BitVec 8).toNat = 1 by decide,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  change (uSecondA bits + uSecondP bits + uSecondE bits + 1).ule
    (hDegree bits 0) = true
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hLeft, hDegreeNat]
  omega

theorem tightEpsilonOneXTwoImpossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1)
    (hx : C.x = 2) (hz : C.z = 4) : False := by
  classical
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hHCard : C.H.card = 3 := by
    change C.h = 3
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hECard : (externalTargets G C).card = 5 := by
    rw [card_externalTargets G C, hz, hEpsilon]
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 1 := by change C.A1.card = 1 at hk; exact hk
  have hXCard : C.X.card = 2 := by change C.X.card = 2 at hx; exact hx
  have hRCard : C.R.card = 4 := by
    have hXR := x_add_card_R_eq_six G C hG hRootDegree hk
    change C.X.card = 2 at hx
    change C.X.card + C.R.card = 6 at hXR
    omega
  have hReach : ∃ u ∈ C.P, G.Adj u C.s := by
    rw [epsilonS_eq_ite] at hEpsilon
    by_cases hr : ∃ u ∈ C.P, G.Adj u C.s
    · exact hr
    · simp [hr] at hEpsilon
  have hsE : C.s ∈ externalTargets G C := by
    apply Finset.mem_union_right C.Z
    simp [rootSecondFinset, hReach]
  let p : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let eA1 : Fin 1 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let h : Fin 3 ≃ {v : V // v ∈ C.H} :=
    FiveZExactLabels.hLabelEquiv G C hHCard eA1 eX
  let eR : Fin 4 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a : Fin 8 ≃ {v : V // v ∈ C.A} :=
    FiveZExactLabels.aLabelEquiv G C hACard h eR
  let e : Fin 5 ≃ {v : V // v ∈ externalTargets G C} :=
    FiveZExactLabels.finsetEquivFinAtZero (externalTargets G C) (by omega)
      hECard C.s hsE
  have hE0 : (e 0).1 = C.s :=
    FiveZExactLabels.finsetEquivFinAtZero_zero (externalTargets G C)
      (by omega) hECard C.s hsE
  have hA0 : (a 0).1 = C.a1 :=
    FiveZExactLabels.aLabelEquiv_zero G C hACard h eR
  have hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1 := by
    intro j
    exact FiveZExactLabels.aLabelEquiv_h G C hACard h eR j
  have hAR : ∀ q : Nat, (hq : q < 4) → (a ⟨q + 4, by omega⟩).1 ∈ C.R := by
    intro q hq
    rw [FiveZExactLabels.aLabelEquiv_r G C hACard h eR ⟨q, hq⟩]
    exact (eR ⟨q, hq⟩).2
  have hH0 : (h 0).1 ∈ C.A1 := by
    rw [FiveZExactLabels.hLabelEquiv_zero G C hHCard eA1 eX]
    exact (eA1 0).2
  have hH1 : (h 1).1 ∈ C.X := by
    rw [FiveZExactLabels.hLabelEquiv_one G C hHCard eA1 eX]
    exact (eX 0).2
  have hH2 : (h 2).1 ∈ C.X := by
    rw [FiveZExactLabels.hLabelEquiv_two G C hHCard eA1 eX]
    exact (eX 1).2
  let bits := coreBits G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (a j).1)
  have hOrP := orientedOnP_true G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (a j).1) hG
  have hOrPH := orientedPH_true G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (a j).1) hG
  have hFixed := fixedHStructure_true G C hG hMin hPivot hPB hk p h
    (fun j => (e j).1) a hA0 hAH hH0 hH1 hH2 hAR
  have hTarget := targetCovered_true G C p h e a hAH hH0 hH1 hH2
  have hExternal := externalCoverage_true G C p (fun j => (h j).1) e
    (fun j => (a j).1)
  have hRows : all 7 (fun i => (8 : BitVec 8).ule (pDegree bits i) &&
      rootEquation bits i) = true := by
    rw [all_eq_true_iff]
    intro i hi
    simp only [Bool.and_eq_true]
    constructor
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [pDegree_toNat G C hG hPB p h e (fun j => (a j).1) i hi]
      simpa using hMin (p ⟨i, hi⟩).1
    · exact rootEquation_true G C hG hPB hNoSeymour hRootDegree
        p h e (fun j => (a j).1) hE0 i hi
  have hAgg := aggregateRows_true G C hG hMin hPB hRootDegree hk hx p h
    (fun j => (e j).1) (fun j => (a j).1)
  have hU := uNonSeymour_true G C hG hPB hNoSeymour p h e a hAH
  have hCore : core bits = true := by
    rw [core]
    simp only [Bool.and_eq_true]
    refine ⟨?_, hU⟩
    refine ⟨?_, hAgg.2⟩
    refine ⟨?_, hAgg.1⟩
    refine ⟨?_, hRows⟩
    refine ⟨?_, hExternal⟩
    refine ⟨?_, hTarget⟩
    refine ⟨?_, hFixed⟩
    exact ⟨hOrP, hOrPH⟩
  have hFalse := EpsilonOneXTwoCore.core_unsat bits
  rw [hFalse] at hCore
  contradiction

end SeymourEight.EpsilonOneXTwoGraphBridge
