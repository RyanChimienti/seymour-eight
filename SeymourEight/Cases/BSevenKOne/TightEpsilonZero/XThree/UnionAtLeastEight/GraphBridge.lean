import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.CoreBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.FiveZUnionEightCapacity
import SeymourEight.Cases.BSevenKOne.Counting
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

namespace SeymourEight.FourZUnionEightGraphBridge

open FourZUnionEight FourZUnionEightBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZUnionEightCapacity FiveZExactPBridge
  FiveZExactCoreBridge FiveZExactGlobalBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 4 → V)
    (i : Nat) (hi : i < 7) :
    (FourZUnionEight.pOut (coreBits G.Adj (fun j ↦ (p j).1) h) i).toNat =
      directCount G C.P (p ⟨i, hi⟩).1 := by
  rw [FourZUnionEight.pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) h i j hi j.isLt]
  simp

theorem pHOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (i : Nat) (hi : i < 7) :
    (FourZUnionEight.pHOut (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) i).toNat =
      directCount G C.H (p ⟨i, hi⟩).1 := by
  rw [FourZUnionEight.pHOut, toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H h
  intro j
  rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    i j hi j.isLt]
  simp

theorem sumPOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 4 → V) :
    (sumCount 7 (FourZUnionEight.pOut
      (coreBits G.Adj (fun j ↦ (p j).1) h))).toNat = edgeCount G C.P C.P := by
  rw [toNat_sumCount_of_le 7 7 _ (by omega)]
  · rw [← Fin.sum_univ_eq_sum_range, edgeCount_eq_sum_fin G C.P C.P p]
    apply Finset.sum_congr rfl
    intro i hi
    exact pOut_toNat G C p h i i.isLt
  · intro i hi
    rw [FourZUnionEight.pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    calc _ ≤ ∑ _j : Fin 7, 1 := by
            apply Finset.sum_le_sum; intro j hj; split <;> omega
         _ = 7 := by simp

theorem totalPToH_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) :
    (FourZUnionEight.totalPToH (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1))).toNat =
      edgeCount G C.P C.H := by
  rw [FourZUnionEight.totalPToH, toNat_count_eq_fin_sum 28 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.P C.H p]
  simp_rw [directCount_eq_sum_fin G C.H h]
  simp only [Fin.sum_univ_succ]
  simp [FourZUnionEightBridge.pToH_coreBits, Nat.add_assoc]

theorem totalHToP_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) :
    (FourZUnionEight.totalHToP (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1))).toNat =
      edgeCount G C.H C.P := by
  rw [FourZUnionEight.totalHToP, toNat_count_eq_fin_sum 28 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.H C.P h]
  simp_rw [directCount_eq_sum_fin G C.P p]
  simp only [Fin.sum_univ_succ]
  simp [FourZUnionEightBridge.hToP_coreBits, Nat.add_assoc]

private def missingPairIndicator (G : Digraph V) [DecidableRel G.Adj]
    (p : Fin 7 → V)
    (i j : Fin 7) : Nat :=
  if ¬G.Adj (p i) (p j) ∧ ¬G.Adj (p j) (p i) then 1 else 0

private def arcIndicator (G : Digraph V) [DecidableRel G.Adj] (p : Fin 7 → V)
    (i j : Fin 7) : Nat := if G.Adj (p i) (p j) then 1 else 0

private def pairTotal (G : Digraph V) [DecidableRel G.Adj]
    (p : Fin 7 → V) (i j : Fin 7) : Nat :=
  missingPairIndicator G p i j + arcIndicator G p i j + arcIndicator G p j i

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
    (∑ q, f q) = ∑ i : Fin 7, ∑ j : Fin 7, f ⟨i * 7 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 7 × Fin 7 ≃ Fin 49).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

private theorem div_index (i j width : Nat) (hj : j < width) :
    (i * width + j) / width = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j width : Nat) (hj : j < width) :
    (i * width + j) % width = j := Nat.mul_add_mod_of_lt hj

set_option maxHeartbeats 2000000 in
theorem totalMissingPPairs_toNat_add_edges (C : G.LocalConfiguration)
    (hG : G.IsOriented) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) :
    (FourZUnionEight.totalMissingPPairs
        (coreBits G.Adj (fun j ↦ (p j).1) h)).toNat +
      edgeCount G C.P C.P = 21 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h
  rw [FourZUnionEight.totalMissingPPairs,
    toNat_count_eq_fin_sum 49 _ (by omega)]
  rw [sum_fin49_eq_blocks]
  rw [edgeCount_eq_sum_fin G C.P C.P p]
  simp_rw [directCount_eq_sum_fin G C.P p]
  simp only [Fin.sum_univ_succ]
  simp [
    FourZUnionEightBridge.pArc_coreBits, Bool.and_eq_true,
    decide_eq_true_eq, decide_eq_false_iff_not]
  have h01 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 0 1
  have h02 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 0 2
  have h03 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 0 3
  have h04 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 0 4
  have h05 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 0 5
  have h06 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 0 6
  have h12 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 1 2
  have h13 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 1 3
  have h14 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 1 4
  have h15 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 1 5
  have h16 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 1 6
  have h23 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 2 3
  have h24 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 2 4
  have h25 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 2 5
  have h26 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 2 6
  have h34 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 3 4
  have h35 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 3 5
  have h36 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 3 6
  have h45 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 4 5
  have h46 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 4 6
  have h56 := pairTotal_eq_one G hG (fun i ↦ (p i).1) 5 6
  have hl0 : ¬G.Adj (p 0).1 (p 0).1 := hG.1 _
  have hl1 : ¬G.Adj (p 1).1 (p 1).1 := hG.1 _
  have hl2 : ¬G.Adj (p 2).1 (p 2).1 := hG.1 _
  have hl3 : ¬G.Adj (p 3).1 (p 3).1 := hG.1 _
  have hl4 : ¬G.Adj (p 4).1 (p 4).1 := hG.1 _
  have hl5 : ¬G.Adj (p 5).1 (p 5).1 := hG.1 _
  have hl6 : ¬G.Adj (p 6).1 (p 6).1 := hG.1 _
  simp only [pairTotal, missingPairIndicator, arcIndicator] at h01 h02 h03 h04 h05 h06 h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
  simp [hl0, hl1, hl2, hl3, hl4, hl5, hl6]
  omega

theorem pDegree_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (i : Nat) (hi : i < 7) :
    (FourZUnionEight.pDegree missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) i).toNat =
      G.outdegree (p ⟨i, hi⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
  have hH := pHOut_toNat G C p h i hi
  have hP := pOut_toNat G C p (fun j ↦ (h j).1) i hi
  have hZ : (externalFirst missing i).toNat =
      directCount G C.Z (p ⟨i, hi⟩).1 := by
    unfold externalFirst
    split
    · rename_i hc
      have hex : missing = 1 ∧ i = 0 := by simpa [Bool.and_eq_true] using hc
      rw [hRows i hi, if_pos hex]
      rfl
    · rename_i hc
      have hex : ¬(missing = 1 ∧ i = 0) := by
        simpa [Bool.and_eq_true] using hc
      rw [hRows i hi, if_neg hex]
      rfl
  have hZLe : directCount G C.Z (p ⟨i, hi⟩).1 ≤ 4 := by
    rw [hRows i hi]
    split <;> omega
  have hHLe : directCount G C.H (p ⟨i, hi⟩).1 ≤ 4 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr h).symm)
  have hPLe : directCount G C.P (p ⟨i, hi⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  rw [FourZUnionEight.pDegree, BitVec.toNat_add, BitVec.toNat_add, hZ, hH, hP]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon _ (p ⟨i, hi⟩).2]

private theorem ordered_index_lt (missing q : Nat)
    (hq : q < 6 - (if missing = 1 then 1 else 0)) :
    q + (if missing = 1 then 1 else 0) < 7 := by
  by_cases hm : missing = 1 <;> simp [hm] at hq ⊢ <;> omega

private theorem ordered_index_succ_lt (missing q : Nat)
    (hq : q < 6 - (if missing = 1 then 1 else 0)) :
    q + (if missing = 1 then 1 else 0) + 1 < 7 := by
  by_cases hm : missing = 1 <;> simp [hm] at hq ⊢ <;> omega

theorem orderedP_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hSorted : ∀ q : Nat, (hq : q < 6 - (if missing = 1 then 1 else 0)) →
      G.outdegree (p ⟨q + (if missing = 1 then 1 else 0) + 1,
          ordered_index_succ_lt missing q hq⟩).1 ≤
          G.outdegree (p ⟨q + (if missing = 1 then 1 else 0),
            ordered_index_lt missing q hq⟩).1 ∧
        (G.outdegree (p ⟨q + (if missing = 1 then 1 else 0),
            ordered_index_lt missing q hq⟩).1 =
            G.outdegree (p ⟨q + (if missing = 1 then 1 else 0) + 1,
              ordered_index_succ_lt missing q hq⟩).1 →
          directCount G C.H (p ⟨q + (if missing = 1 then 1 else 0) + 1,
            ordered_index_succ_lt missing q hq⟩).1 ≤
            directCount G C.H (p ⟨q + (if missing = 1 then 1 else 0),
              ordered_index_lt missing q hq⟩).1)) :
    FourZUnionEight.orderedP missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
  rw [FourZUnionEight.orderedP, all_eq_true_iff]
  intro q hq
  let first := if missing = 1 then 1 else 0
  let i := q + first
  have hs := hSorted q hq
  have hi : i < 7 := by
    simpa [i, first] using ordered_index_lt missing q hq
  have hi1 : i + 1 < 7 := by
    simpa [i, first] using ordered_index_succ_lt missing q hq
  have hd0 := pDegree_toNat G C hG hPB hEpsilon missing p h hRows i hi
  have hd1 := pDegree_toNat G C hG hPB hEpsilon missing p h hRows (i + 1) hi1
  have hh0 := pHOut_toNat G C p h i hi
  have hh1 := pHOut_toNat G C p h (i + 1) hi1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    BitVec.ule_eq_decide, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [hd1, hd0]
    simpa [i, first] using hs.1
  by_cases heq : FourZUnionEight.pDegree missing bits i =
      FourZUnionEight.pDegree missing bits (i + 1)
  · right
    have hdeg : G.outdegree (p ⟨i, hi⟩).1 = G.outdegree (p ⟨i + 1, hi1⟩).1 := by
      rw [← hd0, ← hd1, heq]
    rw [hh1, hh0]
    simpa [i, first] using hs.2 (by simpa [i, first] using hdeg)
  · left
    apply Bool.eq_false_iff.mpr
    intro hEq
    apply heq
    simpa [bits, i, first] using (beq_iff_eq.mp hEq)

theorem secondPCount_le (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (i : Nat) (hi : i < 7) :
    (FourZUnionEight.secondPCount
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) i).toNat ≤
      (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset (p ⟨i, hi⟩).1).card := by
  rw [FourZUnionEight.secondPCount]
  apply count_le_filterCard C.P p _
    (fun v ↦ v ∈ G.secondOutNeighborFinset (p ⟨i, hi⟩).1) (by omega)
  intro j hBit
  simp only [FourZUnionEight.secondPViaPOrH, Bool.and_eq_true,
    decide_eq_true_eq] at hBit
  rcases hBit with ⟨⟨hne, hNot⟩, hReach⟩
  have hNotArc : ¬G.Adj (p ⟨i, hi⟩).1 (p j).1 := by
    rw [FourZUnionEightBridge.pArc_coreBits G.Adj
      (fun q ↦ (p q).1) (fun q ↦ (h q).1)
      i j hi j.isLt] at hNot
    simpa using hNot
  have hVertexNe : (p j).1 ≠ (p ⟨i, hi⟩).1 := by
    intro heq
    have := p.injective (Subtype.ext heq)
    exact hne (Fin.ext_iff.mp this)
  have hPath : ∃ v, G.Adj (p ⟨i, hi⟩).1 v ∧ G.Adj v (p j).1 := by
    simp only [FourZUnionEight.reachedPViaPOrH, Bool.or_eq_true] at hReach
    rcases hReach with hp | hh
    · obtain ⟨k, hk, hkPath⟩ := (any_eq_true_iff 7 _).mp hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hkPath
      refine ⟨(p ⟨k, hk⟩).1, ?_, ?_⟩
      · rw [FourZUnionEightBridge.pArc_coreBits G.Adj
          (fun q ↦ (p q).1) (fun q ↦ (h q).1)
          i k hi hk] at hkPath
        exact of_decide_eq_true hkPath.1.2
      · rw [FourZUnionEightBridge.pArc_coreBits G.Adj
          (fun q ↦ (p q).1) (fun q ↦ (h q).1)
          k j hk j.isLt] at hkPath
        exact of_decide_eq_true hkPath.2
    · obtain ⟨k, hk, hkPath⟩ := (any_eq_true_iff 4 _).mp hh
      simp only [Bool.and_eq_true] at hkPath
      refine ⟨(h ⟨k, hk⟩).1, ?_, ?_⟩
      · rw [FourZUnionEightBridge.pToH_coreBits G.Adj
          (fun q ↦ (p q).1) (fun q ↦ (h q).1)
          i k hi hk] at hkPath
        exact of_decide_eq_true hkPath.1
      · rw [FourZUnionEightBridge.hToP_coreBits G.Adj
          (fun q ↦ (p q).1) (fun q ↦ (h q).1)
          k j hk j.isLt] at hkPath
        exact of_decide_eq_true hkPath.2
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hPath, hNotArc, hVertexNe⟩

set_option linter.flexible false in
/-- With only one missing `P → Z` incidence, the exceptional three-neighbor
row still reaches at least six external vertices through its direct `Z`s. -/
theorem six_le_directZExternal_of_three (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hPZ : edgeCount G C.P C.Z = 27) (u : V) (huP : u ∈ C.P)
    (hRow : directCount G C.Z u = 3) :
    6 ≤ (directZExternalUnion G C u).card := by
  let S := directZNeighbors G C u
  let T := C.Z \ S
  let U := directZExternalUnion G C u
  have hS : S ⊆ C.Z := directZNeighbors_subset_Z G C u
  have hSCard : S.card = 3 := hRow
  have hTCard : T.card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hZCard, hSCard]
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = C.Z := Finset.union_sdiff_of_subset hS
  have hPTLe : edgeCount G C.P T ≤ 6 := by
    calc
      edgeCount G C.P T ≤
          ∑ q ∈ C.P, if q = u then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqu : q = u
        · subst q
          simp
          unfold directCount CertificateBridge.internalFirstNeighbors
          apply Finset.card_eq_zero.mpr
          ext z
          simp only [Finset.notMem_empty, iff_false]
          intro hz
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
            (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp
              (Finset.mem_filter.mp hz).1).1, (Finset.mem_filter.mp hz).2⟩)
        · simp only [hqu, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by
        rw [← Finset.sum_erase_add C.P
          (fun q ↦ if q = u then 0 else T.card) huP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ x ∈ C.P.erase u, if x = u then 0 else T.card) =
              ∑ _x ∈ C.P.erase u, T.card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_neg (Finset.mem_erase.mp hx).1]
          _ = (C.P.erase u).card * T.card := by simp
          _ = 6 := by
            rw [Finset.card_erase_of_mem huP, hPCard, hTCard]
  have hPS : edgeCount G C.P S = 21 := by
    have hSplit : edgeCount G C.P C.Z =
        edgeCount G C.P S + edgeCount G C.P T := by
      rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
    have hCap := edgeCount_le_card_mul_card G C.P S
    rw [hPCard, hSCard] at hCap
    omega
  have hSP : edgeCount G S C.P = 0 := by
    have hCross := cross_edgeCount_add_reverse_le G C.P S hG
    rw [hPCard, hSCard, hPS] at hCross
    omega
  have hZZ : edgeCount G S C.Z ≤ 6 := by
    have hInternal := internal_edgeCount_le_choose_two G S hG
    have hCross := edgeCount_le_card_mul_card G S T
    have hSplit : edgeCount G S C.Z =
        edgeCount G S S + edgeCount G S T := by
      rw [← hUnion, edgeCount_union_of_disjoint G S S T hST]
    rw [hSCard] at hInternal
    rw [hSCard, hTCard] at hCross
    simp only [Nat.choose] at hInternal
    omega
  have hLower := directZ_capacity_lower G C hMin u
  change S.card * (8 - U.card) ≤ edgeCount G S C.Z + edgeCount G S C.P at hLower
  change 6 ≤ U.card
  rw [hSCard, hSP, Nat.add_zero] at hLower
  omega

set_option linter.flexible false in
theorem coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 1) (hx : C.x = 3) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (hZCard : C.Z.card = 4)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (missing degreeSum : Nat) (hMissing : missing ≤ 1)
    (hPZ : edgeCount G C.P C.Z + missing = 28)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hDegreeSum : ∑ u ∈ C.P, G.outdegree u = degreeSum)
    (hOrder : FourZUnionEight.orderedP missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) = true) :
    core missing degreeSum
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hSquare : orientedSquare 7 (pArc bits) = true := by
    rw [orientedSquare, all_eq_true_iff]
    intro i hi
    simp only [Bool.and_eq_true]
    constructor
    · rw [FourZUnionEightBridge.pArc_coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) i i hi hi]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      exact hG.1 _
    · rw [all_eq_true_iff]
      intro j hj
      rw [FourZUnionEightBridge.pArc_coreBits G.Adj
          (fun q ↦ (p q).1) (fun q ↦ (h q).1) i j hi hj,
        FourZUnionEightBridge.pArc_coreBits G.Adj
          (fun q ↦ (p q).1) (fun q ↦ (h q).1) j i hj hi]
      by_cases hij : i = j
      · simp [hij]
      · by_cases hf : G.Adj (p ⟨i, hi⟩).1 (p ⟨j, hj⟩).1
        · have hr : ¬G.Adj (p ⟨j, hj⟩).1 (p ⟨i, hi⟩).1 :=
            hG.2 hf
          simp [hij, hf, hr]
        · simp [hij, hf]
  have hPHOriented : FourZUnionEight.orientedPH bits = true := by
    rw [FourZUnionEight.orientedPH, all_eq_true_iff]
    intro i hi
    rw [all_eq_true_iff]
    intro j hj
    rw [FourZUnionEightBridge.pToH_coreBits G.Adj
      (fun q ↦ (p q).1) (fun q ↦ (h q).1)
      i j hi hj, FourZUnionEightBridge.hToP_coreBits G.Adj
      (fun q ↦ (p q).1) (fun q ↦ (h q).1)
      j i hj hi]
    by_cases hf : G.Adj (p ⟨i, hi⟩).1 (h ⟨j, hj⟩).1
    · have hr : ¬G.Adj (h ⟨j, hj⟩).1 (p ⟨i, hi⟩).1 := hG.2 hf
      simp [hf, hr]
    · simp [hf]
  have hHTotalNat := totalHToP_toNat G C p h
  have hHTotalLower : 14 ≤ edgeCount G C.H C.P := by
    have hc := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB hRootDegree hk
    simpa [hx, Nat.choose] using hc
  have hPTotalNat := totalPToH_toNat G C p h
  have hPTotalUpper : edgeCount G C.P C.H ≤ 14 := by
    have hc := cross_edgeCount_add_reverse_le G C.P C.H hG
    have hHCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
    rw [hPCard, hHCard] at hc
    omega
  have hPOutNat := sumPOut_toNat G C p (fun j ↦ (h j).1)
  have hMissingNat := totalMissingPPairs_toNat_add_edges G C hG p
    (fun j ↦ (h j).1)
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ u ∈ C.P, epsilonAt G u C.s = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [epsilonAt, FiveZExactPBridge.no_P_to_s_of_epsilonS_zero
      G C hEpsilon u hu]
  rw [hNoRoot, hDegreeSum] at hAccounting
  have hDefectEq : FourZUnionEight.totalMissingPPairs bits +
      (14 - FourZUnionEight.totalPToH bits) =
        BitVec.ofNat 8 (63 - missing - degreeSum) := by
    apply BitVec.eq_of_toNat_eq
    have hmLe : (FourZUnionEight.totalMissingPPairs bits).toNat ≤ 21 := by
      change (FourZUnionEight.totalMissingPPairs bits).toNat +
        edgeCount G C.P C.P = 21 at hMissingNat
      omega
    have hSubNat : (14 - FourZUnionEight.totalPToH bits).toNat =
        14 - edgeCount G C.P C.H := by
      have hle : (FourZUnionEight.totalPToH bits).toNat ≤ 14 := by
        rw [hPTotalNat]
        exact hPTotalUpper
      have hleBV : FourZUnionEight.totalPToH bits ≤ (14 : BitVec 8) := by
        rw [BitVec.le_def]
        simpa using hle
      rw [BitVec.toNat_sub_of_le hleBV, hPTotalNat]
      rfl
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), hSubNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    change (FourZUnionEight.totalMissingPPairs bits).toNat +
      edgeCount G C.P C.P = 21 at hMissingNat
    omega
  have hDegreePointwise : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (p ⟨i, hi⟩).1 ≤ 14 := by
    intro i hi
    rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon _ (p ⟨i, hi⟩).2]
    have hh : directCount G C.H (p ⟨i, hi⟩).1 ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr h).symm)
    have hpSubset : C.P.filter (G.Adj (p ⟨i, hi⟩).1) ⊆
        C.P.erase (p ⟨i, hi⟩).1 := by
      intro v hv
      apply Finset.mem_erase.mpr
      refine ⟨?_, (Finset.mem_filter.mp hv).1⟩
      intro hvu
      subst v
      exact hG.1 _ (Finset.mem_filter.mp hv).2
    have hp : directCount G C.P (p ⟨i, hi⟩).1 ≤ 6 := by
      unfold directCount CertificateBridge.internalFirstNeighbors
      calc
        (C.P.filter (G.Adj (p ⟨i, hi⟩).1)).card ≤
            (C.P.erase (p ⟨i, hi⟩).1).card := Finset.card_le_card hpSubset
        _ = 6 := by rw [Finset.card_erase_of_mem (p ⟨i, hi⟩).2, hPCard]
    rw [hRows i hi]
    split <;> omega
  have hRowsCore : all 7 (fun i ↦
      (8 : BitVec 8).ule (FourZUnionEight.pDegree missing bits i) &&
      (FourZUnionEight.pDegree missing bits i).ule 14 &&
        FourZUnionEight.pNonSeymour missing bits i) = true := by
    rw [all_eq_true_iff]
    intro i hi
    have hDegree := pDegree_toNat G C hG hPB hEpsilon missing p h hRows i hi
    have hDegreeUpper := hDegreePointwise i hi
    have hSecond := secondPCount_le G C p h i hi
    let u := (p ⟨i, hi⟩).1
    let S := directZNeighbors G C u
    let U := directZExternalUnion G C u
    have hULower : (externalSecondLower missing i).toNat ≤ U.card := by
      unfold externalSecondLower
      by_cases hex : missing = 1 ∧ i = 0
      · have hRowI : directCount G C.Z u = 3 := by
          change directCount G C.Z (p ⟨i, hi⟩).1 = 3
          simpa [hex] using hRows i hi
        simp [hex]
        have hm : missing = 1 := hex.1
        have hPZ' : edgeCount G C.P C.Z = 27 := by omega
        exact six_le_directZExternal_of_three G C hG hMin hPCard hZCard hPZ'
          u (p ⟨i, hi⟩).2 hRowI
      · have hRowI : directCount G C.Z u = 4 := by
          change directCount G C.Z (p ⟨i, hi⟩).1 = 4
          simpa [hex] using hRows i hi
        simp [hex]
        have hSCard : S.card = 4 := by exact hRowI
        have hSEq : S = C.Z := Finset.eq_of_subset_of_card_le
          (directZNeighbors_subset_Z G C u) (by rw [hSCard, hZCard])
        have hUEq : U = zExternalUnion G C := by
          simp [U, S, directZExternalUnion, zExternalUnion, hSEq]
        simpa [hUEq] using hFullUnion
    have hExternal := PSecond_add_directZExternal_card_le_second_add_H
      G C hG hPB hEpsilon u (p ⟨i, hi⟩).2
    have hHDecode := pHOut_toNat G C p h i hi
    change (FourZUnionEight.pDegree missing bits i).toNat = G.outdegree u at hDegree
    change (FourZUnionEight.pHOut bits i).toNat = directCount G C.H u at hHDecode
    change (FourZUnionEight.secondPCount bits i).toNat ≤
      (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset u).card at hSecond
    have hStrict : G.secondOutdegree u < G.outdegree u := by
      apply Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    have hDegreeUpperU : G.outdegree u ≤ 14 := by
      simpa [u] using hDegreeUpper
    have hsLe : (FourZUnionEight.secondPCount bits i).toNat ≤ 7 := by
      rw [FourZUnionEight.secondPCount, toNat_count_eq_fin_sum 7 _ (by omega)]
      calc _ ≤ ∑ _j : Fin 7, 1 := by
              apply Finset.sum_le_sum; intro j hj; split <;> omega
           _ = 7 := by simp
    have hhLe : (FourZUnionEight.pHOut bits i).toNat ≤ 4 := by
      rw [hHDecode]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr h).symm)
    have heLe : (externalSecondLower missing i).toNat ≤ 8 := by
      unfold externalSecondLower
      split <;> decide
    have hNon : FourZUnionEight.pNonSeymour missing bits i = true := by
      simp only [FourZUnionEight.pNonSeymour, BitVec.ult_eq_decide, decide_eq_true_eq]
      rw [BitVec.toNat_add, BitVec.toNat_add,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        hDegree, hHDecode]
      change (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset u).card + U.card ≤
        G.secondOutdegree u + directCount G C.H u at hExternal
      omega
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
    exact ⟨⟨by rw [hDegree]; exact hMin _, by rw [hDegree]; exact hDegreeUpper⟩, hNon⟩
  have hDegreeEq : sumCount 7 (FourZUnionEight.pDegree missing bits) =
      BitVec.ofNat 8 degreeSum := by
    have hDegreeSmall : degreeSum < 256 := by
      rw [← hDegreeSum, sum_finset_eq_sum_fin C.P p G.outdegree]
      calc
        (∑ i : Fin 7, G.outdegree (p i).1) ≤ ∑ _i : Fin 7, 14 := by
          apply Finset.sum_le_sum
          intro i hi
          exact hDegreePointwise i i.isLt
        _ = 98 := by simp
        _ < 256 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sumCount_of_le 7 15 _ (by omega)]
    · rw [← Fin.sum_univ_eq_sum_range]
      calc
        (∑ i : Fin 7, (FourZUnionEight.pDegree missing bits i).toNat) =
            ∑ i : Fin 7, G.outdegree (p i).1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact pDegree_toNat G C hG hPB hEpsilon missing p h hRows i i.isLt
        _ = ∑ u ∈ C.P, G.outdegree u :=
          (sum_finset_eq_sum_fin C.P p G.outdegree).symm
        _ = degreeSum := hDegreeSum
        _ = (BitVec.ofNat 8 degreeSum).toNat := by
          simp [Nat.mod_eq_of_lt hDegreeSmall]
    · intro i hi
      rw [pDegree_toNat G C hG hPB hEpsilon missing p h hRows i hi]
      exact (hDegreePointwise i hi).trans (by omega)
  change core missing degreeSum bits = true
  have hPT : (FourZUnionEight.totalPToH bits).toNat ≤ 14 := by
    rw [hPTotalNat]
    exact hPTotalUpper
  have hHT : 14 ≤ (FourZUnionEight.totalHToP bits).toNat := by
    rw [hHTotalNat]
    exact hHTotalLower
  have hRowsCore' : all 7 (fun i ↦
      decide ((8 : BitVec 8).toNat ≤
        (FourZUnionEight.pDegree missing bits i).toNat) &&
      decide ((FourZUnionEight.pDegree missing bits i).toNat ≤
        (14 : BitVec 8).toNat) &&
        FourZUnionEight.pNonSeymour missing bits i) = true := by
    simpa only [BitVec.ule_eq_decide] using hRowsCore
  simp only [core, Bool.and_eq_true, hSquare, hPHOriented, hDegreeEq,
    BitVec.ule_eq_decide, decide_eq_true_eq, true_and,
    and_true]
  refine ⟨?_, hOrder⟩
  refine ⟨?_, hRowsCore'⟩
  refine ⟨?_, hDefectEq⟩
  constructor
  · simpa using hPT
  · simpa using hHT

end SeymourEight.FourZUnionEightGraphBridge
