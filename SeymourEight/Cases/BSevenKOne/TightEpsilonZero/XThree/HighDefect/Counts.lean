import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.HighDefect.Labels
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactPBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGlobalBridge

set_option linter.style.header false

namespace SeymourEight.FourZHighDefectGraphBridge

open FourZHighDefect FourZHighDefectBridge FiveZExactGraphBridge
  FiveZExactRisk Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem outdegree_eq_directCount_of_captured (S : Finset V) (u : V)
    (hcap : G.outNeighborFinset u ⊆ S) :
    G.outdegree u = directCount G S u := by
  classical
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  congr 1
  ext v
  simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter]
  exact ⟨fun huv ↦ ⟨hcap ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩,
    fun hv ↦ hv.2⟩

theorem A_outgoingCaptured_retained (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outNeighborFinset u ⊆ retainedVertexSet G C := by
  intro v hv
  have := A_outgoingCaptured G C hG u hu hv
  rcases Finset.mem_union.mp this with hvA | hvB
  · exact Finset.mem_union_left C.Z (Finset.mem_union_left C.P hvA)
  · exact Finset.mem_union_left C.Z
      (Finset.mem_union_right C.A (by simpa [hPB] using hvB))

theorem P_outgoingCaptured_retained (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (u : V) (hu : u ∈ C.P) :
    G.outNeighborFinset u ⊆ retainedVertexSet G C := by
  intro v hv
  have hAdj := (Digraph.mem_outNeighborFinset (G := G)).mp hv
  have hcap := outgoingCaptured_of_p_eq_B G C hG hPB u hu hv
  simp only [Finset.mem_union, Finset.mem_singleton] at hcap
  rcases hcap with ((hvZ | hvs) | hvH) | hvP
  · exact Finset.mem_union_right (C.A ∪ C.P) hvZ
  · subst v
    exact (FiveZExactPBridge.no_P_to_s_of_epsilonS_zero
      G C hEpsilon u hu hAdj).elim
  · exact Finset.mem_union_left C.Z (Finset.mem_union_left C.P
      (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH))
  · exact Finset.mem_union_left C.Z (Finset.mem_union_right C.A hvP)

theorem coreOutdegree_coreBits_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = h i)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i).1 (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i).1 (z j).1)
    (source : Nat) (hs : source < 15) :
    (coreOutdegree (coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)) source).toNat =
      G.outdegree (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) source) := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r
    (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  let e := retainedLabelEquiv G C a p z
  rw [coreOutdegree, FiveZExactGraphBridge.toNat_count_eq_fin_sum 19 _ (by omega)]
  have hCount : (∑ j : Fin 19, if coreArc bits source j then 1 else 0) =
      directCount G (retainedVertexSet G C)
        (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
          (fun i ↦ (z i).1) source) := by
    symm
    apply directCount_eq_sum_bool G (retainedVertexSet G C) e
    intro j
    rw [retainedLabelEquiv_val]
    rw [coreArc_coreBits G (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      hA0P hP0 hAH hAR hPR hAZ source j hs j.isLt]
    simp
  rw [hCount]
  apply (outdegree_eq_directCount_of_captured G _ _ ?_).symm
  by_cases hsA : source < 8
  · have hv : labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) source = (a ⟨source, hsA⟩).1 := by
      simp [labelledVertex, hsA]
    rw [hv]
    exact A_outgoingCaptured_retained G C hG hPB _ (a ⟨source, hsA⟩).2
  · have hsP : source - 8 < 7 := by omega
    have hv : labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) source = (p ⟨source - 8, hsP⟩).1 := by
      simp [labelledVertex, hsA, hs]
    rw [hv]
    exact P_outgoingCaptured_retained G C hG hPB hEpsilon _
      (p ⟨source - 8, hsP⟩).2

theorem pDegree_coreBits_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (r : Fin 3 → V) (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 → V) (source : Nat) (hs : source < 7) :
    (FourZHighDefect.pDegree (coreBits G.Adj (fun i ↦ (p i).1)
      (fun i ↦ (h i).1) r (fun i ↦ (z i).1) a) source).toNat =
      G.outdegree (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
    r (fun i ↦ (z i).1) a
  have hZ : (count 4 (pToZ bits source)).toNat =
      directCount G C.Z (p ⟨source, hs⟩).1 := by
    rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Z z
    intro j
    rw [pToZ_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      r (fun i ↦ (z i).1) a source j hs j.isLt]
    simp
  have hH : (count 4 (pToH bits source)).toNat =
      directCount G C.H (p ⟨source, hs⟩).1 := by
    rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H h
    intro j
    rw [pToH_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      r (fun i ↦ (z i).1) a source j hs j.isLt]
    simp
  have hP : (count 7 (pArc bits source)).toNat =
      directCount G C.P (p ⟨source, hs⟩).1 := by
    rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P p
    intro j
    rw [pArc_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      r (fun i ↦ (z i).1) a source j hs j.isLt]
    simp
  have hZLe : directCount G C.Z (p ⟨source, hs⟩).1 ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr z).symm)
  have hHLe : directCount G C.H (p ⟨source, hs⟩).1 ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr h).symm)
  have hPLe : directCount G C.P (p ⟨source, hs⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  rw [FourZHighDefect.pDegree, BitVec.toNat_add, BitVec.toNat_add,
    hZ, hH, hP, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact (FiveZExactPBridge.P_outdegree_eq_Z_add_H_add_P
    G C hG hPB hEpsilon (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2).symm

theorem pDegreeSum_coreBits_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (r : Fin 3 → V) (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 → V) :
    (FourZHighDefect.pDegreeSum (coreBits G.Adj (fun i ↦ (p i).1)
      (fun i ↦ (h i).1) r (fun i ↦ (z i).1) a)).toNat =
      ∑ u ∈ C.P, G.outdegree u := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
    r (fun i ↦ (z i).1) a
  rw [FourZHighDefect.pDegreeSum,
    FiveZExactGlobalBridge.toNat_sumCount_of_le 7 15 _ (by omega)]
  · rw [← Fin.sum_univ_eq_sum_range, sum_finset_eq_sum_fin C.P p G.outdegree]
    apply Finset.sum_congr rfl
    intro i hi
    exact pDegree_coreBits_toNat G C hG hPB hEpsilon p h r z a i i.isLt
  · intro i hi
    rw [pDegree_coreBits_toNat G C hG hPB hEpsilon p h r z a i hi]
    rw [FiveZExactPBridge.P_outdegree_eq_Z_add_H_add_P
      G C hG hPB hEpsilon _ (p ⟨i, hi⟩).2]
    have hZLe : directCount G C.Z (p ⟨i, hi⟩).1 ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr z).symm)
    have hHLe : directCount G C.H (p ⟨i, hi⟩).1 ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr h).symm)
    have hPLe : directCount G C.P (p ⟨i, hi⟩).1 ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr p).symm)
    omega

end SeymourEight.FourZHighDefectGraphBridge
