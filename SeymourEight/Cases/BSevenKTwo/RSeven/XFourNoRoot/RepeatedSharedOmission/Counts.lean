import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.GraphFacts

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] in
theorem edgeCount_source_union (S T U : Finset V) (hST : Disjoint S T) :
    edgeCount G (S ∪ T) U = edgeCount G S U + edgeCount G T U := by
  classical
  unfold edgeCount
  rw [Finset.sum_union hST]

omit [Fintype V] [DecidableEq V] in
theorem complete_of_internal_edgeCount_max (S : Finset V)
    (hG : G.IsOriented) (hEdges : edgeCount G S S = S.card.choose 2)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    G.Adj u v ∨ G.Adj v u := by
  classical
  have hMissing := card_internalMissingPairs_add_edgeCount G S hG
  have hZero : (internalMissingPairs G S).card = 0 := by omega
  by_contra hNo
  have hPair : ({u, v} : Finset V) ∈ internalMissingPairs G S := by
    unfold internalMissingPairs
    apply Finset.mem_filter.mpr
    constructor
    · rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · simp [huv]
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact fun huv' => hNo (Or.inl huv')
      · exact fun hvu => hNo (Or.inr hvu)
      · exact (hxy rfl).elim
  have : 0 < (internalMissingPairs G S).card := Finset.card_pos.mpr ⟨_, hPair⟩
  omega

structure TightCounts (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) : Prop where
  p_eq_B : C.P = C.B
  p_to_z : edgeCount G C.P C.Z = 22
  p_to_h : edgeCount G C.P C.H = 13
  p_internal : edgeCount G C.P C.P = 21
  p_degree : ∀ i : Fin 7, G.outdegree (L.p i).1 = 8
  p_complete : ∀ i j : Fin 7, i ≠ j →
    G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1
  ph_complete : ∀ i : Fin 7, ∀ j : Fin 6,
    G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
    G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1
  h_complete : ∀ i j : Fin 6, i ≠ j →
    G.Adj (L.a ⟨i + 1, by omega⟩).1 (L.a ⟨j + 1, by omega⟩).1 ∨
    G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.a ⟨i + 1, by omega⟩).1

theorem derive_tight_counts (C : G.LocalConfiguration)
    (L : Profile21111Labels G C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hr : C.r = 7)
    (hRootTail : edgeCount G C.P {C.s} = 0)
    (hHP : edgeCount G C.H C.P = 29)
    (hHCard : C.H.card = 6) (hHH : edgeCount G C.H C.H = 15) :
    TightCounts G C L := by
  have hPB := p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZ : edgeCount G C.P C.Z = 22 := by
    rw [edgeCount_eq_sum_fin G C.P C.Z L.p]
    simp_rw [L.p_z_count]
    norm_num [profileDirectCount, Fin.sum_univ_succ]
  have hPPLe : edgeCount G C.P C.P ≤ 21 := by
    have := internal_edgeCount_le_choose_two G C.P hG
    norm_num [hPCard, Nat.choose] at this ⊢
    exact this
  have hPHLe : edgeCount G C.P C.H ≤ 13 := by
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard, hHP] at hCross
    omega
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hRootSum : (∑ p ∈ C.P, epsilonAt G p C.s) = 0 := by
    rw [← edgeCount_singleton G C.P C.s]
    exact hRootTail
  rw [hZ, hRootSum] at hAccounting
  have hPH : edgeCount G C.P C.H = 13 := by omega
  have hPP : edgeCount G C.P C.P = 21 := by omega
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 56 := by omega
  have hPDegree : ∀ i : Fin 7, G.outdegree (L.p i).1 = 8 := by
    have hPoint := pointwise_eq_of_sum_eq_card_mul C.P G.outdegree 8
      (fun v hv => hMin v) (by simpa [hPCard] using hDegreeSum)
    intro i
    exact hPoint (L.p i).1 (L.p i).2
  have hPHCross : edgeCount G C.P C.H + edgeCount G C.H C.P = 42 := by
    omega
  have hDisjoint : Disjoint C.P C.H :=
    (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
  let K := C.P ∪ C.H
  have hKCard : K.card = 13 := by
    simp [K, Finset.card_union_of_disjoint hDisjoint, hPCard, hHCard]
  have hKEdges : edgeCount G K K = 78 := by
    rw [edgeCount_source_union G C.P C.H K hDisjoint,
      show K = C.P ∪ C.H from rfl,
      edgeCount_union_of_disjoint G C.P C.P C.H hDisjoint,
      edgeCount_union_of_disjoint G C.H C.P C.H hDisjoint]
    omega
  have hKMax : edgeCount G K K = K.card.choose 2 := by
    rw [hKEdges, hKCard]
    norm_num [Nat.choose]
  have hCompleteK {u v : V} (hu : u ∈ K) (hv : v ∈ K) (hne : u ≠ v) :=
    complete_of_internal_edgeCount_max G K hG hKMax hu hv hne
  have hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1 := by
    intro i j hij
    apply hCompleteK
    · exact Finset.mem_union_left C.H (L.p i).2
    · exact Finset.mem_union_left C.H (L.p j).2
    · intro h
      apply hij
      exact L.p.injective (Subtype.ext h)
  have hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1 := by
    intro i j
    have hjH : (L.a ⟨j + 1, by omega⟩).1 ∈ C.H := by
      by_cases hj2 : j.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨j, hj2⟩)
      · apply Finset.mem_union_right C.A1
        simpa [show j.val - 2 + 3 = j.val + 1 by omega] using
          L.a_x ⟨j - 2, by omega⟩
    apply hCompleteK
    · exact Finset.mem_union_left C.H (L.p i).2
    · exact Finset.mem_union_right C.P hjH
    · intro heq
      exact (Finset.disjoint_left.mp hDisjoint) (L.p i).2 (heq ▸ hjH)
  have hHComplete : ∀ i j : Fin 6, i ≠ j →
      G.Adj (L.a ⟨i + 1, by omega⟩).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.a ⟨i + 1, by omega⟩).1 := by
    intro i j hij
    have hiH : (L.a ⟨i + 1, by omega⟩).1 ∈ C.H := by
      by_cases hi2 : i.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi2⟩)
      · apply Finset.mem_union_right C.A1
        simpa [show i.val - 2 + 3 = i.val + 1 by omega] using
          L.a_x ⟨i - 2, by omega⟩
    have hjH : (L.a ⟨j + 1, by omega⟩).1 ∈ C.H := by
      by_cases hj2 : j.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨j, hj2⟩)
      · apply Finset.mem_union_right C.A1
        simpa [show j.val - 2 + 3 = j.val + 1 by omega] using
          L.a_x ⟨j - 2, by omega⟩
    apply hCompleteK
    · exact Finset.mem_union_right C.P hiH
    · exact Finset.mem_union_right C.P hjH
    · intro heq
      apply hij
      have hidx : (⟨i.val + 1, by omega⟩ : Fin 8) =
          ⟨j.val + 1, by omega⟩ := L.a.injective (Subtype.ext heq)
      have hval : i.val + 1 = j.val + 1 := congrArg Fin.val hidx
      exact Fin.ext (by omega)
  exact ⟨hPB, hZ, hPH, hPP, hPDegree, hPComplete, hPHComplete, hHComplete⟩

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
