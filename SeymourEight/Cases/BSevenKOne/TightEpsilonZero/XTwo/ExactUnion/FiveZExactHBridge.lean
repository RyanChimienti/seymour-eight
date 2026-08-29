import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGraphBridge
import SeymourEight.Shared.LocalDegree

set_option linter.style.header false

/-!
# The `H` rows of the exact five-`Z` certificate

This module proves graph soundness of the retained first- and second-neighbor
counts for the three vertices of `H = A1 ∪ X`.  The certificate represents
their strict second neighbors in the pairwise-disjoint target classes
`A`, `P`, and `Z`.
-/

namespace SeymourEight.FiveZExactHBridge

open FiveZExactRisk FiveZExactCoreBridge FiveZExactGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem hDegree_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (source : Nat) (hs : source < 3) :
    (hDegree (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1)) source).toNat =
      directCount G C.A (h ⟨source, hs⟩).1 +
        directCount G C.P (h ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    z w (fun j ↦ (a j).1)
  have hA : (aOut bits (source + 1)).toNat =
      directCount G C.A (h ⟨source, hs⟩).1 := by
    rw [aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.A a
    intro j
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1)
      (source + 1) j (by omega) j.isLt]
    have hSource : (a ⟨source + 1, by omega⟩).1 =
        (h ⟨source, hs⟩).1 := by
      simpa using hAH ⟨source, hs⟩
    simp [hSource]
  have hP : (hPOut bits source).toNat =
      directCount G C.P (h ⟨source, hs⟩).1 := by
    rw [hPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P p
    intro j
    rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w (fun j ↦ (a j).1)
      source j hs j.isLt]
    simp
  have hACard : directCount G C.A (h ⟨source, hs⟩).1 ≤ 8 := by
    calc
      directCount G C.A (h ⟨source, hs⟩).1 ≤ C.A.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 := by simpa using (Fintype.card_congr a).symm
  have hPCard : directCount G C.P (h ⟨source, hs⟩).1 ≤ 7 := by
    calc
      directCount G C.P (h ⟨source, hs⟩).1 ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  rw [hDegree, BitVec.toNat_add, hA, hP, Nat.mod_eq_of_lt (by omega)]

theorem H_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.H) :
    G.outdegree u = directCount G C.A u + directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hEq : G.outNeighborFinset u =
      (C.A ∪ C.P).filter fun v ↦ G.Adj u v := by
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro huv
      have hvCaptured := H_outgoingCaptured G C hG hPB u hu
        ((Digraph.mem_outNeighborFinset (G := G)).mpr huv)
      exact ⟨by simpa only [Finset.mem_union] using hvCaptured, huv⟩
    · exact fun hv ↦ hv.2
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  rw [hEq, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (p := fun v ↦ G.Adj u v)
        (q := fun v ↦ G.Adj u v) hAP)]

theorem secondAFromH_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (source target : Nat) (hs : source < 3) (ht : target < 8)
    (hSecond : secondAFromH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w (fun j ↦ (a j).1))
      source target = true) :
    (a ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (h ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
  simp only [secondAFromH, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hReach⟩, hNotArcBool⟩
  have hSourceA : (a ⟨source + 1, by omega⟩).1 =
      (h ⟨source, hs⟩).1 := by
    simpa using hAH ⟨source, hs⟩
  have hNotArc : ¬G.Adj (h ⟨source, hs⟩).1 (a ⟨target, ht⟩).1 := by
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
      (source + 1) target (by omega) ht] at hNotArcBool
    simpa [hSourceA] using hNotArcBool
  have hTargetVertexNe : (a ⟨target, ht⟩).1 ≠
      (h ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 8) = ⟨source + 1, by omega⟩ := by
      apply a.injective
      exact Subtype.ext (hEq.trans hSourceA.symm)
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V,
      G.Adj (h ⟨source, hs⟩).1 middle ∧
        G.Adj middle (a ⟨target, ht⟩).1 := by
    simp only [reachesAFromH, Bool.or_eq_true] at hReach
    rcases hReach with hViaA | hViaP
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 8 _).mp hViaA
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (a ⟨middle, hm⟩).1 := by
        rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          (source + 1) middle (by omega) hm] at hFirstBool
        simpa [hSourceA] using of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (a ⟨middle, hm⟩).1 (a ⟨target, ht⟩).1 := by
        rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(a ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨hTargetH, hAny⟩
      obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 7 _).mp hAny
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hTargetRange : 1 ≤ target ∧ target ≤ 3 := by omega
      let hj : Fin 3 := ⟨target - 1, by omega⟩
      have hSecondH : G.Adj (p ⟨middle, hm⟩).1 (h hj).1 := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          middle (target - 1) hm (by omega)] at hSecondBool
        exact of_decide_eq_true hSecondBool
      have hTargetEq : (a ⟨target, ht⟩).1 = (h hj).1 := by
        have := hAH hj
        simpa [hj, show target - 1 + 1 = target by omega] using this
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hTargetEq ▸ hSecondH⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondPFromH_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (source target : Nat) (hs : source < 3) (ht : target < 7)
    (hSecond : secondPFromH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w (fun j ↦ (a j).1))
      source target = true) :
    (p ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (h ⟨source, hs⟩).1 := by
  simp only [secondPFromH, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (h ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠
      (h ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
      (h ⟨source, hs⟩).2 (hEq ▸ (p ⟨target, ht⟩).2)
  have hSourceA : (a ⟨source + 1, by omega⟩).1 =
      (h ⟨source, hs⟩).1 := by
    simpa using hAH ⟨source, hs⟩
  have hTwoStep : ∃ middle : V,
      G.Adj (h ⟨source, hs⟩).1 middle ∧
        G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [reachesPFromH, Bool.or_eq_true] at hReach
    rcases hReach with hViaA | hViaP
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 8 _).mp hViaA
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hContinue⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (a ⟨middle, hm⟩).1 := by
        rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          (source + 1) middle (by omega) hm] at hFirstBool
        simpa [hSourceA] using of_decide_eq_true hFirstBool
      simp only [Bool.or_eq_true] at hContinue
      rcases hContinue with hMiddlePivot | hMiddleH
      · have hm0 : middle = 0 := of_decide_eq_true hMiddlePivot
        have hSecond' : G.Adj (a ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
          subst middle
          have ha1p : G.Adj C.a1 (p ⟨target, ht⟩).1 :=
            (Finset.mem_filter.mp (p ⟨target, ht⟩).2).2
          simpa [hA0] using ha1p
        exact ⟨(a ⟨middle, hm⟩).1, hFirst, hSecond'⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hMiddleH
        rcases hMiddleH with ⟨hRange, hSecondBool⟩
        let hj : Fin 3 := ⟨middle - 1, by omega⟩
        have hSecondH : G.Adj (h hj).1 (p ⟨target, ht⟩).1 := by
          rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
            (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
            (middle - 1) target (by omega) ht] at hSecondBool
          exact of_decide_eq_true hSecondBool
        have hMiddleEq : (a ⟨middle, hm⟩).1 = (h hj).1 := by
          have := hAH hj
          simpa [hj, show middle - 1 + 1 = middle by omega] using this
        exact ⟨(a ⟨middle, hm⟩).1, hFirst, hMiddleEq ▸ hSecondH⟩
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmTarget, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem reachesZFromH_true_mem (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (source target : Nat) (hs : source < 3) (ht : target < 5)
    (hReach : reachesZFromH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w (fun j ↦ (a j).1))
      source target = true) :
    (z ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (h ⟨source, hs⟩).1 := by
  obtain ⟨middle, hm, hPath⟩ :=
    (any_eq_true_iff 7 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (h ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
    rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
      source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond : G.Adj (p ⟨middle, hm⟩).1 (z ⟨target, ht⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
      middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (h ⟨source, hs⟩).1 (z ⟨target, ht⟩).1 := by
    intro hDirect
    have hCaptured := H_outgoingCaptured G C hG hPB
      (h ⟨source, hs⟩).1 (h ⟨source, hs⟩).2
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hDirect)
    rcases Finset.mem_union.mp hCaptured with hzA | hzP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C))
        (z ⟨target, ht⟩).2
        (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hzA))
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
        (z ⟨target, ht⟩).2 hzP
  have hTargetVertexNe : (z ⟨target, ht⟩).1 ≠
      (h ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
      (z ⟨target, ht⟩).2 (hEq ▸ (h ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨middle, hm⟩).1, hFirst, hSecond⟩,
    hNotArc, hTargetVertexNe⟩

/-- The full represented `A + P + Z` second-neighbor count for an `H` row
is bounded by its actual strict second outdegree. -/
theorem hSecondCount_coreBits_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (source : Nat) (hs : source < 3) :
    (hSecondCount
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w (fun j ↦ (a j).1)) source).toNat ≤
      G.secondOutdegree (h ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
  let u := (h ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  have hABound : (count 8 (secondAFromH bits source)).toNat ≤
      (C.A.filter Q).card := by
    apply count_le_filterCard C.A a _ Q (by omega)
    intro j hBit
    exact secondAFromH_true_mem G C p z w h a hAH
      source j hs j.isLt hBit
  have hPBound : (count 7 (secondPFromH bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPFromH_true_mem G C p z w h a hA0 hAH
      source j hs j.isLt hBit
  have hZBound : (count 5 (reachesZFromH bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact reachesZFromH_true_mem G C hG hPB p z w h a
      source j hs j.isLt hBit
  have hACard : (C.A.filter Q).card ≤ 8 := by
    calc
      (C.A.filter Q).card ≤ C.A.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 := by simpa using (Fintype.card_congr a).symm
  have hPCard : (C.P.filter Q).card ≤ 7 := by
    calc
      (C.P.filter Q).card ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  have hZCard : (C.Z.filter Q).card ≤ 5 := by
    calc
      (C.Z.filter Q).card ≤ C.Z.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hCountNat : (hSecondCount bits source).toNat =
      (count 8 (secondAFromH bits source)).toNat +
        (count 7 (secondPFromH bits source)).toNat +
          (count 5 (reachesZFromH bits source)).toNat := by
    rw [hSecondCount, BitVec.toNat_add, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  let SA := C.A.filter Q
  let SP := C.P.filter Q
  let SZ := C.Z.filter Q
  have hA_P : Disjoint SA SP := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
      (Finset.mem_filter.mp hvA).1
      (Digraph.LocalConfiguration.P_subset_B (G := G) C
        (Finset.mem_filter.mp hvP).1)
  have hAP_Z : Disjoint (SA ∪ SP) SZ := by
    rw [Finset.disjoint_left]
    intro v hvAP hvZ
    rcases Finset.mem_union.mp hvAP with hvA | hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C))
        (Finset.mem_filter.mp hvZ).1
        (Finset.mem_union_left C.B
          (Finset.mem_union_right {C.s} (Finset.mem_filter.mp hvA).1))
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
        (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
  have hUnionSubset : SA ∪ SP ∪ SZ ⊆ G.secondOutNeighborFinset u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvAP | hvZ
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · exact (Finset.mem_filter.mp hvA).2
      · exact (Finset.mem_filter.mp hvP).2
    · exact (Finset.mem_filter.mp hvZ).2
  have hUnionCard : (SA ∪ SP ∪ SZ).card = SA.card + SP.card + SZ.card := by
    rw [Finset.card_union_of_disjoint hAP_Z,
      Finset.card_union_of_disjoint hA_P]
  rw [hCountNat]
  calc
    (count 8 (secondAFromH bits source)).toNat +
        (count 7 (secondPFromH bits source)).toNat +
      (count 5 (reachesZFromH bits source)).toNat ≤
        SA.card + SP.card + SZ.card := by
      dsimp only [SA, SP, SZ]
      omega
    _ = (SA ∪ SP ∪ SZ).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card :=
      Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (h ⟨source, hs⟩).1 := rfl

theorem hRow_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 3, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 3) :
    ((8 : BitVec 8).ule
        (hDegree
          (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
            (fun j ↦ (z j).1) w (fun j ↦ (a j).1)) source) &&
      hNonSeymour
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) w (fun j ↦ (a j).1)) source) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w (fun j ↦ (a j).1)
  let u := (h ⟨source, hs⟩).1
  have hDegreeRetained := hDegree_coreBits_toNat G C p
    (fun j ↦ (z j).1) w h a hAH source hs
  have hDegreeActual := H_outdegree_eq_A_add_P G C hG hPB u
    (h ⟨source, hs⟩).2
  have hDegree : (hDegree bits source).toNat = G.outdegree u := by
    rw [hDegreeRetained, hDegreeActual]
  have hSecond := hSecondCount_coreBits_toNat_le_secondOutdegree
    G C hG hPB p z w h a hA0 hAH source hs
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [Bool.and_eq_true]
  constructor
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hMin u
  · simp only [hNonSeymour, BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hSecond.trans_lt (by simpa [u] using hStrict)

end SeymourEight.FiveZExactHBridge
