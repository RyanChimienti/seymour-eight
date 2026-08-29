import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactHBridge

set_option linter.style.header false

/-!
# The `P` rows of the exact five-`Z` certificate

The represented strict second neighbors of a `P` vertex are split into the
pairwise-disjoint classes `P`, `W`, `H \ W`, and missing direct members of
`Z`.  This module proves that the corresponding finite-core count is a sound
lower bound for the graph's strict second outdegree.
-/

namespace SeymourEight.FiveZExactPBridge

open FiveZExactRisk FiveZExactCoreBridge FiveZExactGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem no_P_to_s_of_epsilonS_zero (C : G.LocalConfiguration)
    (hEpsilon : epsilonS G C = 0) (p : V) (hp : p ∈ C.P) :
    ¬G.Adj p C.s := by
  intro hps
  rw [epsilonS_eq_ite] at hEpsilon
  simp [show ∃ q ∈ C.P, G.Adj q C.s from ⟨p, hp, hps⟩] at hEpsilon

theorem P_outdegree_eq_Z_add_H_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (p : V) (hp : p ∈ C.P) :
    G.outdegree p = directCount G C.Z p + directCount G C.H p +
      directCount G C.P p := by
  have hEq : G.outNeighborFinset p =
      (C.Z ∪ C.H ∪ C.P).filter fun v ↦ G.Adj p v := by
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro hpv
      have hvCaptured := outgoingCaptured_of_p_eq_B G C hG hPB p hp
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
      simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
      rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
      · exact ⟨Or.inl (Or.inl hvZ), hpv⟩
      · subst v
        exact (no_P_to_s_of_epsilonS_zero G C hEpsilon p hp hpv).elim
      · exact ⟨Or.inl (Or.inr hvH), hpv⟩
      · exact ⟨Or.inr hvP, hpv⟩
    · exact fun hv ↦ hv.2
  have hZH : Disjoint C.Z C.H :=
    Digraph.LocalConfiguration.disjoint_Z_H (G := G) C
  have hZHP : Disjoint (C.Z ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hvZH hvP
    rcases Finset.mem_union.mp hvZH with hvZ | hvH
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  have hZHFilter :
      Disjoint (C.Z.filter fun v ↦ G.Adj p v)
        (C.H.filter fun v ↦ G.Adj p v) :=
    Finset.disjoint_filter_filter (p := fun v ↦ G.Adj p v)
      (q := fun v ↦ G.Adj p v) hZH
  have hZHPFilter :
      Disjoint
        ((C.Z.filter fun v ↦ G.Adj p v) ∪
          (C.H.filter fun v ↦ G.Adj p v))
        (C.P.filter fun v ↦ G.Adj p v) := by
    rw [Finset.disjoint_left]
    intro v hvZH hvP
    apply (Finset.disjoint_left.mp hZHP) ?_ (Finset.mem_filter.mp hvP).1
    rcases Finset.mem_union.mp hvZH with hvZ | hvH
    · exact Finset.mem_union_left _ (Finset.mem_filter.mp hvZ).1
    · exact Finset.mem_union_right _ (Finset.mem_filter.mp hvH).1
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  rw [hEq, Finset.filter_union, Finset.filter_union,
    Finset.card_union_of_disjoint hZHPFilter,
    Finset.card_union_of_disjoint hZHFilter]

theorem pDegree_coreBits_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    (pDegree (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).toNat =
      G.outdegree (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  have hZ : (pZOut bits source).toNat =
      directCount G C.Z (p ⟨source, hs⟩).1 := by
    rw [pZOut, toNat_count_eq_fin_sum 5 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Z z
    intro j
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source j hs j.isLt]
    simp
  have hH : (pHOut bits source).toNat =
      directCount G C.H (p ⟨source, hs⟩).1 := by
    rw [pHOut, toNat_count_eq_fin_sum 3 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H h
    intro j
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source j hs j.isLt]
    simp
  have hP : (pOut bits source).toNat =
      directCount G C.P (p ⟨source, hs⟩).1 := by
    rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P p
    intro j
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source j hs j.isLt]
    simp
  have hZLe : directCount G C.Z (p ⟨source, hs⟩).1 ≤ 5 := by
    calc
      directCount G C.Z (p ⟨source, hs⟩).1 ≤ C.Z.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hHLe : directCount G C.H (p ⟨source, hs⟩).1 ≤ 3 := by
    calc
      directCount G C.H (p ⟨source, hs⟩).1 ≤ C.H.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := by simpa using (Fintype.card_congr h).symm
  have hPLe : directCount G C.P (p ⟨source, hs⟩).1 ≤ 7 := by
    calc
      directCount G C.P (p ⟨source, hs⟩).1 ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  rw [pDegree, BitVec.toNat_add, BitVec.toNat_add, hZ, hH, hP,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact (P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon
    (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2).symm

theorem secondPViaPOrH_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 7)
    (hSecond : secondPViaPOrH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (p ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondPViaPOrH, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hNotArcBool⟩, hReach⟩
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 7) = ⟨source, hs⟩ := by
      apply p.injective
      exact Subtype.ext hEq
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V,
      G.Adj (p ⟨source, hs⟩).1 middle ∧
        G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [reachedPViaPOrH, Bool.or_eq_true] at hReach
    rcases hReach with hViaP | hViaH
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (p ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 3 _).mp hViaH
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (p ⟨source, hs⟩).1 (h ⟨middle, hm⟩).1 := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (h ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(h ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondW_true_mem (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hW0 : (w 0).1 = (h 0).1)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (source target : Nat) (hs : source < 7) (ht : target < 6)
    (hSecond : secondW
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (w ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondW, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotDirectData⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (w ⟨target, ht⟩).1 := by
    rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (w ⟨target, ht⟩).1 := by
    by_cases ht0 : target = 0
    · subst target
      simp only [Bool.or_eq_true] at hNotDirectData
      rcases hNotDirectData with hImpossible | hNotDirectData
      · simp at hImpossible
      rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
        source 0 hs (by omega)] at hNotDirectData
      simpa [hW0] using hNotDirectData
    · intro hDirect
      have hvCaptured := outgoingCaptured_of_p_eq_B G C hG hPB
        (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hDirect)
      simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
      rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
      · exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
          hvZ (w ⟨target, ht⟩).2
      · have hDirectS : G.Adj (p ⟨source, hs⟩).1 C.s := by
          simpa [hvs] using hDirect
        exact no_P_to_s_of_epsilonS_zero G C hEpsilon
          (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2 hDirectS
      · let hj : Fin 3 := h.symm ⟨(w ⟨target, ht⟩).1, hvH⟩
        have hjW : (h hj).1 ∈ zExternalUnion G C := by
          have hjEq : (h hj).1 = (w ⟨target, ht⟩).1 := by
            simp [hj]
          rw [hjEq]
          exact (w ⟨target, ht⟩).2
        have hj0 : hj = 0 := (hInW hj).mp hjW
        have hVertexEq : (w ⟨target, ht⟩).1 = (w 0).1 := by
          calc
            (w ⟨target, ht⟩).1 = (h hj).1 := by simp [hj]
            _ = (h 0).1 := by rw [hj0]
            _ = (w 0).1 := hW0.symm
        have hIndexEq : (⟨target, ht⟩ : Fin 6) = 0 := by
          apply w.injective
          exact Subtype.ext hVertexEq
        exact ht0 (Fin.ext_iff.mp hIndexEq)
      · exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
          hvP (w ⟨target, ht⟩).2
  have hTargetVertexNe : (w ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
      (p ⟨source, hs⟩).2 (hEq ▸ (w ⟨target, ht⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem secondOutsideH_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 3)
    (hSecond : secondOutsideH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (h ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondOutsideH, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hReach⟩, hNotArcBool⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (h ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
      (h ⟨target, ht⟩).2 (hEq ▸ (p ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem secondMissingZ_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 5)
    (hSecond : secondMissingZ
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (z ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondMissingZ, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨_hmTarget, hFirstBool⟩, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (z ⟨target, ht⟩).1 := by
    rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (z ⟨target, ht⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (z ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
      (z ⟨target, ht⟩).2 (hEq ▸ (p ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem pSecondCount_coreBits_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hW0 : (w 0).1 = (h 0).1)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (source : Nat) (hs : source < 7) :
    (secondPCount
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source +
      secondWCount
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source +
      secondOutsideHCount
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source +
      secondMissingZCount
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).toNat ≤
      G.secondOutdegree (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (p ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  let QOutside : V → Prop := fun v ↦
    v ∉ zExternalUnion G C ∧ v ∈ G.secondOutNeighborFinset u
  have hPBound : (count 7 (secondPViaPOrH bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPViaPOrH_true_mem G C p z w h a
      source j hs j.isLt hBit
  have hWBound : (count 6 (secondW bits source)).toNat ≤
      ((zExternalUnion G C).filter Q).card := by
    apply count_le_filterCard (zExternalUnion G C) w _ Q (by omega)
    intro j hBit
    exact secondW_true_mem G C hG hPB hEpsilon p z w h a hW0 hInW
      source j hs j.isLt hBit
  have hHBound : (count 3 (secondOutsideH bits source)).toNat ≤
      (C.H.filter QOutside).card := by
    apply count_le_filterCard C.H h _ QOutside (by omega)
    intro j hBit
    have hMem := secondOutsideH_true_mem G C p z w h a
      source j hs j.isLt hBit
    have hNe : (j : Nat) ≠ 0 := by
      simp only [bits, secondOutsideH, Bool.and_eq_true,
        decide_eq_true_eq] at hBit
      exact hBit.1.1
    have hNotW : (h j).1 ∉ zExternalUnion G C := by
      intro hjW
      have hj0 : j = 0 := (hInW j).mp hjW
      exact hNe (Fin.ext_iff.mp hj0)
    exact ⟨hNotW, hMem⟩
  have hZBound : (count 5 (secondMissingZ bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact secondMissingZ_true_mem G C p z w h a
      source j hs j.isLt hBit
  have hPCard : (C.P.filter Q).card ≤ 7 := by
    calc
      (C.P.filter Q).card ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  have hWCard : ((zExternalUnion G C).filter Q).card ≤ 6 := by
    calc
      ((zExternalUnion G C).filter Q).card ≤ (zExternalUnion G C).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by simpa using (Fintype.card_congr w).symm
  have hHCard : (C.H.filter QOutside).card ≤ 3 := by
    calc
      (C.H.filter QOutside).card ≤ C.H.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := by simpa using (Fintype.card_congr h).symm
  have hZCard : (C.Z.filter Q).card ≤ 5 := by
    calc
      (C.Z.filter Q).card ≤ C.Z.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hCountNat :
      (secondPCount bits source + secondWCount bits source +
        secondOutsideHCount bits source +
          secondMissingZCount bits source).toNat =
      (count 7 (secondPViaPOrH bits source)).toNat +
        (count 6 (secondW bits source)).toNat +
          (count 3 (secondOutsideH bits source)).toNat +
            (count 5 (secondMissingZ bits source)).toNat := by
    rw [secondPCount, secondWCount, secondOutsideHCount,
      secondMissingZCount, BitVec.toNat_add, BitVec.toNat_add,
      BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  let SP := C.P.filter Q
  let SW := (zExternalUnion G C).filter Q
  let SH := C.H.filter QOutside
  let SZ := C.Z.filter Q
  have hP_W : Disjoint SP SW := by
    rw [Finset.disjoint_left]
    intro v hvP hvW
    exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
      (Finset.mem_filter.mp hvP).1 (Finset.mem_filter.mp hvW).1
  have hPW_H : Disjoint (SP ∪ SW) SH := by
    rw [Finset.disjoint_left]
    intro v hvPW hvH
    rcases Finset.mem_union.mp hvPW with hvP | hvW
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 (Finset.mem_filter.mp hvP).1
    · exact (Finset.mem_filter.mp hvH).2.1 (Finset.mem_filter.mp hvW).1
  have hPWH_Z : Disjoint (SP ∪ SW ∪ SH) SZ := by
    rw [Finset.disjoint_left]
    intro v hvPWH hvZ
    rcases Finset.mem_union.mp hvPWH with hvPW | hvH
    · rcases Finset.mem_union.mp hvPW with hvP | hvW
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
          (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
      · exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
          (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvW).1
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
        (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvH).1
  have hUnionSubset : SP ∪ SW ∪ SH ∪ SZ ⊆
      G.secondOutNeighborFinset u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvPWH | hvZ
    · rcases Finset.mem_union.mp hvPWH with hvPW | hvH
      · rcases Finset.mem_union.mp hvPW with hvP | hvW
        · exact (Finset.mem_filter.mp hvP).2
        · exact (Finset.mem_filter.mp hvW).2
      · exact (Finset.mem_filter.mp hvH).2.2
    · exact (Finset.mem_filter.mp hvZ).2
  have hUnionCard : (SP ∪ SW ∪ SH ∪ SZ).card =
      SP.card + SW.card + SH.card + SZ.card := by
    rw [Finset.card_union_of_disjoint hPWH_Z,
      Finset.card_union_of_disjoint hPW_H,
      Finset.card_union_of_disjoint hP_W]
  rw [hCountNat]
  calc
    (count 7 (secondPViaPOrH bits source)).toNat +
          (count 6 (secondW bits source)).toNat +
        (count 3 (secondOutsideH bits source)).toNat +
      (count 5 (secondMissingZ bits source)).toNat ≤
        SP.card + SW.card + SH.card + SZ.card := by
      dsimp only [SP, SW, SH, SZ]
      omega
    _ = (SP ∪ SW ∪ SH ∪ SZ).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card :=
      Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (p ⟨source, hs⟩).1 := rfl

theorem p_outdegree_le_fourteen (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (hZCard : C.Z.card = 5) (hHCard : C.H.card = 3)
    (hPCard : C.P.card = 7) (p : V) (hp : p ∈ C.P) :
    G.outdegree p ≤ 14 := by
  have hPInternal : directCount G C.P p ≤ 6 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    calc
      (C.P.filter (G.Adj p)).card ≤ (C.P.erase p).card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvP, hpv⟩
        exact Finset.mem_erase.mpr ⟨fun hvp ↦ hG.1 p (hvp ▸ hpv), hvP⟩
      _ = 6 := by rw [Finset.card_erase_of_mem hp, hPCard]
  have hZLe : directCount G C.Z p ≤ 5 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hHLe : directCount G C.H p ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon p hp]
  omega

theorem pRow_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hW0 : (w 0).1 = (h 0).1)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 7) :
    ((8 : BitVec 8).ule
        (pDegree
          (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
            (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source) &&
      (pDegree
          (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
            (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).ule 14 &&
      pNonSeymour
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (p ⟨source, hs⟩).1
  have hDegree := pDegree_coreBits_toNat G C hG hPB hEpsilon
    p z w h a source hs
  have hSecond := pSecondCount_coreBits_toNat_le_secondOutdegree
    G C hG hPB hEpsilon p z w h a hW0 hInW source hs
  have hZCard : C.Z.card = 5 := by
    simpa using (Fintype.card_congr z).symm
  have hHCard : C.H.card = 3 := by
    simpa using (Fintype.card_congr h).symm
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr p).symm
  have hUpper := p_outdegree_le_fourteen G C hG hPB hEpsilon
    hZCard hHCard hPCard u (p ⟨source, hs⟩).2
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hMin u
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hUpper
  · simp only [pNonSeymour, BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hSecond.trans_lt (by simpa [u] using hStrict)

end SeymourEight.FiveZExactPBridge
