import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.GraphBridge
import SeymourEight.Shared.LocalDegree

set_option linter.style.header false

/-!
# The `H` rows of the exact-seven four-`Z` certificate

This module proves graph soundness of the represented strict second-neighbor
counts for the four vertices of `H = A1 ∪ X`.  The `P → Z` block is implicit
in the certificate, so its exact graph realization is an explicit hypothesis.
-/

namespace SeymourEight.FourZExactSevenHBridge

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactGlobalBridge
  FiveZExactHBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem secondAFromH_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 → V) (w : Fin 7 → V)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (source target : Nat) (hs : source < 4) (ht : target < 8)
    (hSecond : FourZExactSeven.secondAFromH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (a j).1) z w) source target = true) :
    (a ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (h ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (a j).1) z w
  simp only [FourZExactSeven.secondAFromH, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hReach⟩, hNotArcBool⟩
  have hSourceA : (a ⟨source + 1, by omega⟩).1 =
      (h ⟨source, hs⟩).1 := by
    simpa using hAH ⟨source, hs⟩
  have hNotArc : ¬G.Adj (h ⟨source, hs⟩).1 (a ⟨target, ht⟩).1 := by
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (a j).1) z w (source + 1) target (by omega) ht]
      at hNotArcBool
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
    simp only [FourZExactSeven.reachesAFromH, Bool.or_eq_true] at hReach
    rcases hReach with hViaA | hViaP
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 8 _).mp hViaA
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (a ⟨middle, hm⟩).1 := by
        rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w
          (source + 1) middle (by omega) hm] at hFirstBool
        simpa [hSourceA] using of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (a ⟨middle, hm⟩).1 (a ⟨target, ht⟩).1 := by
        rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(a ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨hTargetH, hAny⟩
      obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hAny
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hTargetRange : 1 ≤ target ∧ target ≤ 4 := by omega
      let hj : Fin 4 := ⟨target - 1, by omega⟩
      have hSecondH : G.Adj (p ⟨middle, hm⟩).1 (h hj).1 := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w middle (target - 1) hm (by omega)]
          at hSecondBool
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
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 → V) (w : Fin 7 → V)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (source target : Nat) (hs : source < 4) (ht : target < 7)
    (hSecond : FourZExactSeven.secondPFromH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (a j).1) z w) source target = true) :
    (p ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (h ⟨source, hs⟩).1 := by
  simp only [FourZExactSeven.secondPFromH, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (h ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (a j).1) z w source target hs ht] at hNotArcBool
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
    simp only [FourZExactSeven.reachesPFromH, Bool.or_eq_true] at hReach
    rcases hReach with hViaA | hViaP
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 8 _).mp hViaA
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hContinue⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (a ⟨middle, hm⟩).1 := by
        rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w
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
        let hj : Fin 4 := ⟨middle - 1, by omega⟩
        have hSecondH : G.Adj (h hj).1 (p ⟨target, ht⟩).1 := by
          rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
            (fun j ↦ (a j).1) z w (middle - 1) target (by omega) ht]
            at hSecondBool
          exact of_decide_eq_true hSecondBool
        have hMiddleEq : (a ⟨middle, hm⟩).1 = (h hj).1 := by
          have := hAH hj
          simpa [hj, show middle - 1 + 1 = middle by omega] using this
        exact ⟨(a ⟨middle, hm⟩).1, hFirst, hMiddleEq ▸ hSecondH⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmTarget, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (h ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) z w middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem reachesZFromH_true_mem (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (missing : Nat)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 → V)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (source target : Nat) (hs : source < 4) (ht : target < 4)
    (hReach : FourZExactSeven.reachesZFromH missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        a (fun j ↦ (z j).1) w) source target = true) :
    (z ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (h ⟨source, hs⟩).1 := by
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (h ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
    rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      a (fun j ↦ (z j).1) w source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond : G.Adj (p ⟨middle, hm⟩).1 (z ⟨target, ht⟩).1 :=
    (hPZ middle target hm ht).mpr hSecondBool
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

theorem hSecondCount_coreBits_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (w : Fin 7 → V)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (source : Nat) (hs : source < 4) :
    (FourZExactSeven.hSecondCount missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (a j).1) (fun j ↦ (z j).1) w) source).toNat ≤
      G.secondOutdegree (h ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (a j).1) (fun j ↦ (z j).1) w
  let u := (h ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  have hABound : (count 8 (FourZExactSeven.secondAFromH bits source)).toNat ≤
      (C.A.filter Q).card := by
    apply count_le_filterCard C.A a _ Q (by omega)
    intro j hBit
    exact secondAFromH_true_mem G C p h a (fun j ↦ (z j).1) w hAH
      source j hs j.isLt hBit
  have hPBound : (count 7 (FourZExactSeven.secondPFromH bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPFromH_true_mem G C p h a (fun j ↦ (z j).1) w hA0 hAH
      source j hs j.isLt hBit
  have hZBound : (count 4 (FourZExactSeven.reachesZFromH missing bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact reachesZFromH_true_mem G C hG hPB missing p h
      (fun j ↦ (a j).1) z w hPZ source j hs j.isLt hBit
  have hACard : (C.A.filter Q).card ≤ 8 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr a).symm)
  have hPCard : (C.P.filter Q).card ≤ 7 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  have hZCard : (C.Z.filter Q).card ≤ 4 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr z).symm)
  have hCountNat : (FourZExactSeven.hSecondCount missing bits source).toNat =
      (count 8 (FourZExactSeven.secondAFromH bits source)).toNat +
        (count 7 (FourZExactSeven.secondPFromH bits source)).toNat +
          (count 4 (FourZExactSeven.reachesZFromH missing bits source)).toNat := by
    rw [FourZExactSeven.hSecondCount, BitVec.toNat_add, BitVec.toNat_add,
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
    (count 8 (FourZExactSeven.secondAFromH bits source)).toNat +
        (count 7 (FourZExactSeven.secondPFromH bits source)).toNat +
      (count 4 (FourZExactSeven.reachesZFromH missing bits source)).toNat ≤
        SA.card + SP.card + SZ.card := by
      dsimp only [SA, SP, SZ]
      omega
    _ = (SA ∪ SP ∪ SZ).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card :=
      Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (h ⟨source, hs⟩).1 := rfl

theorem hRow_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (missing : Nat)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (w : Fin 7 → V)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 4) :
    ((8 : BitVec 8).ule
        (FourZExactSeven.hDegree (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) (fun j ↦ (z j).1) w) source) &&
      FourZExactSeven.hNonSeymour missing
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (a j).1) (fun j ↦ (z j).1) w) source) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (a j).1) (fun j ↦ (z j).1) w
  let u := (h ⟨source, hs⟩).1
  have hDegreeNat := hDegree_toNat G C hG hPB p h a
    (fun j ↦ (z j).1) w hAH source hs
  have hSecond := hSecondCount_coreBits_toNat_le_secondOutdegree
    G C hG hPB missing p h a z w hA0 hAH hPZ source hs
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [Bool.and_eq_true]
  constructor
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegreeNat]
    exact hMin u
  · simp only [FourZExactSeven.hNonSeymour, BitVec.ult_eq_decide,
      decide_eq_true_eq]
    rw [hDegreeNat]
    exact hSecond.trans_lt (by simpa [u] using hStrict)

theorem hRows_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (missing : Nat)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (w : Fin 7 → V)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 4 (FourZExactSeven.hNonSeymour missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (a j).1) (fun j ↦ (z j).1) w)) = true := by
  rw [all_eq_true_iff]
  intro source hs
  have hRow := hRow_coreBits_true G C hG hPB missing p h a z w
    hA0 hAH hPZ hMin hNoSeymour source hs
  simp only [Bool.and_eq_true] at hRow
  exact hRow.2

end SeymourEight.FourZExactSevenHBridge
