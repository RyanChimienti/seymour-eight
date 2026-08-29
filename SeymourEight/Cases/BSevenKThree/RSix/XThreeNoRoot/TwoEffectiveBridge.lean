import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.EffectiveBridge

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.TwoEffectiveBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKThree.RSix.XThreeNoRoot.EffectiveBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem auxiliary_saturated (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8) (hHCard : C.H.card = 6)
    (hk : C.k = 3) (hr : C.r = 6) (hx : C.x = 3)
    (hy : BSevenKThree.y G C = 1) :
    edgeCount G C.P (auxiliarySet G C) = 18 := by
  have hQCard : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hRCard : C.R.card = 1 := by
    rw [BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk, hx]
  have hHCap := BSixKThree.H_degree_capacity_general G C hG hMin hk
  have hPCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hySix : BSixKThree.y G C = 1 := by
    simpa [BSixKThree.y, BSixKThree.Y, BSevenKThree.y,
      BSevenKThree.reachedQ] using hy
  rw [hHCard, hx, hRCard, hQCard, hySix] at hHCap
  rw [hHCard] at hPCap
  simp [Nat.choose] at hHCap
  have hLower : 18 ≤ edgeCount G C.P (auxiliarySet G C) := by
    have hE : edgeCount G C.P (auxiliarySet G C) =
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
      rw [edgeCount_union_of_disjoint]
      apply Finset.disjoint_of_subset_left
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      exact BSixKThree.disjoint_B_externalTargets G C
    rw [hE]
    omega
  have hUpper := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hPCard, auxiliarySet_card G C L] at hUpper
  omega

theorem row_saturated (C : G.LocalConfiguration) (L : Labels G 2 C)
    (_hG : G.IsOriented) (hTotal : edgeCount G C.P (auxiliarySet G C) = 18)
    (p : Nat) (hp : p < 6) :
    directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1 = 3 := by
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hCard : (auxiliarySet G C).card = 3 := auxiliarySet_card G C L
  have hOther : ∑ q ∈ C.P.erase v, directCount G (auxiliarySet G C) q ≤ 15 := by
    calc
      _ ≤ ∑ _q ∈ C.P.erase v, 3 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hCard
      _ = 15 := by
        have hPCard : C.P.card = 6 := by
          simpa using (Fintype.card_congr L.p).symm
        simp [Finset.card_erase_of_mem hvP, hPCard]
  have hSplit := Finset.sum_erase_add C.P
    (directCount G (auxiliarySet G C)) hvP
  have hRowLe : directCount G (auxiliarySet G C) v ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hCard
  unfold edgeCount at hTotal
  rw [← hSplit] at hTotal
  change directCount G (auxiliarySet G C) v = 3
  omega

theorem extra_z_false (C : G.LocalConfiguration) (L : Labels G 2 C)
    (p j : Nat) (hp : p < 6) (hj : j = 2 ∨ j = 3) :
    encodedArc (graphBits G L) (8 + p) (15 + j) = false := by
  rcases hj with rfl | rfl <;> interval_cases p <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLT, Nat.reduceEqDiff, if_true, if_false] <;>
    rw [Encoding.getLsbD_graphBits] <;>
    simp [Encoding.coreBitAt]

theorem genericEffective_eq_four (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hTotal : edgeCount G C.P (auxiliarySet G C) = 18)
    (p : Nat) (hp : p < 6) :
    genericEffective 2 (encodedArc (graphBits G L)) p = 4 := by
  let arc := encodedArc (graphBits G L)
  have hP4 : ∀ q < 6, pAuxOut 4 arc q = 3 := by
    intro q hq
    have hP2Nat := pAuxOut_toNat G C L hG (by omega) q hq
    rw [row_saturated G C L hG hTotal q hq] at hP2Nat
    have hP2 : pAuxOut 2 arc q = 3 := BitVec.eq_of_toNat_eq hP2Nat
    have h2 := extra_z_false G C L q 2 hq (Or.inl rfl)
    have h3 := extra_z_false G C L q 3 hq (Or.inr rfl)
    simpa [pAuxOut, count, bitCount, arc, h2, h3] using hP2
  have hTotal4 : (totalPAux 4 arc).toNat = 18 := by
    rw [totalPAux, toNat_sumCount]
    have hs : (∑ i ∈ Finset.range 6, (pAuxOut 4 arc i).toNat) = 18 := by
      calc
        _ = ∑ _i ∈ Finset.range 6, ((3 : BitVec 8).toNat) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hP4 i (Finset.mem_range.mp hi)]
        _ = 18 := by decide
    rw [hs]
  have hMissing : externalMissing 4 arc = 12 := by
    apply BitVec.eq_of_toNat_eq
    rw [externalMissing, BitVec.toNat_sub, hTotal4]
    decide
  rw [genericEffective, if_neg (by decide), genericEffectiveFive]
  rw [hMissing, hP4 p hp]
  decide

theorem genericEffective_graph (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hTotal : edgeCount G C.P (auxiliarySet G C) = 18)
    (p : Nat) (hp : p < 6) :
    (genericEffective 2 (encodedArc (graphBits G L)) p).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C)
        (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = 3 := by simpa [E] using auxiliarySet_card G C L
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hS : S.card = 3 := by
    exact row_saturated G C L hG hTotal p hp
  have hLower :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffective_capacity_lower
      G C hMin E (auxiliarySet_disjoint_P G C) v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP :=
    SeymourEight.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge.directAux_to_P_capacity
      G C hG E hPCard 3 hECard v hvP
  change S.card * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ S.card.choose 2 at hInternal
  change edgeCount G S C.P ≤ (18 - edgeCount G C.P E) - (3 - S.card) at hToP
  have hTotalE : edgeCount G C.P E = 18 := hTotal
  rw [hTotalE, hS] at hToP
  rw [hS] at hLower hInternal
  simp [Nat.choose] at hInternal
  change (genericEffective 2 (encodedArc (graphBits G L)) p).toNat ≤ U.card
  rw [genericEffective_eq_four G C L hG hTotal p hp]
  dsimp [S, U] at hS hLower hInternal hToP ⊢
  omega

theorem pGenericEffective_true (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 6)
    (hy : BSevenKThree.y G C = 1)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3) :
    pGenericEffective 2 (encodedArc (graphBits G L)) = true := by
  have hTotal := auxiliary_saturated G C L hG hMin hRootDegree hHCard
    hk hr hx hy
  rw [pGenericEffective, all_eq_true_iff]
  intro p hp
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hP := pOut_toNat G C L hG (by omega) p hp
  have hH := pHOut_toNat G C L hG (by omega) hHCard p hp
  have hAux := pAuxOut_toNat G C L hG (by omega) p hp
  have hTable := genericEffective_graph G C L hG hMin hTotal p hp
  have hPS := pSecondP_le_graph G C L hG (by omega) p hp
  have hEeq := auxiliarySet_eq_reached G C L hy
  have hUnion :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG E hEeq v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩)
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro w hw
    obtain ⟨i, hi⟩ := L.q.surjective ⟨w, hw⟩
    simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
  have hDegree :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG v hvP
  rw [← hQ] at hDegree
  have hNatural :
      (pSecondP (encodedArc (graphBits G L)) p).toNat +
          (genericEffective 2 (encodedArc (graphBits G L)) p).toNat + 1 ≤
        (pOut (encodedArc (graphBits G L)) p).toNat +
          2 * (pHOut (encodedArc (graphBits G L)) p).toNat +
            (pAuxOut 2 (encodedArc (graphBits G L)) p).toNat := by
    have hUnion' := hUnion
    change (C.P.filter fun w ↦
        w ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card +
          (directAuxEffectiveUnion G C (auxiliarySet G C)
            (L.p ⟨p, hp⟩).1).card ≤
        G.secondOutdegree (L.p ⟨p, hp⟩).1 +
          directCount G C.H (L.p ⟨p, hp⟩).1 at hUnion'
    dsimp [v, E] at hPS hTable hNS hAux hDegree
    rw [hP, hH, hAux]
    omega
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  have hPSLe : (pSecondP (encodedArc (graphBits G L)) p).toNat ≤ 6 :=
    hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hTableLe := genericEffective_toNat_le 2 (encodedArc (graphBits G L)) p
  have hPLe : (pOut (encodedArc (graphBits G L)) p).toNat ≤ 6 := by
    rw [hP]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut (encodedArc (graphBits G L)) p).toNat ≤ 6 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hAuxLe : (pAuxOut 2 (encodedArc (graphBits G L)) p).toNat ≤ 3 := by
    rw [hAux]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (auxiliarySet_card G C L)
  have hOne : (1 : BitVec 8).toNat = 1 := by decide
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  rw [hOne, hTwo]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.TwoEffectiveBridge
