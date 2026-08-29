import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.OrderingBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pAOneOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hA1Card : C.A1.card = 3) (p : Nat) (hp : p < 5) :
    (count 3 fun a ↦ encodedArc (graphBits G L) (8+p) (1+a)).toNat =
      directCount G C.A1 (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A1 (aOneLabelEquiv G C L hA1Card) _
  intro i
  rw [aOneLabelEquiv_val]
  rw [show 1 + i.val = i.val + 1 by omega,
    pToA_graphBits G C L hG hzLe p (i+1) hp (by omega)]
  simp

theorem pXOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hXCard : C.X.card = 3) (p : Nat) (hp : p < 5) :
    (count 3 fun x ↦ encodedArc (graphBits G L) (8+p) (4+x)).toNat =
      directCount G C.X (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.X (xLabelEquiv G C L hXCard) _
  intro i
  rw [xLabelEquiv_val]
  rw [show 4 + i.val = i.val + 4 by omega,
    pToA_graphBits G C L hG hzLe p (i+4) hp (by omega)]
  simp

theorem pQOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (p : Nat) (hp : p < 5) :
    (count 2 fun q ↦ encodedArc (graphBits G L) (8+p) (13+q)).toNat =
      directCount G C.Q (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 2 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.Q L.q _
  intro i
  rw [pToQ_graphBits G C L hG hzLe p i hp i.isLt]
  simp

theorem zIn_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (z : Nat) (hz : z < zCount) :
    (count 5 fun p ↦ encodedArc (graphBits G L) (8+p) (15+z)).toNat =
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.zInvariantKey G C (L.z ⟨z, hz⟩).1 := by
  rw [toNat_count_eq_fin_sum 5 _ (by omega)]
  unfold SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.zInvariantKey
  rw [edgeCount_eq_sum_fin G C.P {(L.z ⟨z, hz⟩).1} L.p]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pToZ_graphBits G C L hG hzLe p z p.isLt hz]
  by_cases hAdj : G.Adj (L.p p).1 (L.z ⟨z, hz⟩).1 <;>
    simp [directCount, CertificateBridge.internalFirstNeighbors,
      Finset.filter_singleton, hAdj]

theorem qIn_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (q : Nat) (hq : q < 2) :
    (qIn (encodedArc (graphBits G L)) q).toNat =
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.qInvariantKey G C (L.q ⟨q, hq⟩).1 := by
  rw [qIn, BitVec.toNat_add]
  have hA : (count 8 fun a ↦ encodedArc (graphBits G L) a (13+q)).toNat =
      edgeCount G C.A {(L.q ⟨q, hq⟩).1} := by
    rw [toNat_count_eq_fin_sum 8 _ (by omega),
      edgeCount_eq_sum_fin G C.A {(L.q ⟨q, hq⟩).1} L.a]
    apply Finset.sum_congr rfl
    intro a ha
    rw [aToQ_graphBits G C L hG hzLe a q a.isLt hq]
    by_cases hAdj : G.Adj (L.a a).1 (L.q ⟨q, hq⟩).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  have hP : (count 5 fun p ↦ encodedArc (graphBits G L) (8+p) (13+q)).toNat =
      edgeCount G C.P {(L.q ⟨q, hq⟩).1} := by
    rw [toNat_count_eq_fin_sum 5 _ (by omega),
      edgeCount_eq_sum_fin G C.P {(L.q ⟨q, hq⟩).1} L.p]
    apply Finset.sum_congr rfl
    intro p hp
    rw [pToQ_graphBits G C L hG hzLe p q p.isLt hq]
    by_cases hAdj : G.Adj (L.p p).1 (L.q ⟨q, hq⟩).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  have hDis : Disjoint C.A C.P := Finset.disjoint_of_subset_right
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
    (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)
  unfold SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.qInvariantKey
  rw [hA, hP, Nat.mod_eq_of_lt (by
    have ha := edgeCount_le_card_mul_card G C.A {(L.q ⟨q, hq⟩).1}
    have hp := edgeCount_le_card_mul_card G C.P {(L.q ⟨q, hq⟩).1}
    have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
    simp only [Finset.card_singleton] at ha hp
    omega)]
  unfold edgeCount
  rw [Finset.sum_union hDis]

theorem pDegree_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6) (p : Nat) (hp : p < 5) :
    (pDegree zCount (encodedArc (graphBits G L)) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hP := pOut_toNat G C L hG hzLe p hp
  have hH := pHOut_toNat G C L hG hzLe hHCard p hp
  have hAux := pAuxOut_toNat G C L hG hzLe p hp
  rw [pDegree, BitVec.toNat_add, BitVec.toNat_add, hP, hH, hAux]
  have hPLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.P)
  have hHLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.H)
  have hAuxLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) (C.Q ∪ externalTargets G C))
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hQZ : Disjoint C.Q (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvE
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvE
  change directCount G C.P _ ≤ C.P.card at hPLe
  change directCount G C.H _ ≤ C.H.card at hHLe
  change directCount G (C.Q ∪ externalTargets G C) _ ≤
    (C.Q ∪ externalTargets G C).card at hAuxLe
  rw [Finset.card_union_of_disjoint hQZ, hQCard, hZCard] at hAuxLe
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    directCount_union_of_disjoint G C.Q (externalTargets G C) _ hQZ,
    P_outdegree_eq_blocks G C L hG p hp]
  omega

theorem pKey_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6) (hA1Card : C.A1.card = 3)
    (hXCard : C.X.card = 3) (p : Nat) (hp : p < 5) :
    (pKey zCount (encodedArc (graphBits G L)) p).toNat =
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.pInvariantKey G C (L.p ⟨p, hp⟩).1 := by
  have hDegree := pDegree_toNat G C L hG hzLe hHCard p hp
  have hZ := pZOut_toNat G C L hG hzLe p hp
  have hQ := pQOut_toNat G C L hG hzLe p hp
  have hA1 := pAOneOut_toNat G C L hG hzLe hA1Card p hp
  have hX := pXOut_toNat G C L hG hzLe hXCard p hp
  have hP := pOut_toNat G C L hG hzLe p hp
  have hDegreeLe : G.outdegree (L.p ⟨p, hp⟩).1 ≤ 16 := by
    rw [P_outdegree_eq_blocks G C L hG p hp]
    have h1 := Finset.card_le_card (Finset.filter_subset
      (G.Adj (L.p ⟨p, hp⟩).1) C.P)
    have h2 := Finset.card_le_card (Finset.filter_subset
      (G.Adj (L.p ⟨p, hp⟩).1) C.H)
    have h3 := Finset.card_le_card (Finset.filter_subset
      (G.Adj (L.p ⟨p, hp⟩).1) C.Q)
    have h4 := Finset.card_le_card (Finset.filter_subset
      (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
    have hpC : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
    have hqC : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
    have hzC : (externalTargets G C).card = zCount := by
      simpa using (Fintype.card_congr L.z).symm
    change directCount G C.P _ ≤ C.P.card at h1
    change directCount G C.H _ ≤ C.H.card at h2
    change directCount G C.Q _ ≤ C.Q.card at h3
    change directCount G (externalTargets G C) _ ≤
      (externalTargets G C).card at h4
    omega
  have h65536 : (65536 : BitVec 32).toNat = 65536 := by decide
  have h4096 : (4096 : BitVec 32).toNat = 4096 := by decide
  have h512 : (512 : BitVec 32).toNat = 512 := by decide
  have h64 : (64 : BitVec 32).toNat = 64 := by decide
  have h8 : (8 : BitVec 32).toNat = 8 := by decide
  unfold pKey SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.pInvariantKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  norm_num [BitVec.toNat_ofNat]
  rw [hDegree, hZ, hQ, hA1, hX, hP]
  rw [h65536, h4096, h512, h64, h8]
  repeat' rw [Nat.mod_eq_of_lt (by omega)]
  rw [P_outdegree_eq_blocks G C L hG p hp]

theorem ordered_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hzCases : zCount = 1 ∨ zCount = 2 ∨ zCount = 3)
    (hHCard : C.H.card = 6) (hA1Card : C.A1.card = 3)
    (hXCard : C.X.card = 3)
    (hPOrder : ∀ i : Fin 4, SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.pInvariantKey G C (L.p ⟨i.val+1, by omega⟩).1 ≤
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.pInvariantKey G C (L.p ⟨i.val, by omega⟩).1)
    (hAOrder : ∀ i : Fin 2, SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨i.val+2, by omega⟩).1 ≤
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨i.val+1, by omega⟩).1)
    (hXOrder : ∀ i : Fin 2, SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨i.val+5, by omega⟩).1 ≤
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨i.val+4, by omega⟩).1)
    (hQOrder : SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.qInvariantKey G C (L.q 1).1 ≤ SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.qInvariantKey G C (L.q 0).1)
    (hZOrder : ∀ i : Fin (zCount-1),
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.zInvariantKey G C (L.z ⟨i.val+1, by omega⟩).1 ≤
        SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.zInvariantKey G C (L.z ⟨i.val, by omega⟩).1) :
    ordered zCount (encodedArc (graphBits G L)) = true := by
  simp only [ordered, Bool.and_eq_true, all_eq_true_iff,
    BitVec.ule_eq_decide, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    rw [pKey_toNat G C L hG hzLe hHCard hA1Card hXCard (p+1) (by omega),
      pKey_toNat G C L hG hzLe hHCard hA1Card hXCard p (by omega)]
    exact hPOrder ⟨p, hp⟩
  · intro a ha
    rw [aBOut_toNat G C L hG hzLe (a+2) (by omega),
      aBOut_toNat G C L hG hzLe (a+1) (by omega)]
    simpa [SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey, Nat.add_comm] using hAOrder ⟨a, ha⟩
  · intro x hx
    rw [aBOut_toNat G C L hG hzLe (x+5) (by omega),
      aBOut_toNat G C L hG hzLe (x+4) (by omega)]
    simpa [SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey, Nat.add_comm] using hXOrder ⟨x, hx⟩
  · rw [qIn_toNat G C L hG hzLe 1 (by omega),
      qIn_toNat G C L hG hzLe 0 (by omega)]
    exact hQOrder
  · rcases hzCases with rfl | rfl | rfl
    · simp [orderedZ]
    · rw [orderedZ, if_neg (by decide), if_pos (by decide)]
      simp only [
        BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [zIn_toNat G C L hG (by omega) 1 (by omega),
        zIn_toNat G C L hG (by omega) 0 (by omega)]
      exact hZOrder 0
    · rw [orderedZ, if_neg (by decide), if_neg (by decide)]
      simp only [Bool.and_eq_true,
        BitVec.ule_eq_decide, decide_eq_true_eq]
      constructor
      · rw [zIn_toNat G C L hG (by omega) 1 (by omega),
          zIn_toNat G C L hG (by omega) 0 (by omega)]
        exact hZOrder 0
      · rw [zIn_toNat G C L hG (by omega) 2 (by omega),
          zIn_toNat G C L hG (by omega) 1 (by omega)]
        exact hZOrder 1

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.OrderingBridge
