import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.OrderingBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pAOneOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3)
    (p : Nat) (hp : p < 5) :
    (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat =
      directCount G C.A1 (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A1 (aOneLabelEquiv G C L hA1Card) _
  intro i
  rw [pToA_graph G L p (1 + i) hp (by omega)]
  simp [Nat.add_comm]

theorem pXOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 4)
    (p : Nat) (hp : p < 5) :
    (count 4 fun x ↦ pToA (graphArc G L) p (4 + x)).toNat =
      directCount G C.X (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.X (xLabelEquiv G C L hXCard) _
  intro i
  rw [pToA_graph G L p (4 + i) hp (by omega)]
  simp [Nat.add_comm]

theorem zIn_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (z : Nat) (hz : z < zCount) :
    (zIn (graphPToZ G L) z).toNat = zInvariantKey G C (L.z ⟨z, hz⟩).1 := by
  rw [zIn, toNat_count_eq_fin_sum 5 _ (by omega)]
  unfold zInvariantKey
  rw [edgeCount_eq_sum_fin G C.P {(L.z ⟨z, hz⟩).1} L.p]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pToZ_graph G L p z p.isLt hz]
  by_cases hAdj : G.Adj (L.p p) (L.z ⟨z, hz⟩) <;>
    simp [directCount, CertificateBridge.internalFirstNeighbors,
      Finset.filter_singleton, hAdj]

theorem qIn_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (q : Nat) (hq : q < 2) :
    (qIn (graphArc G L) q).toNat = qInvariantKey G C (L.q ⟨q, hq⟩).1 := by
  rw [qIn, BitVec.toNat_add]
  have hA : (count 8 fun a ↦ aToQ (graphArc G L) a q).toNat =
      edgeCount G C.A {(L.q ⟨q, hq⟩).1} := by
    rw [toNat_count_eq_fin_sum 8 _ (by omega)]
    rw [edgeCount_eq_sum_fin G C.A {(L.q ⟨q, hq⟩).1} L.a]
    apply Finset.sum_congr rfl
    intro a ha
    rw [aToQ_graph G L a q a.isLt hq]
    by_cases hAdj : G.Adj (L.a a).1 (L.q ⟨q, hq⟩).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  have hP : (count 5 fun p ↦ pToQ (graphArc G L) p q).toNat =
      edgeCount G C.P {(L.q ⟨q, hq⟩).1} := by
    rw [toNat_count_eq_fin_sum 5 _ (by omega)]
    rw [edgeCount_eq_sum_fin G C.P {(L.q ⟨q, hq⟩).1} L.p]
    apply Finset.sum_congr rfl
    intro p hp
    rw [pToQ_graph G L p q p.isLt hq]
    by_cases hAdj : G.Adj (L.p p).1 (L.q ⟨q, hq⟩).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  have hDis : Disjoint C.A C.P := Finset.disjoint_of_subset_right
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
    (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)
  unfold qInvariantKey
  rw [hA, hP, Nat.mod_eq_of_lt (by
    have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
    have ha := edgeCount_le_card_mul_card G C.A {(L.q ⟨q, hq⟩).1}
    have hp := edgeCount_le_card_mul_card G C.P {(L.q ⟨q, hq⟩).1}
    simp only [Finset.card_singleton] at ha hp
    omega)]
  unfold edgeCount
  rw [Finset.sum_union hDis]

theorem orderedZ_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hOrder : ∀ q : Fin (zCount - 1),
      zInvariantKey G C (L.z ⟨q.val + 1, by omega⟩).1 ≤
        zInvariantKey G C (L.z ⟨q.val, by omega⟩).1) :
    orderedZ zCount (graphPToZ G L) = true := by
  rw [orderedZ, all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zIn_toNat G C L (z + 1) (by omega), zIn_toNat G C L z (by omega)]
  exact hOrder ⟨z, hz⟩

theorem orderedAClasses_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hAOneOrder : ∀ q : Fin 2,
      aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 3,
      aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1) :
    orderedAClasses (graphArc G L) = true := by
  simp only [orderedAClasses, Bool.and_eq_true, all_eq_true_iff,
    BitVec.ule_eq_decide, decide_eq_true_eq]
  constructor
  · intro a ha
    rw [aBOut_toNat G C L (2 + a) (by omega),
      aBOut_toNat G C L (1 + a) (by omega)]
    simpa [aInvariantKey, Nat.add_comm] using hAOneOrder ⟨a, ha⟩
  · intro x hx
    rw [aBOut_toNat G C L (5 + x) (by omega),
      aBOut_toNat G C L (4 + x) (by omega)]
    simpa [aInvariantKey, Nat.add_comm] using hXOrder ⟨x, hx⟩

theorem orderedQ_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hOrder : qInvariantKey G C (L.q 1).1 ≤ qInvariantKey G C (L.q 0).1) :
    orderedQ (graphArc G L) = true := by
  simp only [orderedQ, BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [qIn_toNat G C L 1 (by omega), qIn_toNat G C L 0 (by omega)]
  exact hOrder

theorem pRowKey_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hzLe : zCount ≤ 2) (p : Nat) (hp : p < 5) :
    (pRowKey zCount (graphArc G L) (graphPToZ G L) p).toNat =
      pInvariantKey G C (L.p ⟨p, hp⟩).1 := by
  have hBlocks := pBlockCounts G C L hHCard (by omega) p hp
  have hDegree := pDegree_toNat G C L hG hHCard hzLe p hp
  have hA1 := pAOneOut_toNat G C L hA1Card p hp
  have hX := pXOut_toNat G C L hXCard p hp
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hA1Le := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.A1)
  have hXLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.X)
  have hPL := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.P)
  have hQL := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.Q)
  have hZL := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
  change directCount G C.A1 (L.p ⟨p, hp⟩).1 ≤ C.A1.card at hA1Le
  change directCount G C.X (L.p ⟨p, hp⟩).1 ≤ C.X.card at hXLe
  change directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at hPL
  change directCount G C.Q (L.p ⟨p, hp⟩).1 ≤ C.Q.card at hQL
  change directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤
    (externalTargets G C).card at hZL
  have hDegreeLe : G.outdegree (L.p ⟨p, hp⟩).1 ≤ 16 := by
    rw [P_outdegree_eq_blocks G C L hG p hp]
    have hHLe := Finset.card_le_card (Finset.filter_subset
      (G.Adj (L.p ⟨p, hp⟩).1) C.H)
    change directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at hHLe
    omega
  have h65536 : (65536 : BitVec 32).toNat = 65536 := by decide
  have h4096 : (4096 : BitVec 32).toNat = 4096 := by decide
  have h512 : (512 : BitVec 32).toNat = 512 := by decide
  have h64 : (64 : BitVec 32).toNat = 64 := by decide
  have h8 : (8 : BitVec 32).toNat = 8 := by decide
  unfold pRowKey pInvariantKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  norm_num [BitVec.toNat_ofNat]
  rw [hDegree, hBlocks.2.2.2, hBlocks.2.2.1, hA1, hX, hBlocks.1]
  rw [h65536, h4096, h512, h64, h8]
  repeat' rw [Nat.mod_eq_of_lt (by omega)]
  rw [P_outdegree_eq_blocks G C L hG p hp]

theorem orderedP_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hzLe : zCount ≤ 2)
    (hOrder : ∀ q : Fin 4,
      pInvariantKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.p ⟨q.val, by omega⟩).1) :
    orderedP zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pRowKey_toNat G C L hG hHCard hA1Card hXCard hzLe (p + 1) (by omega),
    pRowKey_toNat G C L hG hHCard hA1Card hXCard hzLe p (by omega)]
  exact hOrder ⟨p, hp⟩

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.OrderingBridge
