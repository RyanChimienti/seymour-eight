import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CommonBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly EffectiveBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pAOneOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3)
    (p : Nat) (hp : p < 6) :
    (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat =
      directCount G C.A1 (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A1 (aOneLabelEquiv G C L hA1Card) _
  intro i
  rw [pToA_graph G L p (1 + i) hp (by omega)]
  have hFin : (⟨1 + i.val, by omega⟩ : Fin 8) =
      ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    simp only
    omega
  simp [hFin]

theorem pXOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 4)
    (p : Nat) (hp : p < 6) :
    (count 4 fun x ↦ pToA (graphArc G L) p (4 + x)).toNat =
      directCount G C.X (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.X (xLabelEquiv G C L hXCard) _
  intro i
  rw [pToA_graph G L p (4 + i) hp (by omega)]
  have hFin : (⟨4 + i.val, by omega⟩ : Fin 8) =
      ⟨i.val + 4, by omega⟩ := by
    apply Fin.ext
    simp only
    omega
  simp [hFin]

theorem zIn_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (z : Nat) (hz : z < zCount) :
    (zIn (graphPToZ G L) z).toNat = zInvariantKey G C (L.z ⟨z, hz⟩).1 := by
  rw [zIn, toNat_count_eq_fin_sum 6 _ (by omega)]
  unfold zInvariantKey
  rw [edgeCount_eq_sum_fin G C.P {(L.z ⟨z, hz⟩).1} L.p]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pToZ_graph G L p z p.isLt hz]
  by_cases hAdj : G.Adj (L.p p) (L.z ⟨z, hz⟩) <;>
    simp [directCount, CertificateBridge.internalFirstNeighbors,
      Finset.filter_singleton, hAdj]

theorem pToQBit_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (p : Nat) (hp : p < 6) :
    (bitCount (pToQ (graphArc G L) p)).toNat =
      if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0 := by
  rw [pToQ_graph G L p hp]
  by_cases hAdj : G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 <;>
    simp [bitCount, hAdj]

theorem pDegree_toNat {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) (p : Nat) (hp : p < 6) :
    (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat =
      directCount G C.P (L.p ⟨p, hp⟩).1 +
        directCount G C.H (L.p ⟨p, hp⟩).1 +
          directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 +
            (if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0) := by
  have hBlocks := pBlockCounts G C L hG hHCard (by omega) p hp
  have hAux := pAuxOut_toNat G C L hG hHCard yValue hy hyCases hzLe p hp
  have hDis : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
  have hQ : directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 =
      if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0 := by
    by_cases hAdj : G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hPLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.P)
  have hHLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.H)
  have hZLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
  have hQLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) ({(L.q 0).1} : Finset V))
  change directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at hPLe
  change directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at hHLe
  change directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card at hZLe
  change directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 ≤ 1 at hQLe
  rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hDis, hQ] at hAux
  simp only [pDegree, BitVec.toNat_add]
  rw [hBlocks.1, hBlocks.2.1, hAux]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem pNonSeymour_true {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) :
    pNonSeymour yValue zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [pNonSeymour, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSecond := projectedSecondCount_le_graph_retained G C L hG (by omega)
    (8 + p) (by omega)
  have hSource : labelledVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [labelledVertex, show ¬8 + p < 8 by omega, show 8 + p < 14 by omega]
  rw [hSource] at hSecond
  have hPDegree := pDegree_toNat G C L hG hHCard hy hyCases hzLe p hp
  have hQ := qSingleton G C L
  have hCaptured :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG (L.p ⟨p, hp⟩).1 (L.p _).2
  have hDis : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
  rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hDis] at hCaptured
  have hQDirect : directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 =
      if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0 := by
    by_cases hAdj : G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  rw [hQDirect] at hCaptured
  have hDegreeEq :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat =
        G.outdegree (L.p ⟨p, hp⟩).1 := by
    rw [hPDegree, hCaptured]
    omega
  rw [hDegreeEq]
  exact hSecond.trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hs ↦ hNoSeymour ⟨_, hs⟩))

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

theorem pRowKey_toNat {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) (p : Nat) (hp : p < 6) :
    (pRowKey yValue zCount (graphArc G L) (graphPToZ G L) p).toNat =
      pInvariantKey G C (L.q 0).1 (L.p ⟨p, hp⟩).1 := by
  have hDegree := pDegree_toNat G C L hG hHCard hy hyCases hzLe p hp
  have hBlocks := pBlockCounts G C L hG hHCard (by omega) p hp
  have hQ := pToQBit_toNat G C L p hp
  have hA1 := pAOneOut_toNat G C L hA1Card p hp
  have hX := pXOut_toNat G C L hXCard p hp
  have hDegreeSmall :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat < 2 ^ 32 :=
    (BitVec.isLt _).trans (by norm_num)
  have hZSmall : (pZOut zCount (graphPToZ G L) p).toNat < 2 ^ 32 :=
    (BitVec.isLt _).trans (by norm_num)
  have hQSmall : (bitCount (pToQ (graphArc G L) p)).toNat < 2 ^ 32 :=
    (BitVec.isLt _).trans (by norm_num)
  have hA1Small :
      (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat < 2 ^ 32 :=
    (BitVec.isLt _).trans (by norm_num)
  have hXSmall :
      (count 4 fun x ↦ pToA (graphArc G L) p (4 + x)).toNat < 2 ^ 32 :=
    (BitVec.isLt _).trans (by norm_num)
  have hPSmall : (pOut (graphArc G L) p).toNat < 2 ^ 32 :=
    (BitVec.isLt _).trans (by norm_num)
  have hDegreeByte := BitVec.isLt
    (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p)
  have hZByte := BitVec.isLt (pZOut zCount (graphPToZ G L) p)
  have hQByte := BitVec.isLt (bitCount (pToQ (graphArc G L) p))
  have hA1Byte := BitVec.isLt
    (count 3 fun a ↦ pToA (graphArc G L) p (1 + a))
  have hXByte := BitVec.isLt
    (count 4 fun x ↦ pToA (graphArc G L) p (4 + x))
  have hPByte := BitVec.isLt (pOut (graphArc G L) p)
  have hPLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.P)
  have hHLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.H)
  have hZLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
  have hA1Le := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.A1)
  have hXLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.X)
  change directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at hPLe
  change directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at hHLe
  change directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card at hZLe
  change directCount G C.A1 (L.p ⟨p, hp⟩).1 ≤ C.A1.card at hA1Le
  change directCount G C.X (L.p ⟨p, hp⟩).1 ≤ C.X.card at hXLe
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  rw [hDegree] at hDegreeByte
  rw [hBlocks.2.2] at hZByte
  rw [hQ] at hQByte
  rw [hA1] at hA1Byte
  rw [hX] at hXByte
  rw [hBlocks.1] at hPByte
  have h65536 : (65536 : BitVec 32).toNat = 65536 := by decide
  have h4096 : (4096 : BitVec 32).toNat = 4096 := by decide
  have h2048 : (2048 : BitVec 32).toNat = 2048 := by decide
  have h256 : (256 : BitVec 32).toNat = 256 := by decide
  have h16 : (16 : BitVec 32).toNat = 16 := by decide
  unfold pRowKey pInvariantKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hDegreeSmall, Nat.mod_eq_of_lt hZSmall,
    Nat.mod_eq_of_lt hQSmall, Nat.mod_eq_of_lt hA1Small,
    Nat.mod_eq_of_lt hXSmall, Nat.mod_eq_of_lt hPSmall]
  rw [h65536, h4096, h2048, h256, h16]
  have hmDegree :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat *
        65536 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 65536 := by omega
      _ < 2 ^ 32 := by norm_num
  have hmZ : (pZOut zCount (graphPToZ G L) p).toNat * 4096 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 4096 := by omega
      _ < 2 ^ 32 := by norm_num
  have hmQ : (bitCount (pToQ (graphArc G L) p)).toNat * 2048 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 2048 := by omega
      _ < 2 ^ 32 := by norm_num
  have hmA1 : (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat *
      256 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 256 := by omega
      _ < 2 ^ 32 := by norm_num
  have hmX : (count 4 fun x ↦ pToA (graphArc G L) p (4 + x)).toNat *
      16 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 16 := by omega
      _ < 2 ^ 32 := by norm_num
  have hs1 :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat * 65536 +
        (pZOut zCount (graphPToZ G L) p).toNat * 4096 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 65536 + 255 * 4096 := by omega
      _ < 2 ^ 32 := by norm_num
  have hs2 :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat * 65536 +
          (pZOut zCount (graphPToZ G L) p).toNat * 4096 +
        (bitCount (pToQ (graphArc G L) p)).toNat * 2048 < 2 ^ 32 := by
    calc
      _ ≤ 255 * 65536 + 255 * 4096 + 255 * 2048 := by omega
      _ < 2 ^ 32 := by norm_num
  have hs3 :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat * 65536 +
            (pZOut zCount (graphPToZ G L) p).toNat * 4096 +
          (bitCount (pToQ (graphArc G L) p)).toNat * 2048 +
        (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat * 256 <
          2 ^ 32 := by
    calc
      _ ≤ 255 * 65536 + 255 * 4096 + 255 * 2048 + 255 * 256 := by omega
      _ < 2 ^ 32 := by norm_num
  have hs4 :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat * 65536 +
              (pZOut zCount (graphPToZ G L) p).toNat * 4096 +
            (bitCount (pToQ (graphArc G L) p)).toNat * 2048 +
          (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat * 256 +
        (count 4 fun x ↦ pToA (graphArc G L) p (4 + x)).toNat * 16 <
          2 ^ 32 := by
    calc
      _ ≤ 255 * 65536 + 255 * 4096 + 255 * 2048 + 255 * 256 +
          255 * 16 := by omega
      _ < 2 ^ 32 := by norm_num
  have hs5 :
      (pDegree yValue zCount (graphArc G L) (graphPToZ G L) p).toNat * 65536 +
                (pZOut zCount (graphPToZ G L) p).toNat * 4096 +
              (bitCount (pToQ (graphArc G L) p)).toNat * 2048 +
            (count 3 fun a ↦ pToA (graphArc G L) p (1 + a)).toNat * 256 +
          (count 4 fun x ↦ pToA (graphArc G L) p (4 + x)).toNat * 16 +
        (pOut (graphArc G L) p).toNat < 2 ^ 32 := by
    calc
      _ ≤ 255 * 65536 + 255 * 4096 + 255 * 2048 + 255 * 256 +
          255 * 16 + 255 := by omega
      _ < 2 ^ 32 := by norm_num
  rw [Nat.mod_eq_of_lt hmDegree, Nat.mod_eq_of_lt hmZ,
    Nat.mod_eq_of_lt hmQ, Nat.mod_eq_of_lt hmA1, Nat.mod_eq_of_lt hmX]
  rw [Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt hs2, Nat.mod_eq_of_lt hs3,
    Nat.mod_eq_of_lt hs4, Nat.mod_eq_of_lt hs5]
  rw [hDegree, hBlocks.1, hBlocks.2.2, hQ, hA1, hX]

theorem orderedP_true {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4)
    (hOrder : ∀ q : Fin 5,
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1) :
    orderedP yValue zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pRowKey_toNat G C L hG hHCard hA1Card hXCard hy hyCases hzLe
      (p + 1) (by omega),
    pRowKey_toNat G C L hG hHCard hA1Card hXCard hy hyCases hzLe p (by omega)]
  exact hOrder ⟨p, hp⟩

set_option linter.flexible false in
theorem commonCore_true {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hHCard : C.H.card = 7) (hA1Card : C.A1.card = 3)
    (hXCard : C.X.card = 4)
    (hk : C.k = 3) (hr : C.r = 6) (hx : C.x = 4)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) (he : yValue + zCount = 3 ∨ yValue + zCount = 4)
    (hPOrder : ∀ q : Fin 5,
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1)
    (hAOneOrder : ∀ q : Fin 2,
      aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 3,
      aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1)
    (hZOrder : ∀ q : Fin (zCount - 1),
      zInvariantKey G C (L.z ⟨q.val + 1, by omega⟩).1 ≤
        zInvariantKey G C (L.z ⟨q.val, by omega⟩).1) :
    commonCore yValue zCount (graphArc G L) (graphPToZ G L) = true := by
  have hOrA := orientedA_true G C L hG
  have hOrP := orientedP_true G C L hG
  have hOrPH := orientedPH_true G C L hG
  have hFixed := fixedAOne_true G C L hG
  have hNoPA1 := noPToAOne_true G C L hG
  have hQB := qInB_true G C L
  have hXReach := everyXReached_true G C L hA1Card
  have hZReach := everyZReached_true G C L
  have hInactive := inactiveZZero_true G C L hzLe
  have hQReach := qReachStatus_true G C L hA1Card yValue hy hyCases
  have hACond := aConditions_true G C L hG hPivot hMin hk hr
  have hPCond := pConditions_true G C L hG hHCard hMin
    yValue hy hyCases hzLe
  have hANS := aNonSeymour_true G C L hG hNoSeymour (by omega)
  have hPNS := pNonSeymour_true G C L hG hHCard hNoSeymour
    hy hyCases hzLe
  have hAMin : ∀ a < 8,
      (3 : BitVec 8).ule (aOut (graphArc G L) a) = true := by
    rw [aConditions, all_eq_true_iff] at hACond
    intro a ha
    have h := hACond a ha
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hThree := degreeThreeConsequences_true G C L hOrA hAMin
  have hDual := degreeAndDual_of_local yValue (graphArc G L) hyCases
    hOrA hOrPH hFixed hXReach hQReach hACond
  have hMissing := externalMissing_le_nine G C L hG hMin hHCard
    hRootDegree hk hr hx yValue hy hyCases hzLe he
  have hMissingBool :
      (externalMissing yValue zCount (graphArc G L) (graphPToZ G L)).ule 9 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hMissing
  have hEffective := pEffectiveConditions_true G C L hG hMin hNoSeymour
    hHCard yValue hy hyCases hzLe he hMissing
  have hSharp := sharpKing_of_orientedP (graphArc G L) hOrP
  have hOrdP := orderedP_true G C L hG hHCard hA1Card hXCard hy hyCases
    hzLe hPOrder
  have hOrdA := orderedAClasses_true G C L hAOneOrder hXOrder
  have hOrdZ := orderedZ_true G C L hZOrder
  simp [commonCore, hOrA, hOrP, hOrPH, hFixed, hNoPA1, hQB, hXReach,
    hZReach, hInactive, hQReach, hACond, hPCond, hANS, hPNS, hThree.1, hThree.2,
    hDual, hEffective, hSharp, hOrdP, hOrdA, hOrdZ]
  exact hMissingBool

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CommonBridge
