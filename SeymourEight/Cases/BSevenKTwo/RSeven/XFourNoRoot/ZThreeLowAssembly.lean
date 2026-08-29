import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeAssembly
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLabels
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowNormalization
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowSharpKing
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowMZeroNoExact
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowMOneNoExact

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Low external-defect assembly for the three-`Z` row

The graph-level capacity calculation at defect two has a sharper
specialization at defects zero and one.  This closes both leaves in the same
147-bit projection.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowBridge

open CertificateBridge Shared ZThreeCore ZThreeLowCore
open FiveZExactGraphBridge FiveZUnionEightCapacity IndividualEffective
open BroadFourBridge RepeatedSharedOmissionBridge
open ZThreeBridge ZThreeLabels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (C : G.LocalConfiguration) (L : Labels G C) :
    Encoding := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.h i).1)
      (fun i ↦ (L.z i).1)

/-- At external defect at most one, the exceptional two-neighbor row has
eight effective targets and every other row has at least seven. -/
theorem low_effective_lower (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 3)
    (m : Nat) (hm : m ≤ 1)
    (hMissing : 21 - edgeCount G C.P C.Z = m)
    (p : V) (hpP : p ∈ C.P) :
    (if m = 1 ∧ (directZNeighbors G C p).card = 2 then 8 else 7) ≤
      (directZEffectiveUnion G C p).card := by
  let S := directZNeighbors G C p
  let U := directZEffectiveUnion G C p
  have hsLe : S.card ≤ 3 :=
    (Finset.card_le_card (directZNeighbors_subset_Z G C p)).trans_eq hZCard
  have hsPos : 2 ≤ S.card := by
    have hRow := row_missing_le_total_missing_three G C hPCard hZCard p hpP
    change 3 - S.card ≤ 21 - edgeCount G C.P C.Z at hRow
    rw [hMissing] at hRow
    omega
  have hLower := directZ_effective_capacity_lower G C hMin p
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directZ_to_P_capacity_three G C hG hPCard hZCard p hpP
  change S.card * (8 - U.card) ≤
    edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ S.card.choose 2 at hInternal
  rw [hMissing] at hToP
  change edgeCount G S C.P ≤ m - (3 - S.card) at hToP
  change (if m = 1 ∧ S.card = 2 then 8 else 7) ≤ U.card
  interval_cases m <;> interval_cases hS : S.card <;>
    simp_all [Nat.choose] <;> omega

theorem lowPConditions_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hNoRoot : epsilonS G C = 0)
    (m : Nat) (hm : m ≤ 1)
    (hMissing : 21 - edgeCount G C.P C.Z = m) :
    lowPConditions (graphBits G C L) = true := by
  let bits := graphBits G C L
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr L.p).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr L.h).symm
  have hZCard : C.Z.card = 3 := by
    simpa using (Fintype.card_congr L.z).symm
  have hPZNat := totalPToZ_toNat G C.P C.H C.Z L.p L.h L.z hG
  have hPZLe : edgeCount G C.P C.Z ≤ 21 := by
    exact (edgeCount_le_card_mul_card G C.P C.Z).trans_eq (by
      rw [hPCard, hZCard])
  have hPZ : edgeCount G C.P C.Z = 21 - m := by omega
  have hExtNat : (externalMissing bits).toNat = m := by
    rw [externalMissing, BitVec.toNat_sub]
    change (256 - (totalPToZ bits).toNat + 21) % 256 = m
    rw [show (totalPToZ bits).toNat = edgeCount G C.P C.Z by
      simpa [bits] using hPZNat]
    rw [hPZ]
    interval_cases m <;> decide
  rw [lowPConditions, ZThreeBridge.all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hBlocks := pBlockCounts G C.P C.H C.Z L.p L.h L.z hG p hp
  have hDegree := pDegree_toNat G C L.p L.h L.z hG hPB hNoRoot p hp
  have hMinimum : (8 : BitVec 8).ule (pDegree bits p) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (pDegree bits p).toNat = G.outdegree v by
      simpa [bits, v] using hDegree]
    exact hMin v
  have hEff := low_effective_lower G C hG hMin hPCard hZCard m hm
    hMissing v (L.p ⟨p, hp⟩).2
  have hSecond := pSecondCount_le_graph G C.P C.H C.Z L.p L.h L.z p hp
  have hUnion := PSecond_add_directZEffective_card_le_second_add_H
    G C hG hPB hNoRoot v (L.p ⟨p, hp⟩).2
  have hNot : ¬G.IsSeymourVertex v := fun h ↦ hNoSeymour ⟨v, h⟩
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
  have hEffNat : (lowEffectiveLower bits p).toNat =
      (if m = 1 ∧ (directZNeighbors G C v).card = 2 then 8 else 7) := by
    have hZNat : (pZOut bits p).toNat = directCount G C.Z v := by
      simpa [bits, v] using hBlocks.2.2
    have hCard : (directZNeighbors G C v).card = directCount G C.Z v :=
      card_directZNeighbors G C v
    interval_cases m
    · have hExt : externalMissing bits = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hExtNat
      simp [lowEffectiveLower, hExt]
    · have hExt : externalMissing bits = 1 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hExtNat
      by_cases hs : directCount G C.Z v = 2
      · have hZ : pZOut bits p = 2 := by
          apply BitVec.eq_of_toNat_eq
          rw [hZNat, hs]
          decide
        simp [lowEffectiveLower, hExt, hCard, hs]
        split <;> simp_all
      · have hZ : pZOut bits p ≠ 2 := by
          intro he
          have hn := congrArg BitVec.toNat he
          rw [hZNat] at hn
          simp [hs] at hn
        have hZFalse : (pZOut bits p == 2) = false := decide_eq_false hZ
        simp [lowEffectiveLower, hExt, hCard, hs]
        split <;> simp_all
  have hIneqNat : (pSecondCount bits p).toNat +
      (lowEffectiveLower bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut bits p).toNat := by
    have hU : (pSecondCount bits p).toNat +
        (directZEffectiveUnion G C v).card ≤
        G.secondOutdegree v + directCount G C.H v := by
      have hSecond' : (pSecondCount bits p).toNat ≤
          (C.P.filter fun w ↦ w ∈ G.secondOutNeighborFinset v).card := by
        simpa [bits, v] using hSecond
      exact (Nat.add_le_add_right hSecond' _).trans (by simpa [v] using hUnion)
    have hU' : (pSecondCount bits p).toNat +
        (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card ≤
        G.secondOutdegree (L.p ⟨p, hp⟩).1 +
          directCount G C.H (L.p ⟨p, hp⟩).1 := by
      simpa [v] using hU
    have hEff' : (if m = 1 ∧
        directCount G C.Z (L.p ⟨p, hp⟩).1 = 2 then 8 else 7) ≤
        (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card := by
      simpa [v, card_directZNeighbors] using hEff
    have hNS' : G.secondOutdegree (L.p ⟨p, hp⟩).1 <
        G.outdegree (L.p ⟨p, hp⟩).1 := by simpa [v] using hNS
    have hDegreeBlocks : G.outdegree (L.p ⟨p, hp⟩).1 =
        directCount G C.P (L.p ⟨p, hp⟩).1 +
          directCount G C.H (L.p ⟨p, hp⟩).1 +
          directCount G C.Z (L.p ⟨p, hp⟩).1 := by
      have hpLe : directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 7 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
      have hhLe : directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 6 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
      have hzLe : directCount G C.Z (L.p ⟨p, hp⟩).1 ≤ 3 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      simpa [pDegree, bits, BitVec.toNat_add, hBlocks.1, hBlocks.2.1,
        hBlocks.2.2, Nat.mod_eq_of_lt (by omega :
          directCount G C.P (L.p ⟨p, hp⟩).1 +
            directCount G C.H (L.p ⟨p, hp⟩).1 < 256),
        Nat.mod_eq_of_lt (by omega :
          directCount G C.P (L.p ⟨p, hp⟩).1 +
            directCount G C.H (L.p ⟨p, hp⟩).1 +
            directCount G C.Z (L.p ⟨p, hp⟩).1 < 256)] using hDegree.symm
    rw [hEffNat, card_directZNeighbors G C v,
      hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    dsimp [v]
    omega
  have hBool :
      (pSecondCount bits p + lowEffectiveLower bits p + 1).ule
        (pOut bits p + 2 * pHOut bits p + pZOut bits p) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_mul]
    norm_num [BitVec.toNat_ofNat]
    change ((pSecondCount bits p).toNat +
        (lowEffectiveLower bits p).toNat + 1) % 256 ≤
      ((pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut bits p).toNat) % 256
    have hSecondCap : (pSecondCount bits p).toNat ≤ 7 := by
      have hs : (pSecondCount bits p).toNat ≤
          (C.P.filter fun w ↦ w ∈
            G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
        simpa [bits] using hSecond
      exact hs.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        hPCard)
    have hEffCap : (lowEffectiveLower bits p).toNat ≤ 8 := by
      rw [hEffNat]
      split <;> omega
    have hL : (pSecondCount bits p).toNat +
        (lowEffectiveLower bits p).toNat + 1 < 256 := by omega
    have hR : (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut bits p).toNat < 256 := by
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      have hpLe : directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 7 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
      have hhLe : directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 6 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
      have hzLe : directCount G C.Z (L.p ⟨p, hp⟩).1 ≤ 3 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      omega
    rw [Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hR]
    exact hIneqNat
  rw [Bool.and_eq_true]
  exact ⟨hMinimum, hBool⟩

theorem lowRowKey_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoRoot : epsilonS G C = 0) (p : Nat) (hp : p < 7) :
    (rowKey (graphBits G C L) p).toNat =
      256 * G.outdegree (L.p ⟨p, hp⟩).1 +
        16 * directCount G C.P (L.p ⟨p, hp⟩).1 +
        directCount G C.H (L.p ⟨p, hp⟩).1 := by
  have hDegree := pDegree_toNat G C L.p L.h L.z hG hPB hNoRoot p hp
  have hBlocks := pBlockCounts G C.P C.H C.Z L.p L.h L.z hG p hp
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hHCard : C.H.card = 6 := by simpa using (Fintype.card_congr L.h).symm
  have hPLe : directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hdSmall : (pDegree (graphBits G C L) p).toNat < 2 ^ 16 :=
    (BitVec.isLt _).trans (show 2 ^ 8 < 2 ^ 16 by decide)
  have hpSmall : (pOut (graphBits G C L) p).toNat < 2 ^ 16 :=
    (BitVec.isLt _).trans (show 2 ^ 8 < 2 ^ 16 by decide)
  have hhSmall : (pHOut (graphBits G C L) p).toNat < 2 ^ 16 :=
    (BitVec.isLt _).trans (show 2 ^ 8 < 2 ^ 16 by decide)
  simp only [rowKey, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hdSmall, Nat.mod_eq_of_lt hpSmall,
    Nat.mod_eq_of_lt hhSmall]
  rw [hDegree, hBlocks.1, hBlocks.2.1]
  have h256 : (256 : BitVec 16).toNat = 256 := by decide
  have h16 : (16 : BitVec 16).toNat = 16 := by decide
  rw [h256, h16]
  have hDegLt : G.outdegree (L.p ⟨p, hp⟩).1 < 256 := by
    rw [← hDegree]
    exact BitVec.isLt _
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem zIn_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (z : Nat) (hz : z < 3) :
    (ZThreeNormalization.zIn (graphBits G C L) z).toNat =
      zIncoming G (fun i => (L.p i).1) (L.z ⟨z, hz⟩).1 := by
  classical
  rw [ZThreeNormalization.zIn, ZThreeBridge.toNat_count_eq_fin_sum 7 _
    (by omega)]
  unfold zIncoming
  apply Finset.sum_congr rfl
  intro p hp
  rw [pToZ_coreBits G.Adj _ _ _ p z p.isLt hz]
  by_cases hAdj : G.Adj (L.p p).1 (L.z ⟨z, hz⟩).1 <;> simp [hAdj]

theorem zOrbitKey_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (z : Nat) (hz : z < 3) :
    (ZThreeNormalization.zOrbitKey (graphBits G C L) z).toNat =
      zLabelKey G (fun i => (L.p i).1) (L.z ⟨z, hz⟩).1 := by
  rw [ZThreeNormalization.zOrbitKey, zLabelKey, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_sub, zIn_toNat G C L z hz]
  rw [pToZ_coreBits G.Adj _ _ _ 0 z (by omega) hz]
  norm_num [BitVec.toNat_ofNat, bitCount]
  have hInLe : zIncoming G (fun i => (L.p i).1) (L.z ⟨z, hz⟩).1 ≤ 7 := by
    unfold zIncoming
    calc
      _ ≤ ∑ _i : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> omega
      _ = 7 := by simp
  by_cases hAdj : G.Adj (L.p 0).1 (L.z ⟨z, hz⟩).1 <;>
    simp [hAdj] <;> omega

theorem orderedExternalRows_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoRoot : epsilonS G C = 0)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 3) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    ZThreeNormalization.orderedExternalRows (graphBits G C L) = true := by
  let L := canonicalLabels G C hPCard hHCard hZCard
  change ZThreeNormalization.orderedExternalRows (graphBits G C L) = true
  rw [ZThreeNormalization.orderedExternalRows, ZThreeBridge.all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  have hKey := canonicalLabels_p_key_anti G C hPCard hHCard hZCard
    (i := ⟨p, by omega⟩) (j := ⟨p + 1, by omega⟩)
    (Fin.mk_le_mk.mpr (by omega))
  have hKey' : pLowKey G C (L.p ⟨p, by omega⟩).1 ≥
      pLowKey G C (L.p ⟨p + 1, by omega⟩).1 := by
    simpa [L] using hKey
  have hLeft := pBlockCounts G C.P C.H C.Z L.p L.h L.z hG p (by omega)
  have hRight := pBlockCounts G C.P C.H C.Z L.p L.h L.z hG (p + 1)
    (by omega)
  have hDegreeLeft := pDegree_toNat G C L.p L.h L.z hG hPB hNoRoot p
    (by omega)
  have hDegreeRight := pDegree_toNat G C L.p L.h L.z hG hPB hNoRoot
    (p + 1) (by omega)
  have hDLt : G.outdegree (L.p ⟨p, by omega⟩).1 < 256 := by
    rw [← hDegreeLeft]
    exact BitVec.isLt _
  have hDRt : G.outdegree (L.p ⟨p + 1, by omega⟩).1 < 256 := by
    rw [← hDegreeRight]
    exact BitVec.isLt _
  have hPL : directCount G C.P (L.p ⟨p, by omega⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hPR : directCount G C.P (L.p ⟨p + 1, by omega⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHL : directCount G C.H (L.p ⟨p, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hHR : directCount G C.H (L.p ⟨p + 1, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hZL : directCount G C.Z (L.p ⟨p, by omega⟩).1 ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hZR : directCount G C.Z (L.p ⟨p + 1, by omega⟩).1 ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  rw [hLeft.2.2, hRight.2.2]
  unfold pLowKey pExternalDefect at hKey'
  omega

theorem orderedExternalZ_true (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 3) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    ZThreeNormalization.orderedExternalZ (graphBits G C L) = true := by
  let L := canonicalLabels G C hPCard hHCard hZCard
  change ZThreeNormalization.orderedExternalZ (graphBits G C L) = true
  rw [ZThreeNormalization.orderedExternalZ, ZThreeBridge.all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zOrbitKey_toNat G C L (z + 1) (by omega),
    zOrbitKey_toNat G C L z (by omega)]
  exact canonicalLabels_z_key_anti G C hPCard hHCard hZCard
    (i := ⟨z, by omega⟩) (j := ⟨z + 1, by omega⟩)
    (Fin.mk_le_mk.mpr (by omega))

theorem orderedH_true (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 3) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    orderedH (graphBits G C L) = true := by
  let L := canonicalLabels G C hPCard hHCard hZCard
  change orderedH (graphBits G C L) = true
  rw [orderedH, ZThreeBridge.all_eq_true_iff]
  intro h hh
  exact canonicalLabels_h_lex G C hPCard hHCard hZCard h hh

theorem orderedRowsFrom_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoRoot : epsilonS G C = 0)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 3) (start countRows : Nat)
    (hEnd : start + countRows < 7)
    (hSame : ∀ i : Fin countRows,
      directCount G C.Z
          ((canonicalLabels G C hPCard hHCard hZCard).p
            ⟨start + i.val, by have := i.isLt; omega⟩).1 =
        directCount G C.Z
          ((canonicalLabels G C hPCard hHCard hZCard).p
            ⟨start + i.val + 1, by have := i.isLt; omega⟩).1) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    orderedRowsFrom (graphBits G C L) start countRows = true := by
  let L := canonicalLabels G C hPCard hHCard hZCard
  change orderedRowsFrom (graphBits G C L) start countRows = true
  rw [orderedRowsFrom, ZThreeBridge.all_eq_true_iff]
  intro i hi
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [lowRowKey_toNat G C L hG hPB hNoRoot (start + i + 1) (by omega),
    lowRowKey_toNat G C L hG hPB hNoRoot (start + i) (by omega)]
  have hKey := canonicalLabels_p_key_anti G C hPCard hHCard hZCard
    (i := ⟨start + i, by omega⟩) (j := ⟨start + i + 1, by omega⟩)
    (Fin.mk_le_mk.mpr (by omega))
  have hKey' : pLowKey G C (L.p ⟨start + i, by omega⟩).1 ≥
      pLowKey G C (L.p ⟨start + i + 1, by omega⟩).1 := by
    simpa [L] using hKey
  have hSame' : directCount G C.Z (L.p ⟨start + i, by omega⟩).1 =
      directCount G C.Z (L.p ⟨start + i + 1, by omega⟩).1 := by
    simpa [L] using hSame ⟨i, hi⟩
  unfold pLowKey pExternalDefect at hKey'
  omega

theorem commonCoreNoExact_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 2) (hx : C.x = 4)
    (hy : BSevenKTwo.y G C = 0)
    (hNoRoot : epsilonS G C = 0)
    (hHCard : C.H.card = 6)
    (m : Nat) (hm : m ≤ 1)
    (hMissing : 21 - edgeCount G C.P C.Z = m)
    (hOrdered : orderedH (graphBits G C L) = true) :
    commonCoreNoExact (graphBits G C L) = true := by
  let bits := graphBits G C L
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr L.p).symm
  have hZCard : C.Z.card = 3 := by
    simpa using (Fintype.card_congr L.z).symm
  have hOrP : orientedP bits = true := by
    simpa [bits] using orientedP_true G C.P C.H C.Z L.p L.h L.z hG
  have hOrPH : orientedPH bits = true := by
    simpa [bits] using orientedPH_true G C.P C.H C.Z L.p L.h L.z hG
  have hZReach : allZReached bits = true := by
    simpa [bits] using allZReached_true G C L.p L.h L.z
  have hPHNat := totalPToH_toNat G C.P C.H C.Z L.p L.h L.z hG
  have hPPNat := totalPOut_toNat G C.P C.H C.Z L.p L.h L.z hG
  have hHPNat := totalHToP_toNat G C.P C.H C.Z L.p L.h L.z
  have hHP : 25 ≤ edgeCount G C.H C.P :=
    twentyFive_le_H_to_P G C hG hMin hRootDegree hk hx hy hPB
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHLe : edgeCount G C.P C.H ≤ 17 := by omega
  have hPPLe : edgeCount G C.P C.P ≤ 21 := by
    have hInternal := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at hInternal
    norm_num [Nat.choose] at hInternal
    exact hInternal
  have hPHBool : (totalPToH bits).ule 17 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalPToH bits).toNat = edgeCount G C.P C.H by
      simpa [bits] using hPHNat]
    exact hPHLe
  have hPPBool : (totalPOut bits).ule 21 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalPOut bits).toNat = edgeCount G C.P C.P by
      simpa [bits] using hPPNat]
    exact hPPLe
  have hHPBool : (25 : BitVec 8).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using hHPNat]
    exact hHP
  have hLow := lowPConditions_true G C L hG hPB hMin hNoSeymour hNoRoot
    m hm hMissing
  have hSharp := generalSharpKing_of_orientedP bits hOrP
  change commonCoreNoExact bits = true
  simp only [commonCoreNoExact, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hOrP, hOrPH⟩, hZReach⟩, hPHBool⟩,
    hPPBool⟩, hHPBool⟩, hLow⟩, hSharp⟩, hOrdered⟩

theorem directZ_eq_three_of_pattern (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (p : Nat) (hp : p < 7)
    (hPat : pZPattern (graphBits G C L) p true true true = true) :
    directCount G C.Z (L.p ⟨p, hp⟩).1 = 3 := by
  have hBlocks := pBlockCounts G C.P C.H C.Z L.p L.h L.z hG p hp
  have hBits : pZOut (graphBits G C L) p = 3 := by
    simp only [pZPattern, Bool.and_eq_true] at hPat
    rcases hPat with ⟨⟨h0, h1⟩, h2⟩
    simp only [beq_iff_eq] at h0 h1 h2
    simp [pZOut, count, h0, h1, h2, bitCount]
  rw [← hBlocks.2.2, hBits]
  decide

theorem zThree_lowDefect_impossible
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (_hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 3)
    (hLow : 21 - edgeCount G C.P C.Z ≤ 1) : False := by
  have hPB : C.P = C.B :=
    RepeatedSharedOmissionBridge.p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : C.Z.card = 3 := by
    change C.Z.card = 3 at hz
    exact hz
  let L := canonicalLabels G C hPCard hHCard hZCard
  let bits := graphBits G C L
  let m := 21 - edgeCount G C.P C.Z
  have hm : m ≤ 1 := hLow
  have hPZLe : edgeCount G C.P C.Z ≤ 21 := by
    exact (edgeCount_le_card_mul_card G C.P C.Z).trans_eq (by
      rw [hPCard, hZCard])
  have hPZ : edgeCount G C.P C.Z = 21 - m := by
    dsimp [m]
    omega
  have hPZNat := totalPToZ_toNat G C.P C.H C.Z L.p L.h L.z hG
  have hPHNat := totalPToH_toNat G C.P C.H C.Z L.p L.h L.z hG
  have hPPNat := totalPOut_toNat G C.P C.H C.Z L.p L.h L.z hG
  have hRows : ZThreeNormalization.orderedExternalRows bits = true := by
    have := orderedExternalRows_true G C hG hPB hNoRoot hPCard hHCard hZCard
    simpa [bits, L] using this
  have hZOrder : ZThreeNormalization.orderedExternalZ bits = true := by
    have := orderedExternalZ_true G C hPCard hHCard hZCard
    simpa [bits, L] using this
  have hOrderedH : orderedH bits = true := by
    have := orderedH_true G C hPCard hHCard hZCard
    simpa [bits, L] using this
  have hCommon : commonCoreNoExact bits = true := by
    simpa [bits] using commonCoreNoExact_true G C L hG hPB hMin hNoSeymour
      hRootDegree hk hx hy hNoRoot hHCard m hm (by rfl) hOrderedH
  have hRootZero := edgeCount_P_root_zero G C hNoRoot
  have hRootSum : (∑ p ∈ C.P, epsilonAt G p C.s) = 0 := by
    rw [← edgeCount_singleton G C.P C.s]
    exact hRootZero
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  rw [hRootSum] at hAccounting
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hPHLe : edgeCount G C.P C.H ≤ 42 :=
    (edgeCount_le_card_mul_card G C.P C.H).trans_eq (by
      rw [hPCard, hHCard])
  have hPPLe : edgeCount G C.P C.P ≤ 49 :=
    (edgeCount_le_card_mul_card G C.P C.P).trans_eq (by
      rw [hPCard])
  interval_cases m
  · have hTotal : (totalPToZ bits == 21) = true := by
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [show (totalPToZ bits).toNat = edgeCount G C.P C.Z by
        simpa [bits] using hPZNat, hPZ]
      decide
    have hLower : (35 : BitVec 8).ule
        (totalPToH bits + totalPOut bits) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
        BitVec.toNat_add]
      rw [show (35 : BitVec 8).toNat = 35 by decide,
        show (totalPToH bits).toNat = edgeCount G C.P C.H by
        simpa [bits] using hPHNat,
        show (totalPOut bits).toNat = edgeCount G C.P C.P by
          simpa [bits] using hPPNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    have hExternal :=
      ZThreeLowNormalization.mZeroExternal_of_total bits hTotal
    have hSame : ∀ i : Fin 6,
        directCount G C.Z (L.p ⟨i.val, by omega⟩).1 =
          directCount G C.Z (L.p ⟨i.val + 1, by omega⟩).1 := by
      intro i
      have hAll : ∀ p < 7, pZPattern bits p true true true = true := by
        simpa only [mZeroExternal, ZThreeBridge.all_eq_true_iff] using hExternal
      have hLeft := directZ_eq_three_of_pattern G C L hG i.val (by omega)
        (by simpa [bits] using hAll i.val (by omega))
      have hRight := directZ_eq_three_of_pattern G C L hG (i.val + 1)
        (by omega) (by simpa [bits] using hAll (i.val + 1) (by omega))
      omega
    have hInternalRows : orderedRowsFrom bits 0 6 = true := by
      have := orderedRowsFrom_true G C hG hPB hNoRoot hPCard hHCard hZCard
        0 6 (by omega) (by simpa [L] using hSame)
      simpa [bits, L] using this
    have hCore : mZeroNoExactCore bits = true := by
      simp only [mZeroNoExactCore, Bool.and_eq_true]
      exact ⟨⟨⟨⟨hCommon, hTotal⟩, hLower⟩, hExternal⟩, hInternalRows⟩
    have hUnsat := mZeroNoExact_unsat bits
    rw [hCore] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hTotal : (totalPToZ bits == 20) = true := by
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [show (totalPToZ bits).toNat = edgeCount G C.P C.Z by
        simpa [bits] using hPZNat, hPZ]
      decide
    have hLower : (36 : BitVec 8).ule
        (totalPToH bits + totalPOut bits) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
        BitVec.toNat_add]
      rw [show (36 : BitVec 8).toNat = 36 by decide,
        show (totalPToH bits).toNat = edgeCount G C.P C.H by
        simpa [bits] using hPHNat,
        show (totalPOut bits).toNat = edgeCount G C.P C.P by
          simpa [bits] using hPPNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    have hExternal := ZThreeLowNormalization.mOneExternal_of_ordered bits
      hTotal hRows hZOrder
    have hSame : ∀ i : Fin 5,
        directCount G C.Z (L.p ⟨1 + i.val, by omega⟩).1 =
          directCount G C.Z (L.p ⟨1 + i.val + 1, by omega⟩).1 := by
      intro i
      have hTail : ∀ q < 6,
          pZPattern bits (q + 1) true true true = true := by
        rw [mOneExternal, Bool.and_eq_true] at hExternal
        simpa only [ZThreeBridge.all_eq_true_iff] using hExternal.2
      have hTailLeft : pZPattern bits (1 + i.val) true true true = true := by
        simpa [Nat.add_comm] using hTail i.val (by omega)
      have hLeft := directZ_eq_three_of_pattern G C L hG (1 + i.val)
        (by omega) (by simpa [bits] using hTailLeft)
      have hTailRight :
          pZPattern bits (1 + i.val + 1) true true true = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hTail (i.val + 1) (by omega)
      have hRight := directZ_eq_three_of_pattern G C L hG (1 + i.val + 1)
        (by omega) (by simpa [bits] using hTailRight)
      omega
    have hInternalRows : orderedRowsFrom bits 1 5 = true := by
      have := orderedRowsFrom_true G C hG hPB hNoRoot hPCard hHCard hZCard
        1 5 (by omega) (by simpa [L] using hSame)
      simpa [bits, L] using this
    have hCore : mOneNoExactCore bits = true := by
      simp only [mOneNoExactCore, Bool.and_eq_true]
      exact ⟨⟨⟨⟨hCommon, hTotal⟩, hLower⟩, hExternal⟩, hInternalRows⟩
    have hUnsat := mOneNoExact_unsat bits
    rw [hCore] at hUnsat
    exact Bool.noConfusion hUnsat

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowBridge
