import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.Assembly
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Reduced

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.OrderBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pAOneOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hA1Card : C.A1.card = 3)
    (p : Nat) (hp : p < 6) :
    (count 3 fun a => encodedArc (graphBits G L) (8+p) (1+a)).toNat =
      directCount G C.A1 (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A1 (GraphFacts.aOneLabelEquiv G C L hA1Card) _
  intro i
  rw [GraphFacts.aOneLabelEquiv_val]
  rw [pToA_graphBits G C L hG hzLe p (1+i) hp (by omega)]
  have hFin : (⟨1 + i.val, by omega⟩ : Fin 8) = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    simp only
    omega
  simp [hFin]

theorem pXOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hXCard : C.X.card = 3)
    (p : Nat) (hp : p < 6) :
    (count 3 fun x => encodedArc (graphBits G L) (8+p) (4+x)).toNat =
      directCount G C.X (L.p ⟨p, hp⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.X (GraphFacts.xLabelEquiv G C L hXCard) _
  intro i
  rw [GraphFacts.xLabelEquiv_val]
  rw [pToA_graphBits G C L hG hzLe p (4+i) hp (by omega)]
  have hFin : (⟨4 + i.val, by omega⟩ : Fin 8) = ⟨i.val + 4, by omega⟩ := by
    apply Fin.ext
    simp only
    omega
  simp [hFin]

theorem pQBit_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (p : Nat) (hp : p < 6) :
    (bitCount (encodedArc (graphBits G L) (8+p) 14)).toNat =
      if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0 := by
  rw [bitCount, pToQ_graphBits G C L hG hzLe p hp]
  by_cases h : G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 <;> simp [h]

theorem pDegree_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hHCard : C.H.card = 6) (p : Nat) (hp : p < 6) :
    (pDegree zCount (encodedArc (graphBits G L)) p).toNat =
      directCount G C.P (L.p ⟨p, hp⟩).1 +
        directCount G C.H (L.p ⟨p, hp⟩).1 +
          directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 +
            (if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0) := by
  have hP := pOut_toNat G C L hG hzLe p hp
  have hH := pHOut_toNat G C L hG hzLe hHCard p hp
  have hAux := pAuxOut_toNat G C L hG hzLe p hp
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro v hv
    obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hv⟩
    simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
  have hDis : Disjoint C.Q (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [directCount_union_of_disjoint G C.Q (externalTargets G C) _ hDis, hQ] at hAux
  have hQCount : directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 =
      if G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 then 1 else 0 := by
    simp [Shared.directCount_singleton, Shared.epsilonAt]
  rw [hQCount] at hAux
  have hPLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.P)
  have hHLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.H)
  have hAuxLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) (C.Q ∪ externalTargets G C))
  have hAuxCard : (C.Q ∪ externalTargets G C).card = 1 + zCount := by
      rw [Finset.card_union_of_disjoint hDis]
      have hQC : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
      have hZC : (externalTargets G C).card = zCount := by
        simpa using (Fintype.card_congr L.z).symm
      omega
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  change directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at hPLe
  change directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at hHLe
  change directCount G (C.Q ∪ externalTargets G C) (L.p ⟨p, hp⟩).1 ≤
    (C.Q ∪ externalTargets G C).card at hAuxLe
  rw [hPCard] at hPLe
  rw [hHCard] at hHLe
  rw [directCount_union_of_disjoint G C.Q (externalTargets G C) _ hDis,
    hQ, hQCount] at hAuxLe
  have hAuxCard' : ({(L.q 0).1} ∪ externalTargets G C).card = 1 + zCount := by
    rw [← hQ]
    exact hAuxCard
  rw [hAuxCard'] at hAuxLe
  simp only [pDegree, BitVec.toNat_add]
  rw [hP, hH, hAux]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem packed_order_implies_lex
    (di dj zi zj qi qj ai aj xi xj pi pj : Nat)
    (_hdi : di ≤ 17) (_hdj : dj ≤ 17) (hzi : zi ≤ 5) (hzj : zj ≤ 5)
    (hqi : qi ≤ 1) (hqj : qj ≤ 1) (hai : ai ≤ 3) (haj : aj ≤ 3)
    (hxi : xi ≤ 3) (hxj : xj ≤ 3) (hpi : pi ≤ 15) (hpj : pj ≤ 15)
    (hKey : di * 65536 + zi * 4096 + qi * 2048 + ai * 256 + xi * 16 + pi ≤
      dj * 65536 + zj * 4096 + qj * 2048 + aj * 256 + xj * 16 + pj) :
    di < dj ∨ di = dj ∧
      (zi < zj ∨ zi = zj ∧
        (qi < qj ∨ qi = qj ∧
          (ai < aj ∨ ai = aj ∧ (xi < xj ∨ xi = xj ∧ pi ≤ pj)))) := by
  omega

theorem pLexLe_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hHCard : C.H.card = 6) (hA1Card : C.A1.card = 3)
    (hXCard : C.X.card = 3) (i j : Nat) (hi : i < 6) (hj : j < 6)
    (hOrder : pInvariantKey G C (L.q 0).1 (L.p ⟨i, hi⟩).1 ≤
      pInvariantKey G C (L.q 0).1 (L.p ⟨j, hj⟩).1) :
    pLexLe zCount (encodedArc (graphBits G L)) i j = true := by
  let arc := encodedArc (graphBits G L)
  let di := (pDegree zCount arc i).toNat
  let dj := (pDegree zCount arc j).toNat
  let zi := (pZOut zCount arc i).toNat
  let zj := (pZOut zCount arc j).toNat
  let qi := (bitCount (arc (8+i) 14)).toNat
  let qj := (bitCount (arc (8+j) 14)).toNat
  let ai := (count 3 fun a => arc (8+i) (1+a)).toNat
  let aj := (count 3 fun a => arc (8+j) (1+a)).toNat
  let xi := (count 3 fun x => arc (8+i) (4+x)).toNat
  let xj := (count 3 fun x => arc (8+j) (4+x)).toNat
  let pi := (pOut arc i).toNat
  let pj := (pOut arc j).toNat
  have hDi := pDegree_toNat G C L hG hzLe hHCard i hi
  have hDj := pDegree_toNat G C L hG hzLe hHCard j hj
  have hZi := GraphFacts.pZOut_toNat G C L hG hzLe i hi
  have hZj := GraphFacts.pZOut_toNat G C L hG hzLe j hj
  have hQi := pQBit_toNat G C L hG hzLe i hi
  have hQj := pQBit_toNat G C L hG hzLe j hj
  have hAi := pAOneOut_toNat G C L hG hzLe hA1Card i hi
  have hAj := pAOneOut_toNat G C L hG hzLe hA1Card j hj
  have hXi := pXOut_toNat G C L hG hzLe hXCard i hi
  have hXj := pXOut_toNat G C L hG hzLe hXCard j hj
  have hPi := pOut_toNat G C L hG hzLe i hi
  have hPj := pOut_toNat G C L hG hzLe j hj
  change di = _ at hDi
  change dj = _ at hDj
  change zi = _ at hZi
  change zj = _ at hZj
  change qi = _ at hQi
  change qj = _ at hQj
  change ai = _ at hAi
  change aj = _ at hAj
  change xi = _ at hXi
  change xj = _ at hXj
  change pi = _ at hPi
  change pj = _ at hPj
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hKey : di*65536 + zi*4096 + qi*2048 + ai*256 + xi*16 + pi ≤
      dj*65536 + zj*4096 + qj*2048 + aj*256 + xj*16 + pj := by
    simpa [pInvariantKey, di, dj, zi, zj, qi, qj, ai, aj, xi, xj, pi, pj,
      hDi, hDj, hZi, hZj, hQi, hQj, hAi, hAj, hXi, hXj, hPi, hPj]
      using hOrder
  have hDirectLe (S : Finset V) (v : V) : directCount G S v ≤ S.card := by
    exact Finset.card_le_card (Finset.filter_subset (G.Adj v) S)
  have hDiLe : di ≤ 17 := by
    rw [hDi]
    have hP := hDirectLe C.P (L.p ⟨i, hi⟩).1
    have hH := hDirectLe C.H (L.p ⟨i, hi⟩).1
    have hZ := hDirectLe (externalTargets G C) (L.p ⟨i, hi⟩).1
    rw [hPCard] at hP
    rw [hHCard] at hH
    rw [hZCard] at hZ
    split <;> omega
  have hDjLe : dj ≤ 17 := by
    rw [hDj]
    have hP := hDirectLe C.P (L.p ⟨j, hj⟩).1
    have hH := hDirectLe C.H (L.p ⟨j, hj⟩).1
    have hZ := hDirectLe (externalTargets G C) (L.p ⟨j, hj⟩).1
    rw [hPCard] at hP
    rw [hHCard] at hH
    rw [hZCard] at hZ
    split <;> omega
  have hZiLe : zi ≤ 5 := by
    rw [hZi]
    have h := hDirectLe (externalTargets G C) (L.p ⟨i, hi⟩).1
    rw [hZCard] at h
    omega
  have hZjLe : zj ≤ 5 := by
    rw [hZj]
    have h := hDirectLe (externalTargets G C) (L.p ⟨j, hj⟩).1
    rw [hZCard] at h
    omega
  have hQiLe : qi ≤ 1 := by rw [hQi]; split <;> omega
  have hQjLe : qj ≤ 1 := by rw [hQj]; split <;> omega
  have hAiLe : ai ≤ 3 := by
    rw [hAi]
    have h := hDirectLe C.A1 (L.p ⟨i, hi⟩).1
    omega
  have hAjLe : aj ≤ 3 := by
    rw [hAj]
    have h := hDirectLe C.A1 (L.p ⟨j, hj⟩).1
    omega
  have hXiLe : xi ≤ 3 := by
    rw [hXi]
    have h := hDirectLe C.X (L.p ⟨i, hi⟩).1
    omega
  have hXjLe : xj ≤ 3 := by
    rw [hXj]
    have h := hDirectLe C.X (L.p ⟨j, hj⟩).1
    omega
  have hPiLe : pi ≤ 15 := by
    rw [hPi]
    have h := hDirectLe C.P (L.p ⟨i, hi⟩).1
    omega
  have hPjLe : pj ≤ 15 := by
    rw [hPj]
    have h := hDirectLe C.P (L.p ⟨j, hj⟩).1
    omega
  have hLex := packed_order_implies_lex di dj zi zj qi qj ai aj xi xj pi pj
    hDiLe hDjLe hZiLe hZjLe hQiLe hQjLe hAiLe hAjLe hXiLe hXjLe hPiLe hPjLe
    hKey
  rcases hLex with hD | ⟨hD, hLex⟩
  · change (pDegree zCount arc i).toNat < (pDegree zCount arc j).toNat at hD
    simp [pLexLe, BitVec.ult_eq_decide, arc, hD]
  change (pDegree zCount arc i).toNat = (pDegree zCount arc j).toNat at hD
  have hDEq : pDegree zCount arc i = pDegree zCount arc j :=
    BitVec.eq_of_toNat_eq hD
  rcases hLex with hZ | ⟨hZ, hLex⟩
  · change (pZOut zCount arc i).toNat < (pZOut zCount arc j).toNat at hZ
    simp [pLexLe, BitVec.ult_eq_decide, arc, hDEq, hZ]
  change (pZOut zCount arc i).toNat = (pZOut zCount arc j).toNat at hZ
  have hZEq : pZOut zCount arc i = pZOut zCount arc j := BitVec.eq_of_toNat_eq hZ
  rcases hLex with hQ | ⟨hQ, hLex⟩
  · change (bitCount (arc (8+i) 14)).toNat <
      (bitCount (arc (8+j) 14)).toNat at hQ
    simp [pLexLe, BitVec.ult_eq_decide, arc, hDEq, hZEq, hQ]
  change (bitCount (arc (8+i) 14)).toNat =
    (bitCount (arc (8+j) 14)).toNat at hQ
  have hQEq : bitCount (arc (8+i) 14) = bitCount (arc (8+j) 14) :=
    BitVec.eq_of_toNat_eq hQ
  rcases hLex with hA | ⟨hA, hLex⟩
  · change (count 3 (fun a => arc (8+i) (1+a))).toNat <
      (count 3 (fun a => arc (8+j) (1+a))).toNat at hA
    simp [pLexLe, BitVec.ult_eq_decide, arc, hDEq, hZEq, hQEq, hA]
  change (count 3 (fun a => arc (8+i) (1+a))).toNat =
    (count 3 (fun a => arc (8+j) (1+a))).toNat at hA
  have hAEq : count 3 (fun a => arc (8+i) (1+a)) =
      count 3 (fun a => arc (8+j) (1+a)) := BitVec.eq_of_toNat_eq hA
  rcases hLex with hX | ⟨hX, hP⟩
  · change (count 3 (fun x => arc (8+i) (4+x))).toNat <
      (count 3 (fun x => arc (8+j) (4+x))).toNat at hX
    simp [pLexLe, BitVec.ult_eq_decide, arc, hDEq, hZEq, hQEq,
      hAEq, hX]
  change (count 3 (fun x => arc (8+i) (4+x))).toNat =
    (count 3 (fun x => arc (8+j) (4+x))).toNat at hX
  change (pOut arc i).toNat ≤ (pOut arc j).toNat at hP
  have hXEq : count 3 (fun x => arc (8+i) (4+x)) =
      count 3 (fun x => arc (8+j) (4+x)) := BitVec.eq_of_toNat_eq hX
  simp [pLexLe, BitVec.ule_eq_decide, arc, hDEq, hZEq, hQEq,
    hAEq, hXEq, hP]

theorem zIn_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4) (z : Nat) (hz : z < zCount) :
    (count 6 fun p ↦ encodedArc (graphBits G L) (8 + p) (15 + z)).toNat =
      zInvariantKey G C (L.z ⟨z, hz⟩).1 := by
  rw [toNat_count_eq_fin_sum 6 _ (by omega)]
  unfold zInvariantKey
  rw [edgeCount_eq_sum_fin G C.P {(L.z ⟨z, hz⟩).1} L.p]
  apply Finset.sum_congr rfl
  intro p hp
  rw [GraphFacts.pToZ_graphBits G C L hG hzLe p z p.isLt hz]
  by_cases hAdj : G.Adj (L.p p) (L.z ⟨z, hz⟩) <;>
    simp [directCount, CertificateBridge.internalFirstNeighbors,
      Finset.filter_singleton, hAdj]

theorem reducedOrdered_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels.Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hHCard : C.H.card = 6) (hA1Card : C.A1.card = 3)
    (hXCard : C.X.card = 3)
    (hPOrder : ∀ q : Fin 5,
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1)
    (hAOrder : ∀ q : Fin 2,
      aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 2,
      aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1)
    (hZOrder : ∀ q : Fin (zCount - 1),
      zInvariantKey G C (L.z ⟨q.val + 1, by omega⟩).1 ≤
        zInvariantKey G C (L.z ⟨q.val, by omega⟩).1) :
    reducedOrdered zCount (encodedArc (graphBits G L)) = true := by
  simp only [reducedOrdered, Bool.and_eq_true, all_eq_true_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    exact pLexLe_true G C L hG hzLe hHCard hA1Card hXCard (p+1) p
      (by omega) (by omega) (hPOrder ⟨p, hp⟩)
  · intro a ha
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [aBOut_toNat G C L hG hzLe (a+2) (by omega),
      aBOut_toNat G C L hG hzLe (a+1) (by omega)]
    simpa [aInvariantKey, Nat.add_comm] using hAOrder ⟨a, ha⟩
  · intro x hx
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [aBOut_toNat G C L hG hzLe (x+5) (by omega),
      aBOut_toNat G C L hG hzLe (x+4) (by omega)]
    simpa [aInvariantKey, Nat.add_comm] using hXOrder ⟨x, hx⟩
  · intro z hz
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show 16 + z = 15 + (z + 1) by omega,
      zIn_toNat G C L hG hzLe (z + 1) (by omega),
      zIn_toNat G C L hG hzLe z (by omega)]
    exact hZOrder ⟨z, hz⟩

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.OrderBridge
