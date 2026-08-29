import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.GraphFacts
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Structure
import SeymourEight.Certificates.BSevenKThree.RSeven.XTwo.Five
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.FiveBridge

open Shared Shared.FiniteCore Labels GraphFacts
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot
open XThreeNoRoot.Encoding XThreeNoRoot.ExpansionCore
open XTwoNoRoot.Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem orientedA_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) : XThreeNoRoot.Core.orientedA (graphBits G L) = true := by
  rw [XThreeNoRoot.Core.orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true]
  constructor
  · rw [aArc_graphBits G C L hG (by omega) i i hi hi]
    simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [aArc_graphBits G C L hG (by omega) i j hi hj,
      aArc_graphBits G C L hG (by omega) j i hj hi]
    by_cases heq : i = j
    · simp [heq]
    by_cases hadj : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
    · simp [heq, hadj, hG.2 hadj]
    · simp [heq, hadj]

theorem orientedP_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) : XThreeNoRoot.Core.orientedP (graphBits G L) = true := by
  rw [XThreeNoRoot.Core.orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [pArc_coreBits G.Adj _ _ _ i j hi hj,
    pArc_coreBits G.Adj _ _ _ j i hj hi]
  by_cases heq : i = j
  · simp [heq]
  by_cases hadj : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
  · simp [heq, hadj, hG.2 hadj]
  · simp [heq, hadj]

theorem orientedPH_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) : XThreeNoRoot.Core.orientedPH (graphBits G L) = true := by
  rw [XThreeNoRoot.Core.orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  rw [pToH_coreBits G.Adj _ _ _ p h hp hh,
    hToP_coreBits G.Adj _ _ _ h p hh hp]
  by_cases hadj : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1
  · simp [hadj, hG.2 hadj]
  · simp [hadj]

theorem everyXReached_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hA1Card : C.A1.card = 3) : everyXReached (graphBits G L) = true := by
  rw [everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := (aOneLabelEquiv G C L hA1Card).surjective ⟨u, huA1⟩
    refine ⟨i, i.isLt, ?_⟩
    have hsEq : 1 + i.val = i.val + 1 := by omega
    have htEq : 4 + x = 3 + x + 1 := by omega
    conv_lhs => rw [hsEq, htEq]
    rw [hArc_coreBits G.Adj _ _ _ i (3 + x) (by omega) (by omega)]
    rw [decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := by
      simpa [aOneLabelEquiv_val] using congrArg Subtype.val hi
    rw [hiVal]
    have hDest : (L.a ⟨3 + x + 1, by omega⟩).1 =
        (L.a ⟨x + 4, by omega⟩).1 := by
      congr 2
      apply Fin.ext
      change 3 + x + 1 = x + 4
      omega
    rw [hDest]
    exact hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨pi, hpi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨pi, pi.isLt, ?_⟩
    rw [pToH_coreBits G.Adj _ _ _ pi (3 + x) pi.isLt (by omega)]
    have hDest : (L.a ⟨3 + x + 1, by omega⟩).1 =
        (L.a ⟨x + 4, by omega⟩).1 := by
      congr 2
      apply Fin.ext
      change 3 + x + 1 = x + 4
      omega
    rw [hDest]
    simpa [congrArg Subtype.val hpi] using hux

theorem rUnreached_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) : rUnreached (graphBits G L) = true := by
  rw [rUnreached, Bool.and_eq_true]
  constructor
  · rw [all_eq_true_iff]
    intro a ha
    rw [all_eq_true_iff]
    intro r hr
    have haAdd : 1 + a = a + 1 := by omega
    have hrAdd : 6 + r = 5 + r + 1 := by omega
    rw [haAdd, hrAdd]
    rw [hArc_coreBits G.Adj _ _ _ a (5 + r) (by omega) (by omega)]
    have hn := BSixKThreeCoreGraphBridge.A1_not_adj_R G C hG
      (L.a ⟨a + 1, by omega⟩).1 (L.a ⟨r + 6, by omega⟩).1
      (L.a_aOne ⟨a, ha⟩) (L.a_r ⟨r, hr⟩)
    have hn' : ¬G.Adj (L.a ⟨a + 1, by omega⟩).1
        (L.a ⟨5 + r + 1, by omega⟩).1 := by
      simpa only [show 5 + r + 1 = r + 6 by omega] using hn
    simp [hn']
  · rw [all_eq_true_iff]
    intro p hp
    rw [all_eq_true_iff]
    intro r hr
    have hrAdd : 5 + r + 1 = r + 6 := by omega
    rw [pToH_coreBits G.Adj _ _ _ p (5 + r) hp (by omega)]
    have hn := BSixKThreeCoreGraphBridge.P_not_adj_R G C
      (L.p ⟨p, hp⟩).1 (L.a ⟨r + 6, by omega⟩).1
      (L.p ⟨p, hp⟩).2 (L.a_r ⟨r, hr⟩)
    simpa [hrAdd] using decide_eq_false hn

theorem allZReached_true (C : G.LocalConfiguration) (L : Labels G 5 C) :
    XThreeNoRoot.Core.allZReached 5 (graphBits G L) = true := by
  rw [XThreeNoRoot.Core.allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := (L.z ⟨z, hz⟩).2
  have hReached : (L.z ⟨z, hz⟩).1 ∈ G.outNeighborFinsetOf C.P := by
    rcases Finset.mem_union.mp hzMem with hzZ | hzRoot
    · exact (Finset.mem_sdiff.mp hzZ).1
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hzs : (L.z ⟨z, hz⟩).1 = C.s := by
          simpa [rootSecondFinset, hReach] using hzRoot
        rw [hzs]
        exact (Digraph.mem_outNeighborFinsetOf (G := G)).mpr hReach
      · simp [rootSecondFinset, hReach] at hzRoot
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReached with ⟨p, hp, hpz⟩
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt (by omega) hz]
  simpa [congrArg Subtype.val hi] using hpz

theorem aMinimumAndDegree_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) :
    XThreeNoRoot.Core.aMinimumAndDegree (graphBits G L) = true := by
  rw [XThreeNoRoot.Core.aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L hG (by omega) a ha
  have hPO := aPOut_toNat G C L hG (by omega) a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 3 ≤ (XThreeNoRoot.Core.aOut (graphBits G L) a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount, CertificateBridge.internalFirstNeighbors]
      using hPivotA.1
  have hTie : (XThreeNoRoot.Core.aOut (graphBits G L) a).toNat = 3 →
      7 ≤ (XThreeNoRoot.Core.aPOut (graphBits G L) a).toNat := by
    intro heq
    rw [hPO]
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change Shared.directCount G C.A (L.a ⟨a, ha⟩).1 = 3
      rw [← hAO]
      exact heq
    have hTieB := hPivotA.2 hCardEq
    change C.r ≤ Shared.directCount G C.B (L.a ⟨a, ha⟩).1 at hTieB
    rw [← hPB] at hTieB
    have hr : C.r = 7 := by
      change C.P.card = 7
      simpa using (Fintype.card_congr L.p).symm
    simpa [hr] using hTieB
  have hTotal : 8 ≤ (XThreeNoRoot.Core.aOut (graphBits G L) a).toNat +
      (XThreeNoRoot.Core.aPOut (graphBits G L) a).toNat := by
    rw [hAO, hPO, ← GraphFacts.A_outdegree_eq_A_add_P
      G C hG hPB _ (L.a _).2]
    exact hMin _
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simpa [BitVec.ule_eq_decide] using hAmin
    · rw [Bool.or_eq_true]
      by_cases heq : XThreeNoRoot.Core.aOut (graphBits G L) a = 3
      · right
        simpa [BitVec.ule_eq_decide] using hTie (congrArg BitVec.toNat heq)
      · left
        simpa using heq
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [BitVec.toNat_add]
    have hSmall : (XThreeNoRoot.Core.aOut (graphBits G L) a).toNat +
        (XThreeNoRoot.Core.aPOut (graphBits G L) a).toNat < 256 := by
      have hA : Shared.directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hP : Shared.directCount G C.P (L.a ⟨a, ha⟩).1 ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [hAO, hPO]
      have hcA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
      have hcP : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
      omega
    rw [Nat.mod_eq_of_lt hSmall]
    exact hTotal

theorem pMinimumDegree_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hHCard : C.H.card = 5)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    pMinimumDegree 5 (graphBits G L) = true := by
  rw [pMinimumDegree, all_eq_true_iff]
  intro p hp
  have hDegree : G.outdegree (L.p ⟨p, hp⟩).1 =
      Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.P (L.p ⟨p, hp⟩).1 := by
    have h := SeymourEight.BSixKTwoCoreGraphBridge.outdegree_P_eq_blocks
      G C hG hPB (L.p ⟨p, hp⟩).1 (L.p _).2
    have hHCount : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 =
        Shared.directCount G C.A1 (L.p ⟨p, hp⟩).1 +
          Shared.directCount G C.X (L.p ⟨p, hp⟩).1 :=
      directCount_union_of_disjoint G C.A1 C.X _
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
    omega
  have hP := pOut_toNat G C L hG p hp
  have hH := pHOut_toNat G C L hG hHCard p hp
  have hZ := pZOut_toNat G C L (by omega) p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have hSmall : (XThreeNoRoot.Core.pOut (graphBits G L) p).toNat +
      (XTwoNoRoot.Core.pHOut (graphBits G L) p).toNat < 256 := by
    rw [hP, hH]
    have hpC : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hpLe : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hhLe : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  rw [Nat.mod_eq_of_lt hSmall]
  have hSmall' : (XThreeNoRoot.Core.pOut (graphBits G L) p).toNat +
      (XTwoNoRoot.Core.pHOut (graphBits G L) p).toNat +
      (XThreeNoRoot.Core.pZOut 5 (graphBits G L) p).toNat < 256 := by
    rw [hP, hH, hZ]
    have hpC : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hzC : (externalTargets G C).card = 5 := by
      simpa using (Fintype.card_congr L.z).symm
    have hpLe : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hhLe : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hzLe : Shared.directCount G (externalTargets G C)
        (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  rw [Nat.mod_eq_of_lt hSmall']
  have hNatural : 8 ≤ (XThreeNoRoot.Core.pOut (graphBits G L) p).toNat +
      (XTwoNoRoot.Core.pHOut (graphBits G L) p).toNat +
      (XThreeNoRoot.Core.pZOut 5 (graphBits G L) p).toNat := by
    rw [hP, hH, hZ]
    have hDegreeLower := hMin (L.p ⟨p, hp⟩).1
    omega
  exact hNatural

theorem pUnionExpansion_true (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (C : G.LocalConfiguration) (L : Labels G 5 C) (hG : G.IsOriented)
    (hPB : C.P = C.B) (hNoSeymour : ¬G.HasSeymourVertex) :
    pUnionExpansion 5 (graphBits G L) = true := by
  let E := G.outNeighborFinsetOf C.P \ (C.P ∪ {C.a1})
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hPSubset : (C.P : Set V) ⊆ G.outNeighborSet C.a1 := fun _ hp ↦
    (Finset.mem_filter.mp hp).2
  have hExpansion : 7 ≤ E.card := by
    simpa [E, hPCard] using
      Digraph.oneVertexReduction G hBound hG hNoSeymour hPSubset (by omega)
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp (Finset.mem_sdiff.mp hv).1
    exact XThreeNoRoot.GraphFacts.P_outgoingCaptured_retained G C hG hPB p hp
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
  have hCount : E.card ≤
      (count 20 (pUnionTarget 5 (graphBits G L))).toNat := by
    have hFilter := XThreeNoRoot.GraphFacts.filterCard_le_count (V := V)
      (retainedVertexSet G C) (retainedLabelEquiv G C L hG)
      (pUnionTarget 5 (graphBits G L)) (fun v ↦ v ∈ E) (by omega) (by
        intro target htE
        have htE' : labelledVertex G L target.val ∈ E := by
          rw [retainedLabelEquiv_val G C L hG] at htE
          exact htE
        have htNot : labelledVertex G L target.val ∉ C.P ∪ {C.a1} :=
          (Finset.mem_sdiff.mp htE').2
        have htZero : target.val ≠ 0 := by
          intro ht
          have htFin : target = 0 := Fin.ext ht
          subst target
          exact htNot (Finset.mem_union_right C.P (by simp [labelledVertex, L.a_zero]))
        have htClass : target.val < 8 ∨ 15 ≤ target.val := by
          by_contra h
          have htP : labelledVertex G L target.val ∈ C.P := by
            simp only [not_or, not_le] at h
            simp [labelledVertex, show ¬target.val < 8 by omega,
              show target.val < 15 by omega, (L.p ⟨target.val - 8, by omega⟩).2]
          exact htNot (Finset.mem_union_left _ htP)
        obtain ⟨p, hp, hpv⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp
            (Finset.mem_sdiff.mp htE').1
        obtain ⟨pi, hpi⟩ := L.p.surjective ⟨p, hp⟩
        rw [pUnionTarget, Bool.and_eq_true]
        refine ⟨by simp [htZero, htClass], ?_⟩
        rw [any_eq_true_iff]
        refine ⟨pi, pi.isLt, ?_⟩
        rw [coreArc_graphBits G C L hG (by omega) (8 + pi.val) target.val
          (by omega) target.isLt]
        simpa [labelledVertex, show ¬8 + pi.val < 8 by omega,
          show 8 + pi.val < 15 by omega, congrArg Subtype.val hpi] using hpv)
    have hFilterEq :
        ((retainedVertexSet G C).filter fun v ↦ v ∈ E).card = E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hv ↦ ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    exact hFilter
  unfold pUnionExpansion
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  norm_num [BitVec.toNat_ofNat]
  exact hExpansion.trans hCount

theorem contradiction (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (C : G.LocalConfiguration) (L : Labels G 5 C) (hG : G.IsOriented)
    (hPB : C.P = C.B) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hk : C.k = 3)
    (hHCard : C.H.card = 5) (hA1Card : C.A1.card = 3)
    (hNoSeymour : ¬G.HasSeymourVertex) : False := by
  have hCore : XTwoNoRoot.Core.core 5 (graphBits G L) = true := by
    have hOrA := orientedA_true G C L hG
    have hOrP := orientedP_true G C L hG
    have hOrPH := orientedPH_true G C L hG
    have hX := everyXReached_true G C L hA1Card
    have hR := rUnreached_true G C L hG
    have hZ := allZReached_true G C L
    have hAMin := aMinimumAndDegree_true G C L hG hPB hPivot hMin hk
    have hANon : all 2 (fun x ↦ XThreeNoRoot.Core.aNonSeymour 5
        (graphBits G L) (4 + x)) = true := by
      rw [all_eq_true_iff]
      intro x hx
      exact nonSeymour_graphBits_true G C L hG (by omega) hPB hNoSeymour
        (4 + x) (by omega)
    have hPMin := pMinimumDegree_true G C L hG hPB hHCard hMin
    have hExpand := pUnionExpansion_true G hBound C L hG hPB hNoSeymour
    simp only [XTwoNoRoot.Core.core, XTwoNoRoot.Core.structuralCore,
      hOrA, hOrP, hOrPH, hX, hR, hZ, hAMin, hANon, hPMin, hExpand,
      Bool.and_self]
  have := congrArg Bool.not (five_unsat (graphBits G L))
  simp [hCore] at this

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.FiveBridge
