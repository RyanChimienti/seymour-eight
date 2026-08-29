import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.UnreachedGraphFacts
import SeymourEight.Cases.BSevenKThree.Counting
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.GraphBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Derived
import SeymourEight.Shared.InnerDegreeThree

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedAssembly

open Shared Shared.FiniteCore Labels UnreachedEncoding Core UnreachedGraphFacts

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem orientedA_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    orientedA (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true]
  constructor
  · rw [aArc_graphBits G C L hG hzLe i i hi hi]
    simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [aArc_graphBits G C L hG hzLe i j hi hj,
      aArc_graphBits G C L hG hzLe j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    by_cases ha : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
    · simp [hij, ha, hG.2 ha]
    · simp [hij, ha]

theorem orientedP_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    orientedP (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [pArc_graphBits G C L hG hzLe i j hi hj,
    pArc_graphBits G C L hG hzLe j i hj hi]
  by_cases hij : i = j
  · simp [hij]
  by_cases ha : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
  · simp [hij, ha, hG.2 ha]
  · simp [hij, ha]

theorem orientedAPQ_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    orientedAPQ (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  simp only [orientedAPQ, Bool.and_eq_true, all_eq_true_iff]
  constructor
  · constructor
    · intro a ha p hp
      rw [aToP_graphBits G C L hG hzLe a p ha hp,
        pToA_graphBits G C L hG hzLe p a hp ha]
      by_cases h : G.Adj (L.a ⟨a, ha⟩).1 (L.p ⟨p, hp⟩).1
      · simp [h, hG.2 h]
      · simp [h]
    · intro a ha
      rw [aToQ_graphBits G C L hG hzLe a ha]
      rw [show UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L) 14 a = false by simp [UnreachedCore.encodedArc]]
      simp
  · intro p hp
    rw [pToQ_graphBits G C L hG hzLe p hp]
    rw [show UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L) 14 (8+p) = false by simp [UnreachedCore.encodedArc]]
    simp

theorem fixedPivot_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (_hG : G.IsOriented) (_hzLe : zCount ≤ 5) :
    fixedPivot (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  simp [fixedPivot, all, UnreachedCore.encodedArc]

theorem everyXReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (hA1Card : C.A1.card = 3) :
    everyXReached (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    have e : Fin 3 ≃ {v : V // v ∈ C.A1} := by
      exact finsetEquivFin C.A1 hA1Card
    obtain ⟨i, hi⟩ := e.surjective ⟨u, huA1⟩
    obtain ⟨j, hj⟩ := L.a.surjective ⟨u,
      Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1⟩
    have hjRange : 1 ≤ j.val ∧ j.val ≤ 3 := by
      have hjAdj : G.Adj C.a1 (L.a j).1 := by
        rw [congrArg Subtype.val hj]
        exact (Finset.mem_filter.mp huA1).2
      by_contra hn
      have hfixed := fixedPivot_true G C L hG hzLe
      rw [fixedPivot, all_eq_true_iff] at hfixed
      have := hfixed j.val (by omega)
      rw [aArc_graphBits G C L hG hzLe 0 j (by omega) j.isLt] at this
      simp [L.a_zero, hjAdj, hn] at this
      omega
    refine ⟨j.val - 1, by omega, ?_⟩
    rw [aArc_graphBits G C L hG hzLe (1+(j.val-1)) (4+x)
      (by omega) (by omega)]
    have hxFin : (⟨4+x, by omega⟩ : Fin 8) = ⟨x+4, by omega⟩ :=
      Fin.ext (by simp; omega)
    simpa [show 1 + (j.val-1)=j.val by omega, hxFin,
      congrArg Subtype.val hj] using decide_eq_true hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [pToA_graphBits G C L hG hzLe i (4+x) i.isLt (by omega)]
    have hxFin : (⟨4+x, by omega⟩ : Fin 8) = ⟨x+4, by omega⟩ :=
      Fin.ext (by simp; omega)
    simpa [hxFin, congrArg Subtype.val hi] using decide_eq_true hux

theorem rUnreached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    rUnreached (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  simp only [rUnreached, Bool.and_eq_true, all_eq_true_iff]
  constructor
  · intro a ha
    rw [aArc_graphBits G C L hG hzLe (1+a) 7 (by omega) (by omega)]
    have heq : (⟨1+a, by omega⟩ : Fin 8) = ⟨a+1, by omega⟩ :=
      Fin.ext (by simp; omega)
    have hn := BSixKThreeCoreGraphBridge.A1_not_adj_R G C hG
      (L.a ⟨1+a, by omega⟩).1 (L.a 7).1 (by simpa [heq] using L.a_aOne ⟨a, ha⟩) L.a_r
    simp [hn]
  · intro p hp
    rw [pToA_graphBits G C L hG hzLe p 7 hp (by omega)]
    have hn := BSixKThreeCoreGraphBridge.P_not_adj_R G C
      (L.p ⟨p, hp⟩).1 (L.a 7).1 (L.p _).2 L.a_r
    simp [hn]

theorem qUnreached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (hy : BSevenKThree.y G C = 0) :
    UnreachedCore.qUnreached
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  change (reachedQ G C).card = 0 at hy
  have hEmpty : reachedQ G C = ∅ := Finset.card_eq_zero.mp hy
  simp only [UnreachedCore.qUnreached, Bool.and_eq_true, all_eq_true_iff]
  constructor
  · intro a ha
    rw [aToQ_graphBits G C L hG hzLe (1+a) (by omega)]
    have hn : ¬G.Adj (L.a ⟨1+a, by omega⟩).1 (L.q 0).1 := by
      intro hadj
      have hm : (L.q 0).1 ∈ reachedQ G C := by
        rw [reachedQ, Finset.mem_inter]
        exact ⟨(L.q 0).2, (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨(L.a ⟨1+a, by omega⟩).1,
            Finset.mem_union_left _ (by
              simpa [Nat.add_comm] using L.a_aOne ⟨a, ha⟩), hadj⟩⟩
      simp [hEmpty] at hm
    simp [hn]
  · intro p hp
    rw [pToQ_graphBits G C L hG hzLe p hp]
    have hn : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 := by
      intro hadj
      have hm : (L.q 0).1 ∈ reachedQ G C := by
        rw [reachedQ, Finset.mem_inter]
        exact ⟨(L.q 0).2, (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨(L.p ⟨p, hp⟩).1,
            Finset.mem_union_right _ (L.p ⟨p, hp⟩).2, hadj⟩⟩
      simp [hEmpty] at hm
    simp [hn]

theorem allZReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    allZReached zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  obtain ⟨p, hp, hpz⟩ : ∃ p ∈ C.P, G.Adj p (L.z ⟨z, hz⟩).1 := by
    rcases Finset.mem_union.mp (L.z ⟨z, hz⟩).2 with hvZ | hvRoot
    · exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp (Finset.mem_sdiff.mp hvZ).1
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : (L.z ⟨z, hz⟩).1 = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        simpa [hvs] using hReach
      · simp [rootSecondFinset, hReach] at hvRoot
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pToZ_graphBits G C L hG hzLe i z i.isLt hz]
  simpa [congrArg Subtype.val hi] using decide_eq_true hpz

theorem A_outdegree_eq_A_add_B (C : G.LocalConfiguration)
    (hG : G.IsOriented) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = Shared.directCount G C.A u + Shared.directCount G C.B u := by
  have hAB := Digraph.LocalConfiguration.disjoint_A_B (G := G) C
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG u hu
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.B) u hCap
  rw [directCount_union_of_disjoint G C.A C.B u hAB] at hEq
  exact hEq

theorem aMinimumAndPivot_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hr : C.r = 6) :
    aMinimumAndPivot (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [aMinimumAndPivot, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L hG hzLe a ha
  have hBO := aBOut_toNat G C L hG hzLe a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 3 ≤ (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat = 3 →
      6 ≤ (aBOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat := by
    intro heq
    rw [hBO]
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change Shared.directCount G C.A (L.a ⟨a, ha⟩).1 = 3
      rw [← hAO]
      exact heq
    have hTieB := hPivotA.2 hCardEq
    change C.r ≤ Shared.directCount G C.B (L.a ⟨a, ha⟩).1 at hTieB
    simpa [hr] using hTieB
  have hTotal : 8 ≤ (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat +
      (aBOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat := by
    rw [hAO, hBO, ← A_outdegree_eq_A_add_B G C hG _ (L.a _).2]
    exact hMin _
  have hSmall : (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat +
      (aBOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat < 256 := by
    rw [hAO, hBO]
    have hALe : Shared.directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hBLe : Shared.directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hcA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hcB : C.B.card = 7 := by
      have hCard := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
      have hQ : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
      omega
    omega
  simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
  refine ⟨⟨hAmin, ?_⟩, ?_⟩
  · rw [Bool.or_eq_true]
    by_cases heq : aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a = 3
    · right
      simpa [BitVec.ule_eq_decide] using hTie (congrArg BitVec.toNat heq)
    · left
      simpa using heq
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt hSmall]
    exact hTotal

theorem aNonSeymour_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    aNonSeymour zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [aNonSeymour, all_eq_true_iff]
  intro a ha
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSecond := secondCount_le_graph G C L hG hzLe a ha
  have hAO := aOut_toNat G C L hG hzLe a ha
  have hBO := aBOut_toNat G C L hG hzLe a ha
  have hSmall : (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat +
      (aBOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat < 256 := by
    rw [hAO, hBO]
    have hALe : Shared.directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hBLe : Shared.directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hcA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hcB : C.B.card = 7 := by
      rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
        Finset.card_union_of_disjoint
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
      have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
      have hq : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
      omega
    omega
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt hSmall, hAO, hBO,
    ← A_outdegree_eq_A_add_B G C hG _ (L.a _).2]
  exact hSecond.trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨(L.a ⟨a, ha⟩).1, h⟩))

theorem pMinimum_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (hHCard : C.H.card = 6) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    pMinimum zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [pMinimum, all_eq_true_iff]
  intro p hp
  have hP := pOut_toNat G C L hG hzLe p hp
  have hH := pHOut_toNat G C L hG hzLe hHCard p hp
  have hAux := pAuxOut_toNat G C L hG hzLe p hp
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro v hv
    obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hv⟩
    simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
  have hDegree :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG (L.p ⟨p, hp⟩).1 (L.p _).2
  rw [← hQ] at hDegree
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pDegree, BitVec.toNat_add, BitVec.toNat_add, hP, hH, hAux]
  have hPLe : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.p).symm)
  have hHLe : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hAuxLe : Shared.directCount G (C.Q ∪ externalTargets G C)
      (L.p ⟨p, hp⟩).1 ≤ 1 + zCount := by
    apply (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    have hDis : Disjoint C.Q (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvQ hvE
      rcases Finset.mem_union.mp hvE with hvZ | hvRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
            (Finset.mem_union_right _
              (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ))
      · by_cases hr : ∃ u ∈ C.P, G.Adj u C.s
        · have hvs : v = C.s := by simpa [rootSecondFinset, hr] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_B (G := G) C
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
        · simp [rootSecondFinset, hr] at hvRoot
    rw [Finset.card_union_of_disjoint hDis]
    have hQC : C.Q.card = 1 := by
      simpa using (Fintype.card_congr L.q).symm
    have hZC : (externalTargets G C).card = zCount := by
      simpa using (Fintype.card_congr L.z).symm
    omega
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [← hDegree]
  simpa using hMin (L.p ⟨p, hp⟩).1

theorem degreeThreeConsequences_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hOriented : orientedA (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true)
    (hMinimum : ∀ a < 8,
      (3 : BitVec 8).ule (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a) = true) :
    degreeThreeClassification (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true ∧
      threeInnerWitnesses (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  let arc := UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)
  have hOr : InnerDegreeThree.oriented arc = true := by
    simpa [arc, InnerDegreeThree.oriented, orientedA] using hOriented
  have hMin : InnerDegreeThree.minimumThree arc = true := by
    rw [InnerDegreeThree.minimumThree, all_eq_true_iff]
    intro a ha
    simpa [arc, InnerDegreeThree.outCount, aOut] using hMinimum a ha
  exact ⟨InnerDegreeThree.classification_of arc hOr hMin,
    InnerDegreeThree.threeWitnesses_of arc hOr hMin⟩

theorem sharpKing_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hOriented :
      orientedP (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true) :
    sharpKing (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  apply Core.sharpKing_of_orientedP _ hOriented
  rw [all_eq_true_iff]
  intro p hp
  simp [UnreachedCore.encodedArc, show 8 + p < 14 by omega]

theorem hallCondition_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 8 (hallCondition zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L))) = true := by
  rw [all_eq_true_iff]
  intro a ha
  unfold hallCondition
  by_cases hInner : innerSeymour (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a = true
  · by_cases hAQ : UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L) a 14 = true
    · simp [hInner, hAQ]
    · have hAQFalse := Bool.eq_false_of_not_eq_true hAQ
      rw [hInner, hAQFalse]
      simp only [Bool.not_true, Bool.false_or,
        Bool.and_eq_true]
      let v := (L.a ⟨a, ha⟩).1
      let S := CertificateBridge.internalFirstNeighbors G C.P v
      let T := CertificateBridge.internalSecondNeighbors (G := G) C.A v
      let U := hallTargets G C v
      have hAO := aOut_toNat G C L hG hzLe a ha
      have hSO := aPOut_toNat G C L hG hzLe a ha
      have hTO := innerSecondCount_toNat G C L hG hzLe a ha
      have hUO := hallCount_le_card G C L hG hzLe a ha
      have hInnerNat : (aOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat ≤
          (innerSecondCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) a).toNat := by
        unfold innerSeymour at hInner
        simpa [BitVec.ule_eq_decide] using hInner
      have hNotQ : ¬G.Adj v (L.q 0).1 := by
        have hh := hAQFalse
        rw [aToQ_graphBits G C L hG hzLe a ha] at hh
        simpa [v] using hh
      have hQ : C.Q = {(L.q 0).1} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨(L.q 0).2, ?_⟩
        intro w hw
        obtain ⟨i, hi⟩ := L.q.surjective ⟨w, hw⟩
        simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
      have hOutEq : G.outdegree v = S.card + Shared.directCount G C.A v := by
        have hAB := A_outdegree_eq_A_add_B G C hG v (L.a ⟨a, ha⟩).2
        have hPQ := directCount_union_of_disjoint G C.P C.Q v
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)
        rw [Digraph.LocalConfiguration.P_union_Q (G := G) C] at hPQ
        have hQZero : Shared.directCount G C.Q v = 0 := by
          rw [hQ]
          simp [Shared.directCount_singleton, Shared.epsilonAt, hNotQ]
        rw [hQZero, Nat.add_zero] at hPQ
        rw [hPQ] at hAB
        dsimp [S, CertificateBridge.internalFirstNeighbors,
          Shared.directCount] at hAB ⊢
        omega
      have hALe : Shared.directCount G C.A v ≤ 7 := by
        have hSub : C.A.filter (G.Adj v) ⊆ C.A.erase v := by
          intro w hw
          rcases Finset.mem_filter.mp hw with ⟨hwA, hvw⟩
          exact Finset.mem_erase.mpr
            ⟨fun heq ↦ hG.1 v (heq ▸ hvw), hwA⟩
        have hCard := Finset.card_le_card hSub
        have hACard : C.A.card = 8 := by
          simpa using (Fintype.card_congr L.a).symm
        rw [Finset.card_erase_of_mem (L.a ⟨a, ha⟩).2, hACard] at hCard
        exact hCard
      have hSPos : 1 ≤ S.card := by
        have hvMin := hMin v
        omega
      have hTSub : T ⊆ G.secondOutNeighborFinset v := by
        intro w hw
        rcases Finset.mem_filter.mp hw with
          ⟨_, hNot, hwv, middle, _, hFirst, hLast⟩
        rw [Digraph.mem_secondOutNeighborFinset,
          Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨middle, hFirst, hLast⟩, hNot, hwv⟩
      have hUSub : U ⊆ G.secondOutNeighborFinset v := by
        intro e he
        rcases Finset.mem_filter.mp he with
          ⟨heAux, p, hpP, hFirst, hLast⟩
        have hNot : ¬G.Adj v e := by
          rcases Finset.mem_union.mp heAux with heQ | heExt
          · rw [hQ] at heQ
            simpa [Finset.mem_singleton.mp heQ] using hNotQ
          · exact A_not_adj_external G C hG v e (L.a ⟨a, ha⟩).2 heExt
        have hne : e ≠ v := by
          intro heq
          subst e
          rcases Finset.mem_union.mp heAux with heQ | heExt
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
                (L.a ⟨a, ha⟩).2
                (Digraph.LocalConfiguration.Q_subset_B (G := G) C heQ)
          · rcases Finset.mem_union.mp heExt with heZ | heRoot
            · exact (Finset.disjoint_left.mp
                (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) heZ
                  (Finset.mem_union_left C.B
                    (Finset.mem_union_right {C.s} (L.a ⟨a, ha⟩).2))
            · by_cases hr : ∃ p ∈ C.P, G.Adj p C.s
              · have : v = C.s := by simpa [rootSecondFinset, hr] using heRoot
                have hvA := (L.a ⟨a, ha⟩).2
                change v ∈ C.A at hvA
                rw [this] at hvA
                exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
                  hvA
              · simp [rootSecondFinset, hr] at heRoot
        rw [Digraph.mem_secondOutNeighborFinset,
          Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨p, hFirst, hLast⟩, hNot, hne⟩
      have hDisjoint : Disjoint T U := by
        rw [Finset.disjoint_left]
        intro w hwT hwU
        have hwA := (Finset.mem_filter.mp hwT).1
        have hwAux := (Finset.mem_filter.mp hwU).1
        rcases Finset.mem_union.mp hwAux with hwQ | hwExt
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hwA
              (Digraph.LocalConfiguration.Q_subset_B (G := G) C hwQ)
        · rcases Finset.mem_union.mp hwExt with hwZ | hwRoot
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
                (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hwA))
          · by_cases hr : ∃ p ∈ C.P, G.Adj p C.s
            · have : w = C.s := by simpa [rootSecondFinset, hr] using hwRoot
              subst w
              exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hwA
            · simp [rootSecondFinset, hr] at hwRoot
      have hSecondLower : T.card + U.card ≤ G.secondOutdegree v := by
        rw [← Finset.card_union_of_disjoint hDisjoint]
        unfold Digraph.secondOutdegree
        exact Finset.card_le_card (Finset.union_subset hTSub hUSub)
      have hStrict : U.card < S.card := by
        by_contra hn
        have hUS : S.card ≤ U.card := by omega
        have hTA : Shared.directCount G C.A v ≤ T.card := by
          dsimp [T, v]
          rw [← hTO, ← hAO]
          exact hInnerNat
        have hSecondStrict :=
          Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
            (fun hs ↦ hNoSeymour ⟨v, hs⟩)
        omega
      constructor
      · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
        rw [hSO]
        simpa [S, Shared.directCount,
          CertificateBridge.internalFirstNeighbors] using hSPos
      · simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
        rw [hSO]
        have hCountStrict := hUO.trans_lt hStrict
        simpa [S, U, Shared.directCount,
          CertificateBridge.internalFirstNeighbors] using hCountStrict
  · have hf := Bool.eq_false_of_not_eq_true hInner
    simp [hf]

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedAssembly
