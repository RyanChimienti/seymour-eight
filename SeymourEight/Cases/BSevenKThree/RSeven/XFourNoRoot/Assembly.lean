import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.GraphFacts
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.Capacity
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.SharpKing
import SeymourEight.Cases.BSevenKThree.Counting
import SeymourEight.Shared.InnerDegreeThree
import SeymourEight.Shared.AlmostTournamentKing
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.BroadFourAssembly
import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Assembly

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem orientedA_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    orientedA (graphBits G L) = true := by
  rw [orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true]
  have hii := coreArc_graphBits G C L hG hzLe i i (by omega) (by omega)
  have hArcII : aArc (graphBits G L) i i =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨i, hi⟩).1) := by
    simpa [Core.coreArc, hi, labelledVertex] using hii
  constructor
  · rw [hArcII]
    simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    have hij := coreArc_graphBits G C L hG hzLe i j (by omega) (by omega)
    have hji := coreArc_graphBits G C L hG hzLe j i (by omega) (by omega)
    have hArcIJ : aArc (graphBits G L) i j =
        decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
      simpa [Core.coreArc, hi, hj, labelledVertex] using hij
    have hArcJI : aArc (graphBits G L) j i =
        decide (G.Adj (L.a ⟨j, hj⟩).1 (L.a ⟨i, hi⟩).1) := by
      simpa [Core.coreArc, hi, hj, labelledVertex] using hji
    rw [hArcIJ, hArcJI]
    by_cases heq : i = j
    · simp [heq]
    by_cases hadj : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
    · simp [heq, hadj, hG.2 hadj]
    · simp [heq, hadj]

theorem orientedP_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) : orientedP (graphBits G L) = true := by
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pArc_coreBits
      G.Adj _ _ _ i j hi hj,
    SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pArc_coreBits
      G.Adj _ _ _ j i hj hi]
  by_cases heq : i = j
  · simp [heq]
  by_cases hadj : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
  · simp [heq, hadj, hG.2 hadj]
  · simp [heq, hadj]

theorem orientedPH_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) : orientedPH (graphBits G L) = true := by
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToH_coreBits
      G.Adj _ _ _ p h hp hh,
    SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.hToP_coreBits
      G.Adj _ _ _ h p hh hp]
  by_cases hadj : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1
  · simp [hadj, hG.2 hadj]
  · simp [hadj]

theorem everyXReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hA1Card : C.A1.card = 3) :
    everyXReached (graphBits G L) = true := by
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
    have htEq : 4 + x = (3 + x) + 1 := by omega
    conv_lhs => rw [hsEq, htEq]
    rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.hArc_coreBits
      G.Adj _ _ _ i (3 + x) (by omega) (by omega)]
    have hDest : (⟨(3 + x) + 1, by omega⟩ : Fin 8) =
        ⟨x + 4, by omega⟩ := by
      apply Fin.ext
      change 3 + x + 1 = x + 4
      omega
    rw [hDest]
    rw [decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := by
      simpa [aOneLabelEquiv_val] using congrArg Subtype.val hi
    rw [hiVal]
    exact hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨pi, hpi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨pi, pi.isLt, ?_⟩
    rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToH_coreBits
      G.Adj _ _ _ pi (3 + x) pi.isLt (by omega)]
    have hDest : (⟨(3 + x) + 1, by omega⟩ : Fin 8) =
        ⟨x + 4, by omega⟩ := by
      apply Fin.ext
      change 3 + x + 1 = x + 4
      omega
    rw [hDest]
    simpa [congrArg Subtype.val hpi] using hux

theorem allZReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 5) :
    allZReached zCount (graphBits G L) = true := by
  rw [allZReached, all_eq_true_iff]
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
  rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToZ_coreBits
      G.Adj _ _ _ i z i.isLt (by omega) hz]
  simpa [congrArg Subtype.val hi] using hpz

theorem inactiveZZero_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 5) :
    inactiveZZero zCount (graphBits G L) = true := by
  rw [inactiveZZero, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro j hj
  rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToZ_coreBits_inactive
    G.Adj _ _ _ p (zCount + j) hp (by omega) (by omega)]
  decide

theorem A_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = Shared.directCount G C.A u + Shared.directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG u hu
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.P) u (by
    intro v hv
    simpa [hPB] using hCap hv)
  rw [directCount_union_of_disjoint G C.A C.P u hAP] at hEq
  exact hEq

theorem aMinimumAndDegree_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hzLe : zCount ≤ 5) :
    aMinimumAndDegree (graphBits G L) = true := by
  rw [aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L hG hzLe a ha
  have hPO := aPOut_toNat G C L hG hzLe a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 3 ≤ (aOut (graphBits G L) a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut (graphBits G L) a).toNat = 3 →
      7 ≤ (aPOut (graphBits G L) a).toNat := by
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
  have hTotal : 8 ≤ (aOut (graphBits G L) a).toNat +
      (aPOut (graphBits G L) a).toNat := by
    rw [hAO, hPO, ← A_outdegree_eq_A_add_P G C hG hPB _ (L.a _).2]
    exact hMin _
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simpa [BitVec.ule_eq_decide] using hAmin
    · rw [Bool.or_eq_true]
      by_cases heq : aOut (graphBits G L) a = 3
      · right
        simpa [BitVec.ule_eq_decide] using hTie (congrArg BitVec.toNat heq)
      · left
        simpa using heq
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [BitVec.toNat_add]
    have hSmall : (aOut (graphBits G L) a).toNat +
        (aPOut (graphBits G L) a).toNat < 256 := by
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

theorem pMinimumDegree_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 7)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hzCount : zCount ≤ 5) :
    pMinimumDegree zCount (graphBits G L) = true := by
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
  have hZ := pZOut_toNat G C L hG hzCount p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have hSmall : (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat < 256 := by
    rw [hP, hH]
    have hpC : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hpLe : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hhLe : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  rw [Nat.mod_eq_of_lt hSmall]
  have hSmall' : (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat +
      (pZOut zCount (graphBits G L) p).toNat < 256 := by
    rw [hP, hH, hZ]
    have hpC : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hzC : (externalTargets G C).card = zCount := by
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
  have hNatural : 8 ≤ (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat +
      (pZOut zCount (graphBits G L) p).toNat := by
    rw [hP, hH, hZ]
    have hDegreeLower := hMin (L.p ⟨p, hp⟩).1
    omega
  exact hNatural

theorem aNonSeymour_all_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hzLe : zCount ≤ 5) :
    all 8 (aNonSeymour zCount (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  exact nonSeymour_graphBits_true G C L hG hzLe hPB hNoSeymour a (by omega)

theorem degreeThreeTie_all_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hPB : C.P = C.B) (hzLe : zCount ≤ 5) :
    all 8 (degreeThreeTieCondition (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  unfold degreeThreeTieCondition
  by_cases hInner : degreeThreeInner (graphBits G L) a = true
  · rw [hInner]
    simp only [Bool.not_true, Bool.false_or]
    have hDeg : aOut (graphBits G L) a = 3 := by
      simp only [degreeThreeInner, Bool.and_eq_true] at hInner
      simpa [degreeThree] using hInner.1
    have hAO := aOut_toNat G C L hG hzLe a ha
    have hPO := aPOut_toNat G C L hG hzLe a ha
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change Shared.directCount G C.A (L.a ⟨a, ha⟩).1 = 3
      rw [← hAO, hDeg]
      decide
    have hTie := (hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2).2 hCardEq
    change C.r ≤ Shared.directCount G C.B (L.a ⟨a, ha⟩).1 at hTie
    rw [← hPB] at hTie
    have hr : C.r = 7 := by
      change C.P.card = 7
      simpa using (Fintype.card_congr L.p).symm
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hPO]
    simpa [hr, BitVec.toNat_ofNat] using hTie
  · have : degreeThreeInner (graphBits G L) a = false :=
      Bool.eq_false_of_not_eq_true hInner
    simp [this]

theorem degreeThreeConsequences_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hOriented : orientedA (graphBits G L) = true)
    (hMinimum : ∀ a < 8, (3 : BitVec 8).ule (aOut (graphBits G L) a) = true) :
    degreeThreeClassification (graphBits G L) = true ∧
      threeInnerWitnesses (graphBits G L) = true := by
  let arc := aArc (graphBits G L)
  have hOr : InnerDegreeThree.oriented arc = true := by
    simpa [arc, InnerDegreeThree.oriented, orientedA] using hOriented
  have hMin : InnerDegreeThree.minimumThree arc = true := by
    rw [InnerDegreeThree.minimumThree, all_eq_true_iff]
    intro a ha
    simpa [arc, InnerDegreeThree.outCount, aOut] using hMinimum a ha
  constructor
  · change InnerDegreeThree.classification arc = true
    exact InnerDegreeThree.classification_of arc hOr hMin
  · change InnerDegreeThree.threeWitnesses arc = true
    exact InnerDegreeThree.threeWitnesses_of arc hOr hMin

theorem hallCondition_all_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzLe : zCount ≤ 5) :
    all 8 (hallCondition zCount (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  unfold hallCondition
  by_cases hInner : innerSeymour (graphBits G L) a = true
  · rw [hInner]
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
    let v := (L.a ⟨a, ha⟩).1
    let S := CertificateBridge.internalFirstNeighbors G C.P v
    let T := CertificateBridge.internalSecondNeighbors (G := G) C.A v
    let U := hallTargets G C v
    have hAO := aOut_toNat G C L hG hzLe a ha
    have hSO := aPOut_toNat G C L hG hzLe a ha
    have hTO := innerSecondCount_toNat G C L hG hzLe a ha
    have hUO := hallZCount_toNat G C L hG hzLe a ha
    have hInnerNat : (aOut (graphBits G L) a).toNat ≤
        (innerSecondCount (graphBits G L) a).toNat := by
      unfold innerSeymour at hInner
      simpa [BitVec.ule_eq_decide] using hInner
    have hOutEq : G.outdegree v = S.card +
        Shared.directCount G C.A v := by
      have h := A_outdegree_eq_A_add_P G C hG hPB v (L.a ⟨a, ha⟩).2
      dsimp [v, S, CertificateBridge.internalFirstNeighbors,
        Shared.directCount] at h ⊢
      omega
    have hALe : Shared.directCount G C.A v ≤ 7 := by
      have hSub : C.A.filter (G.Adj v) ⊆ C.A.erase v := by
        intro w hw
        rcases Finset.mem_filter.mp hw with ⟨hwA, hvw⟩
        exact Finset.mem_erase.mpr ⟨fun heq ↦ hG.1 v (heq ▸ hvw), hwA⟩
      have hCard := Finset.card_le_card hSub
      have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
      have hvA : v ∈ C.A := (L.a ⟨a, ha⟩).2
      rw [Finset.card_erase_of_mem hvA, hACard] at hCard
      exact hCard
    have hSPos : 1 ≤ S.card := by
      have hvMin := hMin v
      omega
    have hTSub : T ⊆ G.secondOutNeighborFinset v := by
      intro w hw
      rcases Finset.mem_filter.mp hw with
        ⟨hwA, hNot, hwv, middle, hmA, hFirst, hLast⟩
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨middle, hFirst, hLast⟩, hNot, hwv⟩
    have hUSub : U ⊆ G.secondOutNeighborFinset v := by
      intro z hz
      rcases Finset.mem_filter.mp hz with
        ⟨hzZ, p, hpP, hFirst, hLast⟩
      have hNot := A_not_adj_external G C hG v z (L.a ⟨a, ha⟩).2 hzZ
      have hne : z ≠ v := by
        intro heq
        subst z
        exact external_not_mem_A G C hG v hzZ (L.a ⟨a, ha⟩).2
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨p, hFirst, hLast⟩, hNot, hne⟩
    have hDisjoint : Disjoint T U := by
      rw [Finset.disjoint_left]
      intro w hwT hwU
      have hwA := (Finset.mem_filter.mp hwT).1
      have hwZ := (Finset.mem_filter.mp hwU).1
      exact external_not_mem_A G C hG w hwZ hwA
    have hUnionSub : T ∪ U ⊆ G.secondOutNeighborFinset v :=
      Finset.union_subset hTSub hUSub
    have hSecondLower : T.card + U.card ≤ G.secondOutdegree v := by
      rw [← Finset.card_union_of_disjoint hDisjoint]
      unfold Digraph.secondOutdegree
      exact Finset.card_le_card hUnionSub
    have hStrict : U.card < S.card := by
      by_contra hNotStrict
      have hUS : S.card ≤ U.card := by omega
      have hTA : Shared.directCount G C.A v ≤ T.card := by
        dsimp [T, v]
        rw [← hTO, ← hAO]
        exact hInnerNat
      have hNotSeymour : ¬G.IsSeymourVertex v := fun h ↦
        hNoSeymour ⟨v, h⟩
      have hSecondStrict :=
        Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNotSeymour
      omega
    constructor
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hSO]
      simpa [S, Shared.directCount,
        CertificateBridge.internalFirstNeighbors] using hSPos
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
      rw [hUO, hSO]
      simpa [U, S, hallTargets, Shared.directCount,
        CertificateBridge.internalFirstNeighbors] using hStrict
  · have hFalse : innerSeymour (graphBits G L) a = false :=
      Bool.eq_false_of_not_eq_true hInner
    simp [hFalse]

theorem pSecondPCount_le_graphPSecond {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (p : Nat) (hp : p < 7) :
    (pSecondPCount zCount (graphBits G L) p).toNat ≤
      (C.P.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply count_le_filterCard C.P L.p
    (fun q ↦ strictSecondLocal zCount (graphBits G L) (8 + p) (8 + q))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro j hj
  have hmem := strictSecondLocal_true_mem G C L hG hzLe
    (8 + p) (8 + j) (by omega) (by omega) hj
  simpa [labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
    show 8 + j.val < 15 by omega] using hmem

theorem pSecondPCount_le_qCount {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5)
    (p : Nat) (hp : p < 7) :
    (pSecondPCount zCount (graphBits G L) p).toNat ≤
      TerminalAlphaBeta.qCount G C.P C.H (L.p ⟨p, hp⟩).1 := by
  unfold pSecondPCount TerminalAlphaBeta.qCount
  unfold TerminalAlphaBeta.secondNeighborsThrough
  apply count_le_filterCard C.P L.p
    (fun q => strictSecondLocal zCount (graphBits G L) (8 + p) (8 + q))
    (fun v => ¬G.Adj (L.p ⟨p, hp⟩).1 v ∧
      v ≠ (L.p ⟨p, hp⟩).1 ∧ ∃ w ∈ C.P ∪ C.H,
        G.Adj (L.p ⟨p, hp⟩).1 w ∧ G.Adj w v) (by omega)
  intro j hj
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hj
  rcases hj with ⟨⟨hjp, hNotDirect⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hSecond⟩
  have hTargetNe : (L.p j).1 ≠ (L.p ⟨p, hp⟩).1 := by
    intro hEq
    have : j = ⟨p, hp⟩ := L.p.injective (Subtype.ext hEq)
    have hjp' : j.val ≠ p := by simpa using hjp
    exact hjp' (congrArg Fin.val this)
  have hNotAdj : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.p j).1 := by
    intro hAdj
    have hTrue : coreArc zCount (graphBits G L) (8 + p) (8 + j.val) = true := by
      rw [coreArc_graphBits G C L hG hzLe (8 + p) (8 + j.val)
        (by omega) (by omega)]
      exact decide_eq_true (by
        simpa [labelledVertex, show ¬8 + p < 8 by omega,
          show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
          show 8 + j.val < 15 by omega] using hAdj)
    simp [hTrue] at hNotDirect
  have hFirstGraph : G.Adj (L.p ⟨p, hp⟩).1 (labelledVertex G L middle) := by
    rw [coreArc_graphBits G C L hG hzLe (8 + p) middle
      (by omega) (by omega)] at hFirst
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 15 by omega] using hFirst
  have hSecondGraph : G.Adj (labelledVertex G L middle) (L.p j).1 := by
    rw [coreArc_graphBits G C L hG hzLe middle (8 + j.val)
      (by omega) (by omega)] at hSecond
    simpa [labelledVertex, show ¬8 + j.val < 8 by omega,
      show 8 + j.val < 15 by omega] using hSecond
  have hMiddle : labelledVertex G L middle ∈ C.P ∪ C.H := by
    by_cases hmA : middle < 8
    · have hmZero : middle ≠ 0 := by
        intro hzero
        subst middle
        have hRootToP : G.Adj C.a1 (L.p ⟨p, hp⟩).1 :=
          (Finset.mem_filter.mp (L.p ⟨p, hp⟩).2).2
        have hPToRoot : G.Adj (L.p ⟨p, hp⟩).1 C.a1 := by
          simpa [labelledVertex, L.a_zero] using hFirstGraph
        exact hG.2 hRootToP hPToRoot
      apply Finset.mem_union_right
      simp only [labelledVertex, dif_pos hmA]
      by_cases hmSmall : middle ≤ 3
      · have hIdx : (⟨middle, hmA⟩ : Fin 8) =
            ⟨(middle - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hIdx]
        exact Finset.mem_union_left C.X (L.a_aOne ⟨middle - 1, by omega⟩)
      · have hIdx : (⟨middle, hmA⟩ : Fin 8) =
            ⟨(middle - 4) + 4, by omega⟩ := Fin.ext (by simp; omega)
        rw [hIdx]
        exact Finset.mem_union_right C.A1 (L.a_x ⟨middle - 4, by omega⟩)
    · apply Finset.mem_union_left
      simp [labelledVertex, hmA, show middle < 15 by omega]
  exact ⟨hNotAdj, hTargetNe, labelledVertex G L middle, hMiddle,
    hFirstGraph, hSecondGraph⟩

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem sumAOut_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) :
    (sumCount 8 (aOut (graphBits G L))).toNat = edgeCount G C.A C.A := by
  rw [toNat_sumCount]
  have hEach : ∀ i : Fin 8, (aOut (graphBits G L) i).toNat =
      Shared.directCount G C.A (L.a i).1 := by
    intro i
    exact aOut_toNat G C L hG (by omega) i i.isLt
  have hSum : (∑ i ∈ Finset.range 8,
      (aOut (graphBits G L) i).toNat) = edgeCount G C.A C.A := by
    rw [edgeCount_eq_sum_fin G C.A C.A L.a, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.A C.A
  have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
  rw [ha] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem aMissing_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) :
    (aMissing (graphBits G L)).toNat = 28 - edgeCount G C.A C.A := by
  rw [aMissing, BitVec.toNat_sub, sumAOut_toNat G C L hG]
  have hInternal : edgeCount G C.A C.A ≤ 28 := by
    have h := internal_edgeCount_le_choose_two G C.A hG
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    rw [ha] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.A C.A + 28) % 256) = _
  have hRewrite : 256 - edgeCount G C.A C.A + 28 =
      256 + (28 - edgeCount G C.A C.A) := by omega
  have hSmall : 28 - edgeCount G C.A C.A < 256 := by omega
  rw [hRewrite, Nat.add_mod]
  norm_num [Nat.mod_eq_of_lt hSmall]

theorem totalPToZ_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) :
    (totalPToZ 5 (graphBits G L)).toNat =
      edgeCount G C.P (externalTargets G C) := by
  rw [totalPToZ, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pZOut 5 (graphBits G L) i).toNat =
      Shared.directCount G (externalTargets G C) (L.p i).1 := by
    intro i
    exact pZOut_toNat G C L hG (by omega) i i.isLt
  have hSum : (∑ i ∈ Finset.range 7,
      (pZOut 5 (graphBits G L) i).toNat) =
        edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_eq_sum_fin G C.P (externalTargets G C) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hz : (externalTargets G C).card = 5 := by
    simpa using (Fintype.card_congr L.z).symm
  rw [hp, hz] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) :
    (externalMissing 5 (graphBits G L)).toNat =
      35 - edgeCount G C.P (externalTargets G C) := by
  rw [externalMissing, BitVec.toNat_sub, totalPToZ_toNat G C L hG]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hz : (externalTargets G C).card = 5 := by
    simpa using (Fintype.card_congr L.z).symm
  rw [hp, hz] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.P (externalTargets G C) + 35) % 256) = _
  omega

set_option maxHeartbeats 5000000 in
-- The interval enumeration below checks every small missing-edge and row-size case.
theorem individualEffectiveLower_graph (C : G.LocalConfiguration)
    (L : Labels G 5 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hmBound : 35 - edgeCount G C.P (externalTargets G C) ≤ 14)
    (p : Nat) (hp : p < 7)
    (hps : ¬G.Adj (L.p ⟨p, hp⟩).1 C.s) :
    (individualEffectiveLower (graphBits G L) p).toNat ≤
      (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G L
  let v := (L.p ⟨p, hp⟩).1
  let S := FiveZUnionEightCapacity.directZNeighbors G C v
  let U := directZEffectiveUnion G C v
  let m := 35 - edgeCount G C.P (externalTargets G C)
  let s := S.card
  have hmDef : m = 35 - edgeCount G C.P (externalTargets G C) := rfl
  have hsDef : s = S.card := rfl
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = 5 := by
    simpa using (Fintype.card_congr L.z).symm
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ 5 := by
    have hSub : C.Z ⊆ externalTargets G C := Finset.subset_union_left
    exact (Finset.card_le_card
      ((FiveZUnionEightCapacity.directZNeighbors_subset_Z G C v).trans hSub)).trans_eq
        hZCard
  have hLower := directZ_effective_capacity_lower G C hMin v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hES : Shared.directCount G (externalTargets G C) v = s := by
    rw [SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
      G C v hvP]
    have hps' : ¬G.Adj v C.s := by simpa [v] using hps
    rw [show epsilonAt G v C.s = 0 by simp [epsilonAt, hps'], Nat.add_zero]
    exact (FiveZUnionEightCapacity.card_directZNeighbors G C v).symm
  have hRow : 5 - s ≤ m :=
    by
      simpa [m, hES] using
        (SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly.external_row_missing_le_total
          G C hPCard hZCard v hvP)
  have hToP : edgeCount G S C.P ≤ m - (5 - s) :=
    SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly.directZ_to_P_capacity_external
      G C hG hPCard hZCard v hvP hps
  have hM : (externalMissing 5 bits).toNat = m := by
    exact externalMissing_toNat G C L hG
  have hS : (pZOut 5 bits p).toNat = s := by
    rw [pZOut_toNat G C L hG (by omega) p hp]
    exact hES
  have hMBV : externalMissing 5 bits = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hSBV : pZOut 5 bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hm : m ≤ 14 := by simpa [m] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change (individualEffectiveLower bits p).toNat ≤ U.card
  simp only [individualEffectiveLower]
  rw [hMBV, hSBV]
  interval_cases m <;> interval_cases s <;>
    simp only [BEq.rfl, BitVec.ofNat_eq_ofNat, BitVec.reduceBEq,
      BitVec.toNat_ofNat, Bool.false_eq_true, Finset.one_le_card,
      Nat.add_one_sub_one, Nat.choose, Nat.not_ofNat_le_one, Nat.one_le_ofNat,
      Nat.one_mod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Nat.zero_mod, OfNat.ofNat_ne_zero, Std.le_refl, add_zero,
      effectiveAtRowSize, nonpos_iff_eq_zero, one_mul, one_ne_zero,
      tsub_le_iff_right, tsub_self, tsub_zero, zero_le, zero_mul, ↓reduceIte]
      at hmDef hsDef hInternal hRow hToP hLower ⊢ <;>
    first | omega | exact Finset.card_pos.mp (by omega)

theorem pEffectiveCondition_all_true (C : G.LocalConfiguration)
    (L : Labels G 5 C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hHCard : C.H.card = 7)
    (hmBound : 35 - edgeCount G C.P (externalTargets G C) ≤ 14) :
    all 7 (pEffectiveCondition (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hP := pOut_toNat G C L hG p hp
  have hH := pHOut_toNat G C L hG hHCard p hp
  have hZ := pZOut_toNat G C L hG (by omega) p hp
  have hNatural : (pSecondPCount 5 (graphBits G L) p).toNat +
      (individualEffectiveLower (graphBits G L) p).toNat + 1 ≤
      (pOut (graphBits G L) p).toNat +
        2 * (pHOut (graphBits G L) p).toNat +
          (pZOut 5 (graphBits G L) p).toNat := by
    by_cases hps : G.Adj v C.s
    · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
        G C hG hPB hNoSeymour hRootDegree v hvP hps
      have hSecond := pSecondPCount_le_qCount G C L hG (by omega) p hp
      let m := 35 - edgeCount G C.P (externalTargets G C)
      let s := Shared.directCount G (externalTargets G C) v
      have hm : m ≤ 14 := by simpa [m] using hmBound
      have hs : s ≤ 5 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (by simpa using (Fintype.card_congr L.z).symm)
      have hRow :=
        SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly.external_row_missing_le_total
          G C hPCard (by simpa using (Fintype.card_congr L.z).symm) v hvP
      have hMNat : (externalMissing 5 (graphBits G L)).toNat = m :=
        externalMissing_toNat G C L hG
      have hSNat : (pZOut 5 (graphBits G L) p).toNat = s := hZ
      have hMBV : externalMissing 5 (graphBits G L) = BitVec.ofNat 8 m := by
        apply BitVec.eq_of_toNat_eq
        rw [hMNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hSBV : pZOut 5 (graphBits G L) p = BitVec.ofNat 8 s := by
        apply BitVec.eq_of_toNat_eq
        rw [hSNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hTable : (individualEffectiveLower (graphBits G L) p).toNat ≤ 8 := by
        change 5 - s ≤ m at hRow
        simp only [individualEffectiveLower]
        rw [hMBV, hSBV]
        interval_cases m <;> interval_cases s <;>
          simp [effectiveAtRowSize] at hRow ⊢
      have hEpsilon : epsilonAt G v C.s = 1 := by simp [epsilonAt, hps]
      rw [hEpsilon] at hEquation
      dsimp [v] at hSecond hEquation hTable hps
      rw [hP, hH, hZ]
      rw [SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
        G C (L.p ⟨p, hp⟩).1 hvP]
      simp [epsilonAt, hps]
      omega
    · have hTable := individualEffectiveLower_graph G C L hG hMin
        hmBound p hp (by simpa [v] using hps)
      have hPS := pSecondPCount_le_graphPSecond G C L hG (by omega) p hp
      have hUnion :=
      BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.PSecond_add_directZEffective_card_le_second_add_H
          G C hG hPB v hvP hps
      have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun h => hNoSeymour ⟨v, h⟩)
      have hDegreeBlocks := SeymourEight.BSixKTwoCoreGraphBridge.outdegree_P_eq_blocks
        G C hG hPB v hvP
      have hHCount : Shared.directCount G C.H v =
          Shared.directCount G C.A1 v + Shared.directCount G C.X v :=
        directCount_union_of_disjoint G C.A1 C.X v
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
      have hDegree : G.outdegree v =
          Shared.directCount G (externalTargets G C) v +
          Shared.directCount G C.H v + Shared.directCount G C.P v := by
        rw [hHCount]
        omega
      dsimp [v] at hPS hUnion hNS hDegree hTable
      rw [hP, hH, hZ]
      omega
  simp only [pEffectiveCondition, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pSecondPCount 5 (graphBits G L) p).toNat +
      (individualEffectiveLower (graphBits G L) p).toNat + 1) % 256 ≤
    ((pOut (graphBits G L) p).toNat +
      2 * (pHOut (graphBits G L) p).toNat +
        (pZOut 5 (graphBits G L) p).toNat) % 256
  have hRightSmall : (pOut (graphBits G L) p).toNat +
      2 * (pHOut (graphBits G L) p).toNat +
        (pZOut 5 (graphBits G L) p).toNat < 256 := by
    have hpLe : (pOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hP]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hhLe : (pHOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hH]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hzLe : (pZOut 5 (graphBits G L) p).toNat ≤ 5 := by
      rw [hZ]
      have hZCard : (externalTargets G C).card = 5 := by
        simpa using (Fintype.card_congr L.z).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
    omega
  rw [Nat.mod_eq_of_lt hRightSmall,
    Nat.mod_eq_of_lt (hNatural.trans_lt hRightSmall)]
  exact hNatural

/-- All graph-theoretic hypotheses needed by the compact finite core. -/
theorem commonCore_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hA1Card : C.A1.card = 3) (hHCard : C.H.card = 7) :
    commonCore (graphBits G L) = true := by
  let bits := graphBits G L
  have hOrA : orientedA bits = true := orientedA_true G C L hG (by omega)
  have hOrP : orientedP bits = true := orientedP_true G C L hG
  have hOrPH : orientedPH bits = true := orientedPH_true G C L hG
  have hX : everyXReached bits = true := everyXReached_true G C L hA1Card
  have hZ : allZReached 5 bits = true := allZReached_true G C L (by omega)
  have hAMin : aMinimumAndDegree bits = true :=
    aMinimumAndDegree_true G C L hG hPB hPivot hMin hk (by omega)
  have hANon : all 8 (aNonSeymour 5 bits) = true :=
    aNonSeymour_all_true G C L hG hPB hNoSeymour (by omega)
  have hPMin : pMinimumDegree 5 bits = true :=
    pMinimumDegree_true G C L hG hPB hHCard hMin (by omega)
  have hTie : all 8 (degreeThreeTieCondition bits) = true :=
    degreeThreeTie_all_true G C L hG hPivot hk hPB (by omega)
  have hAMinEach : ∀ a < 8, (3 : BitVec 8).ule (aOut bits a) = true := by
    rw [aMinimumAndDegree, all_eq_true_iff] at hAMin
    intro a ha
    have hRow := hAMin a ha
    simp only [Bool.and_eq_true] at hRow
    exact hRow.1.1
  have hDegreeThree := degreeThreeConsequences_true G C L hOrA hAMinEach
  change degreeThreeClassification bits = true ∧
    threeInnerWitnesses bits = true at hDegreeThree
  have hHall : all 8 (hallCondition 5 bits) = true :=
    hallCondition_all_true G C L hG hPB hMin hNoSeymour (by omega)
  have hDual : degreeAndDualConditions bits = true :=
    degreeAndDual_of_local bits hOrA hOrPH hAMin
  have hMissing : (externalMissing 5 bits).ule 12 = true :=
    externalMissing_le_twelve bits hOrA hOrP hAMin hPMin hDual
  have hmNat : 35 - edgeCount G C.P (externalTargets G C) ≤ 14 := by
    have hToNat := externalMissing_toNat G C L hG
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at hMissing
    have hTwelve : ((12 : BitVec 8).toNat) = 12 := by decide
    rw [hTwelve] at hMissing
    rw [hToNat] at hMissing
    omega
  have hPEff : all 7 (pEffectiveCondition bits) = true :=
    pEffectiveCondition_all_true G C L hG hPB hMin hNoSeymour
      hRootDegree hHCard hmNat
  have hSharp : sharpKing bits = true := sharpKing_of_orientedP bits hOrP
  change commonCore bits = true
  simp only [commonCore, hOrA, hOrP, hOrPH, hX, hZ, hAMin, hANon,
    hPMin, hPEff, hHall, hTie, hDegreeThree.1, hDegreeThree.2,
    hDual, hSharp, Bool.and_self]

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Assembly
