import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.AugmentedBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.EffectiveBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 5000000 in
def auxiliarySet (C : G.LocalConfiguration) : Finset V :=
  BSevenKThree.reachedQ G C ∪ externalTargets G C

set_option maxHeartbeats 5000000 in
theorem auxiliarySet_card {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hy : BSevenKThree.y G C = yValue) :
    (auxiliarySet G C).card = yValue + zCount := by
  have hDis : Disjoint (BSevenKThree.reachedQ G C) (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left Finset.inter_subset_left
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [auxiliarySet, Finset.card_union_of_disjoint hDis]
  have hz : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  simpa [BSevenKThree.y, hz] using congrArg (fun n ↦ n + zCount) hy

set_option maxHeartbeats 5000000 in
theorem auxiliarySet_disjoint_P (C : G.LocalConfiguration) :
    Disjoint (auxiliarySet G C) C.P := by
  rw [Finset.disjoint_left]
  intro v hvE hvP
  rcases Finset.mem_union.mp hvE with hvQ | hvExt
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
        (Finset.mem_inter.mp hvQ).1
  · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExt

set_option maxHeartbeats 5000000 in
theorem directCount_Q_eq_reachedQ (C : G.LocalConfiguration) (p : V)
    (hp : p ∈ C.P) :
    directCount G C.Q p = directCount G (BSevenKThree.reachedQ G C) p := by
  unfold directCount CertificateBridge.internalFirstNeighbors
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · intro h
    exact ⟨Finset.mem_inter.mpr ⟨h.1,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨p, Finset.mem_union_right C.A1 hp, h.2⟩⟩, h.2⟩
  · intro h
    exact ⟨(Finset.mem_inter.mp h.1).1, h.2⟩

set_option maxHeartbeats 5000000 in
theorem pAuxOut_to_auxiliary {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7)
    (hzLe : zCount ≤ 2) (p : Nat) (hp : p < 5) :
    (pAuxOut zCount (graphArc G L) (graphPToZ G L) p).toNat =
      directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1 := by
  have hBlocks := pBlockCounts G C L hHCard (by omega) p hp
  have hDis : Disjoint (BSevenKThree.reachedQ G C) (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left Finset.inter_subset_left
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [pAuxOut, BitVec.toNat_add, hBlocks.2.2.1, hBlocks.2.2.2,
    directCount_Q_eq_reachedQ G C _ (L.p _).2,
    Nat.mod_eq_of_lt (by
      have hq := Finset.card_le_card (Finset.filter_subset
        (G.Adj (L.p ⟨p, hp⟩).1) (BSevenKThree.reachedQ G C))
      have hz := Finset.card_le_card (Finset.filter_subset
        (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
      have hqCard : (BSevenKThree.reachedQ G C).card ≤ 2 := by
        exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
          (by simpa using (Fintype.card_congr L.q).symm)
      have hzCard : (externalTargets G C).card = zCount := by
        simpa using (Fintype.card_congr L.z).symm
      change directCount G (BSevenKThree.reachedQ G C) (L.p ⟨p, hp⟩).1 ≤
        (BSevenKThree.reachedQ G C).card at hq
      change directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤
        (externalTargets G C).card at hz
      omega)]
  rw [auxiliarySet, directCount_union_of_disjoint G _ _ _ hDis]

set_option maxHeartbeats 5000000 in
theorem totalPToAux_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7) (hzLe : zCount ≤ 2) :
    (totalPToAux zCount (graphArc G L) (graphPToZ G L)).toNat =
      edgeCount G C.P (auxiliarySet G C) := by
  have hTotal : totalPToAux zCount (graphArc G L) (graphPToZ G L) =
      sumCount 5 (pAuxOut zCount (graphArc G L) (graphPToZ G L)) := by
    simp only [totalPToAux, totalPToQ, totalPToZ, pAuxOut, sumCount]
    ac_rfl
  rw [hTotal, AugmentedBridge.toNat_sumCount, ← Fin.sum_univ_eq_sum_range]
  have hEq : (∑ i : Fin 5,
      (pAuxOut zCount (graphArc G L) (graphPToZ G L) i).toNat) =
      ∑ i : Fin 5, directCount G (auxiliarySet G C) (L.p i).1 := by
    apply Finset.sum_congr rfl
    intro i _
    exact pAuxOut_to_auxiliary G C L hHCard hzLe i i.isLt
  have hSum : (∑ i : Fin 5,
      (pAuxOut zCount (graphArc G L) (graphPToZ G L) i).toNat) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [hEq, edgeCount_eq_sum_fin G C.P (auxiliarySet G C) L.p]
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have he : (auxiliarySet G C).card ≤ 4 := by
    rw [auxiliarySet_card G C L (yValue := BSevenKThree.y G C) rfl]
    have hy : BSevenKThree.y G C ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq
        (by simpa using (Fintype.card_congr L.q).symm)
    omega
  rw [hp] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 5000000 in
theorem externalMissing_toNat {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7) (hzLe : zCount ≤ 2)
    (hy : BSevenKThree.y G C = yValue) (he : yValue + zCount = 3) :
    (externalMissing zCount (graphArc G L) (graphPToZ G L)).toNat =
      15 - edgeCount G C.P (auxiliarySet G C) := by
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  rw [hp, auxiliarySet_card G C L hy, he] at hCap
  have h15 : (15 : BitVec 8).toNat = 15 := by decide
  have hLe : totalPToAux zCount (graphArc G L) (graphPToZ G L) ≤
      (15 : BitVec 8) := by
    rw [BitVec.le_def, totalPToAux_toNat G C L hHCard hzLe, h15]
    omega
  rw [externalMissing, BitVec.toNat_sub_of_le hLe,
    totalPToAux_toNat G C L hHCard hzLe, h15]

set_option maxHeartbeats 5000000 in
abbrev directAuxNeighbors (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxNeighbors G E p

set_option maxHeartbeats 5000000 in
abbrev directAuxEffectiveUnion (C : G.LocalConfiguration)
    (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffectiveUnion G C E p

set_option maxHeartbeats 5000000 in
theorem directAux_to_P_capacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (E : Finset V)
    (hPCard : C.P.card = 5) (eCount : Nat) (hECard : E.card = eCount)
    (p : V) (hpP : p ∈ C.P) :
    edgeCount G (directAuxNeighbors G E p) C.P ≤
      (5 * eCount - edgeCount G C.P E) -
        (eCount - (directAuxNeighbors G E p).card) := by
  let S := directAuxNeighbors G E p
  let T := E \ S
  have hS : S ⊆ E := Finset.filter_subset _ _
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = E := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = eCount - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hECard]
  have hpT : directCount G T p = 0 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e heT hpe
    exact (Finset.mem_sdiff.mp heT).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp heT).1, hpe⟩)
  have hPT : edgeCount G C.P T ≤ 4 * T.card := by
    calc
      _ ≤ ∑ q ∈ C.P, if q = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqp : q = p
        · subst q; simp [hpT]
        · simp only [hqp, if_false]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 4 * T.card := by
        rw [← Finset.sum_erase_add C.P (fun q ↦ if q = p then 0 else T.card) hpP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ q ∈ C.P.erase p, if q = p then 0 else T.card) =
              ∑ _q ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [if_neg (Finset.mem_erase.mp hq).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 4 * T.card := by
            rw [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit : edgeCount G C.P E = edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = eCount := by
    rw [hTCard]
    have := (Finset.card_le_card hS).trans_eq hECard
    omega
  change edgeCount G S C.P ≤
    (5 * eCount - edgeCount G C.P E) - (eCount - S.card)
  omega

set_option maxHeartbeats 5000000 in
theorem individualEffectiveTable_toNat_le (m s : BitVec 8) :
    (individualEffectiveTable m s).toNat ≤ 10 := by
  have h : (individualEffectiveTable m s).ule (10 : BitVec 8) = true := by
    simp only [individualEffectiveTable, effectiveAtRowSize]
    bv_decide
  simpa [BitVec.ule_eq_decide] using h

set_option maxHeartbeats 5000000 in
theorem individualEffectiveLower_graph {zCount yValue : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hzLe : zCount ≤ 2)
    (hy : BSevenKThree.y G C = yValue) (he : yValue + zCount = 3)
    (hmBound :
      (externalMissing zCount (graphArc G L) (graphPToZ G L)).toNat ≤ 3)
    (p : Nat) (hp : p < 5) :
    (individualEffectiveLower zCount (graphArc G L) (graphPToZ G L) p).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C)
        (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  let m := 15 - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = 3 := by simpa [E, he] using auxiliarySet_card G C L hy
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ 3 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hRow : 3 - s ≤ m := by
    have hOther : ∑ q ∈ C.P.erase v, directCount G E q ≤ 4 * 3 := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase v, 3 := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 4 * 3 := by simp [Finset.card_erase_of_mem hvP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (directCount G E) hvP
    have hEdge : edgeCount G C.P E =
        (∑ q ∈ C.P.erase v, directCount G E q) + directCount G E v := by
      unfold edgeCount
      omega
    have hsEq : s = directCount G E v := rfl
    dsimp [m]
    omega
  have hLower :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffective_capacity_lower
      G C hMin E (auxiliarySet_disjoint_P G C) v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directAux_to_P_capacity G C hG E hPCard 3 hECard v hvP
  have hMN :
      (externalMissing zCount (graphArc G L) (graphPToZ G L)).toNat = m := by
    simpa [m, E] using externalMissing_toNat G C L hHCard hzLe hy he
  have hSN :
      (pAuxOut zCount (graphArc G L) (graphPToZ G L) p).toNat = s := by
    rw [pAuxOut_to_auxiliary G C L hHCard hzLe p hp]
    rfl
  have hMBV : externalMissing zCount (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hMN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hSBV : pAuxOut zCount (graphArc G L) (graphPToZ G L) p =
      BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hSN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : m ≤ 3 := by simpa [hMN] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (3 - s) at hToP
  change (individualEffectiveLower zCount (graphArc G L)
    (graphPToZ G L) p).toNat ≤ U.card
  simp only [individualEffectiveLower]
  rw [hMBV, hSBV]
  interval_cases m <;> interval_cases s <;>
    simp [effectiveAtRowSize, individualEffectiveTable, Nat.choose,
      BitVec.toNat_ofNat] at hm hs hRow hInternal hToP hLower ⊢ <;>
    omega

set_option maxHeartbeats 5000000 in
theorem pStrictSecond_true_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (p r : Nat)
    (hp : p < 5) (hr : r < 5)
    (hSecond : strictSecondLocal (graphArc G L) (8 + p) (8 + r) = true) :
    (L.p ⟨r, hr⟩).1 ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1 := by
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 13 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  have hFirst' : G.Adj (labelledVertex G L (8 + p))
      (labelledVertex G L middle) := by
    apply of_decide_eq_true
    rw [← coreArc_graph G C L hG (8 + p) middle (by omega) (by omega)]
    simpa [coreArc, show ¬8 + p < 8 by omega,
      show 8 + p < 13 by omega, show middle < 15 by omega] using hFirst
  have hLast' : G.Adj (labelledVertex G L middle)
      (labelledVertex G L (8 + r)) := by
    apply of_decide_eq_true
    rw [← coreArc_graph G C L hG middle (8 + r) (by omega) (by omega)]
    by_cases hmA : middle < 8
    · simpa [coreArc, hmA, show 8 + r < 15 by omega] using hLast
    · simpa [coreArc, hmA, show middle < 13 by omega,
        show 8 + r < 15 by omega] using hLast
  have hNot' : ¬G.Adj (labelledVertex G L (8 + p))
      (labelledVertex G L (8 + r)) := by
    apply decide_eq_false_iff_not.mp
    rw [← coreArc_graph G C L hG (8 + p) (8 + r) (by omega) (by omega)]
    simpa [coreArc, show ¬8 + p < 8 by omega,
      show 8 + p < 13 by omega, show 8 + r < 15 by omega] using hNot
  have hneV : (L.p ⟨r, hr⟩).1 ≠ (L.p ⟨p, hp⟩).1 := by
    intro heq
    apply hne
    have hfin : (⟨r, hr⟩ : Fin 5) = ⟨p, hp⟩ := by
      apply L.p.injective
      exact Subtype.ext heq
    exact congrArg (fun n : Nat ↦ 8 + n) (Fin.ext_iff.mp hfin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  have hFirst'' : G.Adj (L.p ⟨p, hp⟩).1 (labelledVertex G L middle) := by
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 13 by omega] using hFirst'
  have hNot'' : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.p ⟨r, hr⟩).1 := by
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 13 by omega, show ¬8 + r < 8 by omega,
      show 8 + r < 13 by omega] using hNot'
  have hLast'' : G.Adj (labelledVertex G L middle) (L.p ⟨r, hr⟩).1 := by
    simpa [labelledVertex, show ¬8 + r < 8 by omega,
      show 8 + r < 13 by omega] using hLast'
  refine ⟨⟨labelledVertex G L middle, hFirst'', hLast''⟩, hNot'', ?_⟩
  simpa [labelledVertex, show ¬8 + r < 8 by omega,
    show 8 + r < 13 by omega, show ¬8 + p < 8 by omega,
    show 8 + p < 13 by omega] using hneV

set_option maxHeartbeats 5000000 in
theorem pSecondPCount_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (p : Nat) (hp : p < 5) :
    (pSecondPCount (graphArc G L) p).toNat ≤
      (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.count_le_filterCard
    C.P L.p (fun r ↦ strictSecondLocal (graphArc G L) (8 + p) (8 + r))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1) (by omega)
  intro r hr'
  exact pStrictSecond_true_mem G C L hG p r hp r.isLt hr'

set_option maxHeartbeats 5000000 in
theorem pEffectiveConditions_true {zCount yValue : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hzLe : zCount ≤ 2) (hy : BSevenKThree.y G C = yValue)
    (he : yValue + zCount = 3)
    (hmBound :
      (externalMissing zCount (graphArc G L) (graphPToZ G L)).toNat ≤ 3) :
    all 5 (pEffectiveCondition zCount (graphArc G L) (graphPToZ G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hBlocks := pBlockCounts G C L hHCard (by omega) p hp
  have hAux := pAuxOut_to_auxiliary G C L hHCard hzLe p hp
  have hTable := individualEffectiveLower_graph G C L hG hMin hHCard hzLe
    hy he hmBound p hp
  have hPS := pSecondPCount_le_graph G C L hG p hp
  have hEeq : auxiliarySet G C =
      SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet G C := by
    rfl
  have hUnion :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG (auxiliarySet G C) hEeq v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩)
  have hDegree := P_outdegree_eq_blocks G C L hG p hp
  have hDegreeE : G.outdegree v = directCount G C.P v + directCount G C.H v +
      directCount G (auxiliarySet G C) v := by
    dsimp only [v] at hvP ⊢
    have hDis : Disjoint (BSevenKThree.reachedQ G C) (externalTargets G C) := by
      apply Finset.disjoint_of_subset_left Finset.inter_subset_left
      apply Finset.disjoint_of_subset_left
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      exact BSixKThree.disjoint_B_externalTargets G C
    rw [hDegree, directCount_Q_eq_reachedQ G C (L.p ⟨p, hp⟩).1 (L.p _).2]
    change _ = _ + _ + directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1
    rw [auxiliarySet, directCount_union_of_disjoint G _ _
      (L.p ⟨p, hp⟩).1 hDis]
    omega
  have hNatural :
      (pSecondPCount (graphArc G L) p).toNat +
          (individualEffectiveLower zCount (graphArc G L)
            (graphPToZ G L) p).toNat + 1 ≤
        (pOut (graphArc G L) p).toNat +
          2 * (pHOut (graphArc G L) p).toNat +
            (pAuxOut zCount (graphArc G L) (graphPToZ G L) p).toNat := by
    have hUnion' := hUnion
    change (C.P.filter fun w ↦ w ∈ G.secondOutNeighborFinset v).card +
        (directAuxEffectiveUnion G C (auxiliarySet G C) v).card ≤
          G.secondOutdegree v + directCount G C.H v at hUnion'
    dsimp only [v] at hPS hTable hNS hAux hDegreeE hUnion' ⊢
    rw [hBlocks.1, hBlocks.2.1, hAux]
    omega
  unfold pEffectiveCondition
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  have hTableLe := individualEffectiveTable_toNat_le
    (externalMissing zCount (graphArc G L) (graphPToZ G L))
    (pAuxOut zCount (graphArc G L) (graphPToZ G L) p)
  have hPSLe : (pSecondPCount (graphArc G L) p).toNat ≤ 5 := by
    exact hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hPLe : (pOut (graphArc G L) p).toNat ≤ 5 := by
    rw [hBlocks.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut (graphArc G L) p).toNat ≤ 7 := by
    rw [hBlocks.2.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hAuxLe : (pAuxOut zCount (graphArc G L) (graphPToZ G L) p).toNat ≤ 3 := by
    rw [hAux]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa [he] using auxiliarySet_card G C L hy)
  have h1 : (1 : BitVec 8).toNat = 1 := by decide
  have h2 : (2 : BitVec 8).toNat = 2 := by decide
  rw [h1, h2]
  repeat' rw [Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.EffectiveBridge
