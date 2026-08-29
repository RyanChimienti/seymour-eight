import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev auxiliarySet (G : Digraph V) [DecidableRel G.Adj]
    (C : G.LocalConfiguration) : Finset V :=
  BSevenKThree.reachedQ G C ∪ externalTargets G C

theorem auxiliarySet_eq {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (yValue : Nat) (hy : BSevenKThree.y G C = yValue)
    (hyCases : yValue = 0 ∨ yValue = 1) :
    auxiliarySet G C =
      if yValue = 0 then (externalTargets G C) else {(L.q 0).1} ∪ (externalTargets G C) := by
  have hQ := qSingleton G C L
  rcases hyCases with rfl | rfl
  · have hReached : reachedQ G C = ∅ := Finset.card_eq_zero.mp hy
    simp [auxiliarySet, hReached]
  · have hSub : reachedQ G C ⊆ C.Q := Finset.inter_subset_left
    have hReachedCard : (reachedQ G C).card = 1 := by
      simpa [BSevenKThree.y] using hy
    have hQCard : C.Q.card = 1 := by
      simpa using (Fintype.card_congr L.q).symm
    have hReached : reachedQ G C = C.Q :=
      Finset.eq_of_subset_of_card_le hSub (by omega)
    simp [auxiliarySet, hReached, hQ]

theorem auxiliarySet_card {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C)
    (yValue : Nat) (hy : BSevenKThree.y G C = yValue)
    (hyCases : yValue = 0 ∨ yValue = 1) :
    (auxiliarySet G C).card = yValue + zCount := by
  rw [auxiliarySet_eq G C L yValue hy hyCases]
  have hz : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
  rcases hyCases with rfl | rfl
  · simp [hz]
  · have hDis : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvQ hvZ
      have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
      subst v
      exact (Finset.disjoint_left.mp
        (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
    simp only [if_neg (by omega : ¬1 = 0)]
    rw [Finset.card_union_of_disjoint hDis]
    simp [hz]

theorem auxiliarySet_disjoint_P (C : G.LocalConfiguration) :
    Disjoint (auxiliarySet G C) C.P := by
  rw [Finset.disjoint_left]
  intro v hvE hvP
  rcases Finset.mem_union.mp hvE with hvQ | hvExt
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
        (Finset.mem_inter.mp hvQ).1
  · rcases Finset.mem_union.mp hvExt with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
      · simp [rootSecondFinset, hReach] at hvRoot

theorem pAuxOut_to_auxiliary {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (yValue : Nat)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) (p : Nat) (hp : p < 6) :
    (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) p).toNat =
      directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1 := by
  have hAux := pAuxOut_toNat G C L hG hHCard yValue hy hyCases hzLe p hp
  have hE := auxiliarySet_eq G C L yValue hy hyCases
  rcases hyCases with rfl | rfl
  · rw [if_pos rfl] at hE
    rw [hE]
    have hEmpty : reachedQ G C = ∅ := Finset.card_eq_zero.mp hy
    have hn : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 := by
      intro ha
      have hm : (L.q 0).1 ∈ reachedQ G C := Finset.mem_inter.mpr ⟨(L.q 0).2,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨_, Finset.mem_union_right C.A1 (L.p _).2, ha⟩⟩
      simp [hEmpty] at hm
    have hZero : directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 = 0 := by
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hn]
    have hDis := auxiliarySet_disjoint_P G C
    have hqz : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvQ hvZ
      have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
      subst v
      exact (Finset.disjoint_left.mp
        (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
    rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hqz, hZero,
      Nat.zero_add] at hAux
    exact hAux
  · rw [if_neg (by omega)] at hE
    rw [hE]
    exact hAux

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      norm_num

theorem totalPToAux_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (yValue : Nat)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) :
    (totalPToAux yValue zCount (graphArc G L) (graphPToZ G L)).toNat =
      edgeCount G C.P (auxiliarySet G C) := by
  have hEach : ∀ i : Fin 6,
      (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) i).toNat =
        directCount G (auxiliarySet G C) (L.p i).1 := by
    intro i
    exact pAuxOut_to_auxiliary G C L hG hHCard yValue hy hyCases
      hzLe i i.isLt
  have hSum : (∑ i ∈ Finset.range 6,
      (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) i).toNat) =
        edgeCount G C.P (auxiliarySet G C) := by
    rw [edgeCount_eq_sum_fin G C.P (auxiliarySet G C) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  have hTotal : totalPToAux yValue zCount (graphArc G L) (graphPToZ G L) =
      sumCount 6 (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L)) := by
    rcases hyCases with rfl | rfl
    · simp [totalPToAux, pAuxOut, totalPToZ, sumCount]
    · simp only [totalPToAux, if_neg (by omega : ¬1 = 0), totalPToZ,
        totalPToQ, pAuxOut, sumCount, count, bitCount]
      ac_rfl
  rw [hTotal, toNat_sumCount, hSum]
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard := auxiliarySet_card G C L yValue hy hyCases
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  rw [hPCard, hECard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (yValue : Nat)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) :
    (externalMissing yValue zCount (graphArc G L) (graphPToZ G L)).toNat =
      6 * (yValue + zCount) -
        edgeCount G C.P (auxiliarySet G C) := by
  rw [externalMissing, BitVec.toNat_sub,
    totalPToAux_toNat G C L hG hHCard yValue hy hyCases hzLe]
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard := auxiliarySet_card G C L yValue hy hyCases
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  rw [hPCard, hECard] at hCap
  norm_num [BitVec.toNat_ofNat]
  omega

theorem edgeCount_P_auxiliary_eq (C : G.LocalConfiguration) :
    edgeCount G C.P (auxiliarySet G C) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
  have hReached : edgeCount G C.P (BSevenKThree.reachedQ G C) =
      edgeCount G C.P C.Q := by
    unfold edgeCount
    apply Finset.sum_congr rfl
    intro p hp
    unfold directCount CertificateBridge.internalFirstNeighbors
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨(Finset.mem_inter.mp h.1).1, h.2⟩
    · intro h
      exact ⟨Finset.mem_inter.mpr ⟨h.1,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨p, Finset.mem_union_right C.A1 hp, h.2⟩⟩, h.2⟩
  have hDis : Disjoint (BSevenKThree.reachedQ G C) (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left Finset.inter_subset_left
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  change edgeCount G C.P
      (BSevenKThree.reachedQ G C ∪ externalTargets G C) = _
  rw [edgeCount_union_of_disjoint G C.P _ _ hDis, hReached]

theorem externalMissing_le_nine {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 4) (yValue : Nat) (hy : BSevenKThree.y G C = yValue)
    (hyCases : yValue = 0 ∨ yValue = 1) (hzLe : zCount ≤ 4)
    (he : yValue + zCount = 3 ∨ yValue + zCount = 4) :
    (externalMissing yValue zCount (graphArc G L) (graphPToZ G L)).toNat ≤ 9 := by
  have hQCard : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hRCard : C.R.card = 0 := by
    rw [BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk, hx]
  have hHCap := BSixKThree.H_degree_capacity_general G C hG hMin hk
  have hPCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hySix : BSixKThree.y G C = yValue := by
    simpa [BSixKThree.y, BSixKThree.Y, BSevenKThree.y,
      BSevenKThree.reachedQ] using hy
  rw [hHCard, hx, hRCard, hQCard, hySix] at hHCap
  simp [Nat.choose] at hHCap
  have hTarget : 15 ≤ edgeCount G C.P C.Q +
      edgeCount G C.P (externalTargets G C) := by
    omega
  have hAux := edgeCount_P_auxiliary_eq G C
  have hMissing := externalMissing_toNat G C L hG hHCard
    yValue hy hyCases hzLe
  rw [hAux] at hMissing
  rw [hMissing]
  rcases he with he | he <;> omega

set_option maxHeartbeats 5000000 in
-- This is a finite normalization of the two small lookup tables.
theorem individualEffectiveTable_toNat_le (four : Bool) (m s : BitVec 8) :
    (individualEffectiveTable four m s).toNat ≤ 11 := by
  have h : (individualEffectiveTable four m s).ule (11 : BitVec 8) = true := by
    simp only [individualEffectiveTable, effectiveAtRowSize]
    bv_decide
  simpa [BitVec.ule_eq_decide] using h

abbrev directAuxNeighbors (G : Digraph V) [DecidableRel G.Adj]
    (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxNeighbors G E p

abbrev directAuxEffectiveUnion (G : Digraph V) [DecidableRel G.Adj]
    (C : G.LocalConfiguration) (E : Finset V)
    (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffectiveUnion G C E p

theorem directAux_to_P_capacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (E : Finset V)
    (hPCard : C.P.card = 6) (eCount : Nat) (hECard : E.card = eCount)
    (p : V) (hpP : p ∈ C.P) :
    edgeCount G (directAuxNeighbors G E p) C.P ≤
      (6 * eCount - edgeCount G C.P E) -
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
  have hPT : edgeCount G C.P T ≤ 5 * T.card := by
    calc
      edgeCount G C.P T ≤ ∑ q ∈ C.P, if q = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqp : q = p
        · subst q
          simp [hpT]
        · simp only [hqp, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 * T.card := by
        rw [← Finset.sum_erase_add C.P
          (fun q ↦ if q = p then 0 else T.card) hpP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ q ∈ C.P.erase p, if q = p then 0 else T.card) =
              ∑ _q ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [if_neg (Finset.mem_erase.mp hq).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 5 * T.card := by
            rw [Finset.card_erase_of_mem hpP, hPCard]
  have hPESplit : edgeCount G C.P E =
      edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = eCount := by
    rw [hTCard]
    have hSLe : S.card ≤ eCount := (Finset.card_le_card hS).trans_eq hECard
    omega
  have hPEUpper := edgeCount_le_card_mul_card G C.P E
  rw [hPCard, hECard] at hPEUpper
  change edgeCount G S C.P ≤
    (6 * eCount - edgeCount G C.P E) - (eCount - S.card)
  omega

set_option maxHeartbeats 5000000 in
theorem individualEffectiveLower_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (yValue : Nat)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) (he : yValue + zCount = 3 ∨ yValue + zCount = 4)
    (hmBound :
      (externalMissing yValue zCount (graphArc G L) (graphPToZ G L)).toNat ≤ 9)
    (p : Nat) (hp : p < 6) :
    (individualEffectiveLower yValue zCount (graphArc G L) (graphPToZ G L) p).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C) (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  let e := yValue + zCount
  let m := 6 * e - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = e := by
    simpa [E, e] using auxiliarySet_card G C L yValue hy hyCases
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ e :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hRow : e - s ≤ m := by
    have hOther : ∑ q ∈ C.P.erase v, directCount G E q ≤ 5 * e := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase v, e := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 5 * e := by simp [Finset.card_erase_of_mem hvP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (directCount G E) hvP
    have hSCard : s = directCount G E v := rfl
    have hEdge : edgeCount G C.P E =
        (∑ q ∈ C.P.erase v, directCount G E q) + directCount G E v := by
      unfold edgeCount
      omega
    dsimp [m]
    omega
  have hLower :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffective_capacity_lower
      G C hMin E (auxiliarySet_disjoint_P G C) v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directAux_to_P_capacity G C hG E hPCard e hECard v hvP
  have hMN :
      (externalMissing yValue zCount (graphArc G L) (graphPToZ G L)).toNat = m := by
    simpa [m, e, E] using
      externalMissing_toNat G C L hG hHCard yValue hy hyCases hzLe
  have hSN :
      (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) p).toNat = s := by
    rw [pAuxOut_to_auxiliary G C L hG hHCard yValue hy hyCases hzLe p hp]
    rfl
  have hMBV : externalMissing yValue zCount (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hMN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hSBV : pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) p =
      BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hSN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : m ≤ 9 := by simpa [hMN] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (e - s) at hToP
  change (individualEffectiveLower yValue zCount (graphArc G L)
    (graphPToZ G L) p).toNat ≤ U.card
  simp only [individualEffectiveLower, individualEffectiveTable]
  rw [hMBV, hSBV]
  rcases he with he | he
  · have he' : e = 3 := by simpa [e] using he
    rw [he'] at hs hRow hToP
    simp only [he]
    interval_cases m <;> interval_cases s <;>
      simp [effectiveAtRowSize, Nat.choose, BitVec.toNat_ofNat]
        at hm hs hRow hInternal hToP hLower ⊢ <;>
      omega
  · have he' : e = 4 := by simpa [e] using he
    rw [he'] at hs hRow hToP
    simp only [he, decide_true, if_true]
    interval_cases m <;> interval_cases s <;>
      simp [effectiveAtRowSize, Nat.choose, BitVec.toNat_ofNat]
        at hm hs hRow hInternal hToP hLower ⊢ <;>
      omega

set_option maxHeartbeats 5000000 in
-- The finite table normalization generates one small goal per nested branch.
theorem pEffectiveConditions_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 7)
    (yValue : Nat) (hy : BSevenKThree.y G C = yValue)
    (hyCases : yValue = 0 ∨ yValue = 1) (hzLe : zCount ≤ 4)
    (he : yValue + zCount = 3 ∨ yValue + zCount = 4)
    (hmBound :
      (externalMissing yValue zCount (graphArc G L) (graphPToZ G L)).toNat ≤ 9) :
    all 6 (pEffectiveCondition yValue zCount (graphArc G L) (graphPToZ G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hBlocks := pBlockCounts G C L hG hHCard (by omega) p hp
  have hAux := pAuxOut_to_auxiliary G C L hG hHCard yValue hy hyCases
    hzLe p hp
  have hTable := individualEffectiveLower_graph G C L hG hMin hHCard
    yValue hy hyCases hzLe he hmBound p hp
  have hPS := pSecondPCount_le_graph G C L hG p hp
  have hEeq : E =
      SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet G C := by rfl
  have hUnion :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG E hEeq v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩)
  have hQ := qSingleton G C L
  have hDegree :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG v hvP
  have hEGraph := auxiliarySet_eq G C L yValue hy hyCases
  have hDegreeE : G.outdegree v = directCount G C.P v + directCount G C.H v +
      directCount G E v := by
    dsimp only [E]
    rcases hyCases with rfl | rfl
    · rw [if_pos rfl] at hEGraph
      rw [hEGraph]
      have hReached : reachedQ G C = ∅ := Finset.card_eq_zero.mp hy
      have hn : ¬G.Adj v (L.q 0).1 := by
        intro ha
        have hm : (L.q 0).1 ∈ reachedQ G C := Finset.mem_inter.mpr ⟨(L.q 0).2,
          (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
            ⟨v, Finset.mem_union_right C.A1 hvP, ha⟩⟩
        simp [hReached] at hm
      have hqz : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
        rw [Finset.disjoint_left]
        intro w hwQ hwZ
        have hw : w = (L.q 0).1 := Finset.mem_singleton.mp hwQ
        subst w
        exact (Finset.disjoint_left.mp
          (BSixKThree.disjoint_B_externalTargets G C))
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hwZ
      have hZero : directCount G {(L.q 0).1} v = 0 := by
        simp [directCount, CertificateBridge.internalFirstNeighbors,
          Finset.filter_singleton, hn]
      rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) v hqz, hZero,
        Nat.zero_add] at hDegree
      exact hDegree
    · rw [if_neg (by omega)] at hEGraph
      rw [hEGraph]
      exact hDegree
  have hNatural :
      (pSecondPCount (graphArc G L) p).toNat +
          (individualEffectiveLower yValue zCount (graphArc G L)
            (graphPToZ G L) p).toNat + 1 ≤
        (pOut (graphArc G L) p).toNat +
          2 * (pHOut (graphArc G L) p).toNat +
            (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) p).toNat := by
    have hDegreeE' : G.outdegree (L.p ⟨p, hp⟩).1 =
        directCount G C.P (L.p ⟨p, hp⟩).1 +
          directCount G C.H (L.p ⟨p, hp⟩).1 +
            directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1 := by
      simpa [v, E] using hDegreeE
    have hUnion' := hUnion
    change (C.P.filter fun w ↦
        w ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card +
          (directAuxEffectiveUnion G C (auxiliarySet G C)
            (L.p ⟨p, hp⟩).1).card ≤
        G.secondOutdegree (L.p ⟨p, hp⟩).1 +
          directCount G C.H (L.p ⟨p, hp⟩).1 at hUnion'
    dsimp [v, E] at hPS hTable hNS hAux
    rw [hBlocks.1, hBlocks.2.1, hAux]
    omega
  unfold pEffectiveCondition
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  have hPSLe : (pSecondPCount (graphArc G L) p).toNat ≤ 6 :=
    hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hTableLe : (individualEffectiveLower yValue zCount (graphArc G L)
      (graphPToZ G L) p).toNat ≤ 11 := by
    exact individualEffectiveTable_toNat_le _ _ _
  have hPLe : (pOut (graphArc G L) p).toNat ≤ 6 := by
    rw [hBlocks.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut (graphArc G L) p).toNat ≤ 7 := by
    rw [hBlocks.2.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hECard := auxiliarySet_card G C L yValue hy hyCases
  have hAuxLe : (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) p).toNat ≤ 4 := by
    rw [hAux]
    exact ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard).trans
      (by rcases he with he | he <;> omega)
  have hOne : (1 : BitVec 8).toNat = 1 := by decide
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  rw [hOne, hTwo]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge
