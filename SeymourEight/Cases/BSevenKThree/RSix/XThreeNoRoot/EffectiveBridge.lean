import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.Assembly
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Reduced

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.EffectiveBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev auxiliarySet (C : G.LocalConfiguration) : Finset V :=
  C.Q ∪ externalTargets G C

abbrev directAuxNeighbors (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxNeighbors G E p

abbrev directAuxEffectiveUnion (C : G.LocalConfiguration)
    (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffectiveUnion G C E p

theorem auxiliarySet_card {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : (auxiliarySet G C).card = 1 + zCount := by
  have hDis : Disjoint C.Q (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [Finset.card_union_of_disjoint hDis]
  have hQ : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hZ : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  omega

theorem auxiliarySet_disjoint_P (C : G.LocalConfiguration) :
    Disjoint (auxiliarySet G C) C.P := by
  rw [Finset.disjoint_left]
  intro v hvE hvP
  rcases Finset.mem_union.mp hvE with hvQ | hvExt
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hvQ
  · exact (Finset.disjoint_left.mp
      (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExt

theorem auxiliarySet_eq_reached {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hy : BSevenKThree.y G C = 1) :
    auxiliarySet G C =
      SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet G C := by
  have hSub : reachedQ G C ⊆ C.Q := Finset.inter_subset_left
  have hReachedCard : (reachedQ G C).card = 1 := hy
  have hQCard : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hReached : reachedQ G C = C.Q :=
    Finset.eq_of_subset_of_card_le hSub (by omega)
  have hCross : BSevenKTwo.reachedQ G C = reachedQ G C := by rfl
  rw [SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet,
    hCross, hReached]

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      norm_num

theorem totalPAux_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4) :
    (totalPAux zCount (encodedArc (graphBits G L))).toNat =
      edgeCount G C.P (auxiliarySet G C) := by
  have hEach : ∀ i : Fin 6,
      (pAuxOut zCount (encodedArc (graphBits G L)) i).toNat =
        directCount G (auxiliarySet G C) (L.p i).1 := by
    intro i
    exact pAuxOut_toNat G C L hG hzLe i i.isLt
  have hSum : (∑ i ∈ Finset.range 6,
      (pAuxOut zCount (encodedArc (graphBits G L)) i).toNat) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [edgeCount_eq_sum_fin G C.P (auxiliarySet G C) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [totalPAux, toNat_sumCount, hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hP : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hP, auxiliarySet_card G C L] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4) :
    (externalMissing zCount (encodedArc (graphBits G L))).toNat =
      6 * (1 + zCount) - edgeCount G C.P (auxiliarySet G C) := by
  rw [externalMissing, BitVec.toNat_sub,
    totalPAux_toNat G C L hG hzLe]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hP : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hP, auxiliarySet_card G C L] at hCap
  norm_num [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 5000000 in
theorem genericEffective_toNat_le (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) :
    (genericEffective zCount arc p).toNat ≤ 12 := by
  by_cases hz : zCount = 3
  · rw [genericEffective, if_pos hz]
    have hb : (genericEffectiveFour arc p).ule (12 : BitVec 8) = true := by
      unfold genericEffectiveFour effectiveAt
      bv_decide
    rw [BitVec.ule_eq_decide] at hb
    norm_num [BitVec.toNat_ofNat] at hb
    exact hb
  · rw [genericEffective, if_neg hz]
    have hb : (genericEffectiveFive arc p).ule (12 : BitVec 8) = true := by
      unfold genericEffectiveFive effectiveAt
      bv_decide
    rw [BitVec.ule_eq_decide] at hb
    norm_num [BitVec.toNat_ofNat] at hb
    exact hb

theorem externalMissing_bound {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hRootDegree : G.outdegree C.s = 8)
    (hHCard : C.H.card = 6) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 3) (hy : BSevenKThree.y G C = 1)
    (hz : zCount = 3 ∨ zCount = 4) :
    (externalMissing zCount (encodedArc (graphBits G L))).toNat ≤
      if zCount = 3 then 6 else 12 := by
  have hQCard : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hRCard : C.R.card = 1 := by
    rw [BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk, hx]
  have hHCap := BSixKThree.H_degree_capacity_general G C hG hMin hk
  have hPCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hySix : BSixKThree.y G C = 1 := by
    simpa [BSixKThree.y, BSixKThree.Y, BSevenKThree.y,
      BSevenKThree.reachedQ] using hy
  rw [hHCard, hx, hRCard, hQCard, hySix] at hHCap
  rw [hHCard] at hPCap
  simp [Nat.choose] at hHCap
  have hAuxEdge : 18 ≤ edgeCount G C.P (auxiliarySet G C) := by
    have hE : edgeCount G C.P (auxiliarySet G C) =
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
      rw [edgeCount_union_of_disjoint]
      apply Finset.disjoint_of_subset_left
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      exact BSixKThree.disjoint_B_externalTargets G C
    rw [hE]
    omega
  rw [externalMissing_toNat G C L hG (by omega)]
  rcases hz with rfl | rfl <;> simp <;> omega

set_option maxHeartbeats 5000000 in
-- The interval enumeration below checks all small missing-edge and row-size cases.
theorem genericEffective_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hz : zCount = 3 ∨ zCount = 4)
    (hmBound : (externalMissing zCount (encodedArc (graphBits G L))).toNat ≤
      if zCount = 3 then 6 else 12)
    (p : Nat) (hp : p < 6) :
    (genericEffective zCount (encodedArc (graphBits G L)) p).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C)
        (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  let e := 1 + zCount
  let m := 6 * e - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = e := by
    simpa [E, e] using auxiliarySet_card G C L
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hMDef : m = 6 * e - edgeCount G C.P E := rfl
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
    have hEdge : edgeCount G C.P E =
        (∑ q ∈ C.P.erase v, directCount G E q) + directCount G E v := by
      unfold edgeCount
      omega
    have hSCard : s = directCount G E v := rfl
    dsimp [m]
    omega
  have hPresent : s ≤ edgeCount G C.P E := by
    have hSplit := Finset.sum_erase_add C.P (directCount G E) hvP
    have hEdge : edgeCount G C.P E =
        (∑ q ∈ C.P.erase v, directCount G E q) + directCount G E v := by
      unfold edgeCount
      omega
    have hSCard : s = directCount G E v := rfl
    omega
  have hEdgeCap : edgeCount G C.P E ≤ 6 * e := by
    have h := edgeCount_le_card_mul_card G C.P E
    rw [hPCard, hECard] at h
    exact h
  have hMS : m + s ≤ 6 * e := by
    dsimp [m]
    omega
  have hLower :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffective_capacity_lower
      G C hMin E (auxiliarySet_disjoint_P G C) v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP :=
    SeymourEight.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge.directAux_to_P_capacity
      G C hG E hPCard e hECard v hvP
  have hMN :
      (externalMissing zCount (encodedArc (graphBits G L))).toNat = m := by
    simpa [m, e, E] using externalMissing_toNat G C L hG (by omega)
  have hSN :
      (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat = s := by
    rw [pAuxOut_toNat G C L hG (by omega) p hp]
    rfl
  have hMBV : externalMissing zCount (encodedArc (graphBits G L)) =
      BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hMN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hmCap := edgeCount_le_card_mul_card G C.P E
    rw [hPCard, hECard] at hmCap
    rcases hz with rfl | rfl <;> omega
  have hSBV : pAuxOut zCount (encodedArc (graphBits G L)) p =
      BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hSN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rcases hz with rfl | rfl <;> omega
  have hm : m ≤ 30 := by
    have hmCap := edgeCount_le_card_mul_card G C.P E
    rw [hPCard, hECard] at hmCap
    rcases hz with rfl | rfl <;> omega
  have hmTight : m ≤ if zCount = 3 then 6 else 12 := by
    simpa [hMN] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (e - s) at hToP
  change (genericEffective zCount (encodedArc (graphBits G L)) p).toNat ≤ U.card
  rcases hz with rfl | rfl
  · rw [genericEffective, if_pos rfl]
    simp only [genericEffectiveFour]
    rw [hMBV, hSBV]
    interval_cases m <;> interval_cases s <;>
      simp only [BEq.rfl, BitVec.ofNat_eq_ofNat, BitVec.reduceBEq,
        BitVec.toNat_ofNat, Bool.false_eq_true, Nat.add_one_sub_one, Nat.choose,
        Nat.not_ofNat_le_one, Nat.one_le_ofNat, Nat.reduceAdd, Nat.reduceLeDiff,
        Nat.reduceMod, Nat.reduceMul, Nat.reducePow, Nat.reduceSub,
        Nat.zero_mod, OfNat.ofNat_ne_zero, Std.le_refl, add_zero, e, effectiveAt,
        nonpos_iff_eq_zero, one_mul, one_ne_zero, tsub_le_iff_right, tsub_self,
        tsub_zero, zero_add, zero_le, zero_mul, ↓reduceIte]
        at hMDef hEdgeCap hm hmTight hSN hs hRow hMS hInternal hToP hLower ⊢ <;>
      omega
  · rw [genericEffective, if_neg (show 4 ≠ 3 by decide)]
    simp only [genericEffectiveFive]
    rw [hMBV, hSBV]
    interval_cases m <;> interval_cases s <;>
      simp only [BEq.rfl, BitVec.ofNat_eq_ofNat, BitVec.reduceBEq,
        BitVec.toNat_ofNat, Bool.false_eq_true, Nat.add_one_sub_one, Nat.choose,
        Nat.not_ofNat_le_one, Nat.one_le_ofNat, Nat.reduceAdd, Nat.reduceLeDiff,
        Nat.reduceMod, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.succ_ne_self,
        Nat.zero_mod, OfNat.ofNat_ne_zero, Std.le_refl, add_zero, e, effectiveAt,
        nonpos_iff_eq_zero, one_mul, one_ne_zero, tsub_le_iff_right, tsub_self,
        tsub_zero, zero_add, zero_le, zero_mul, ↓reduceIte]
        at hMDef hEdgeCap hm hmTight hSN hs hRow hMS hInternal hToP hLower ⊢ <;>
      omega

set_option maxHeartbeats 5000000 in
-- Establishing every row condition expands the finite Boolean definitions substantially.
theorem pGenericEffective_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 6) (hy : BSevenKThree.y G C = 1)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3)
    (hz : zCount = 3 ∨ zCount = 4) :
    pGenericEffective zCount (encodedArc (graphBits G L)) = true := by
  rw [pGenericEffective, all_eq_true_iff]
  intro p hp
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hP := pOut_toNat G C L hG (by omega) p hp
  have hH := pHOut_toNat G C L hG (by omega) hHCard p hp
  have hAux := pAuxOut_toNat G C L hG (by omega) p hp
  have hmBound := externalMissing_bound G C L hG hMin hRootDegree hHCard
    hk hr hx hy hz
  have hTable := genericEffective_graph G C L hG hMin hz hmBound p hp
  have hPS := pSecondP_le_graph G C L hG (by omega) p hp
  have hEeq := auxiliarySet_eq_reached G C L hy
  have hUnion :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG E hEeq v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩)
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro w hw
    obtain ⟨i, hi⟩ := L.q.surjective ⟨w, hw⟩
    simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
  have hDegree :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG v hvP
  rw [← hQ] at hDegree
  have hNatural :
      (pSecondP (encodedArc (graphBits G L)) p).toNat +
          (genericEffective zCount (encodedArc (graphBits G L)) p).toNat + 1 ≤
        (pOut (encodedArc (graphBits G L)) p).toNat +
          2 * (pHOut (encodedArc (graphBits G L)) p).toNat +
            (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat := by
    have hUnion' := hUnion
    change (C.P.filter fun w ↦
        w ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card +
          (directAuxEffectiveUnion G C (auxiliarySet G C)
            (L.p ⟨p, hp⟩).1).card ≤
        G.secondOutdegree (L.p ⟨p, hp⟩).1 +
          directCount G C.H (L.p ⟨p, hp⟩).1 at hUnion'
    dsimp [v, E] at hPS hTable hNS hAux hDegree
    rw [hP, hH, hAux]
    omega
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  have hPSLe : (pSecondP (encodedArc (graphBits G L)) p).toNat ≤ 6 :=
    hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hTableLe := genericEffective_toNat_le zCount (encodedArc (graphBits G L)) p
  have hPLe : (pOut (encodedArc (graphBits G L)) p).toNat ≤ 6 := by
    rw [hP]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut (encodedArc (graphBits G L)) p).toNat ≤ 6 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hAuxLe : (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat ≤ 5 := by
    rw [hAux]
    exact ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (auxiliarySet_card G C L)).trans (by rcases hz with rfl | rfl <;> omega)
  have hOne : (1 : BitVec 8).toNat = 1 := by decide
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  rw [hOne, hTwo]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.EffectiveBridge
