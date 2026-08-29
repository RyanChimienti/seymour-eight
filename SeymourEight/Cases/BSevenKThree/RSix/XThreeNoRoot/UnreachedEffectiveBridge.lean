import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.UnreachedAssembly
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Unreached

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedEffectiveBridge

open Shared Shared.FiniteCore Labels UnreachedEncoding Core UnreachedCore
  UnreachedGraphFacts UnreachedAssembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev auxiliarySet (C : G.LocalConfiguration) : Finset V :=
  externalTargets G C

abbrev directAuxNeighbors (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxNeighbors G E p

abbrev directAuxEffectiveUnion (C : G.LocalConfiguration)
    (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffectiveUnion G C E p

theorem auxiliarySet_card {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : (auxiliarySet G C).card = zCount := by
  simpa using (Fintype.card_congr L.z).symm

theorem auxiliarySet_disjoint_P (C : G.LocalConfiguration) :
    Disjoint (auxiliarySet G C) C.P := by
  exact Finset.disjoint_of_subset_right
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
    (BSixKThree.disjoint_B_externalTargets G C).symm

theorem auxiliarySet_eq_reached {zCount : Nat} (C : G.LocalConfiguration)
    (_L : Labels G zCount C) (hy : BSevenKThree.y G C = 0) :
    auxiliarySet G C =
      SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet G C := by
  have hReachedCard : (reachedQ G C).card = 0 := hy
  have hReached : reachedQ G C = ∅ := Finset.card_eq_zero.mp hReachedCard
  have hCross : BSevenKTwo.reachedQ G C = reachedQ G C := by rfl
  rw [SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet,
    hCross, hReached]
  simp [auxiliarySet]

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      norm_num

theorem totalPAux_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    (UnreachedCore.totalPZ zCount
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L))).toNat =
      edgeCount G C.P (auxiliarySet G C) := by
  have hEach : ∀ i : Fin 6,
      (pZOut zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) i).toNat =
        directCount G (auxiliarySet G C) (L.p i).1 := by
    intro i
    exact pZOut_toNat G C L hG hzLe i i.isLt
  have hSum : (∑ i ∈ Finset.range 6,
      (pZOut zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) i).toNat) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [edgeCount_eq_sum_fin G C.P (auxiliarySet G C) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [UnreachedCore.totalPZ, toNat_sumCount, hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hP : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hP, auxiliarySet_card G C L] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 5) :
    (UnreachedCore.externalMissing zCount
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L))).toNat =
      6 * zCount - edgeCount G C.P (auxiliarySet G C) := by
  rw [UnreachedCore.externalMissing, BitVec.toNat_sub,
    totalPAux_toNat G C L hG hzLe]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hP : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hP, auxiliarySet_card G C L] at hCap
  norm_num [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 5000000 in
theorem genericEffective_toNat_le (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) :
    (UnreachedCore.genericEffective zCount arc p).toNat ≤ 12 := by
  by_cases hz : zCount = 4
  · rw [UnreachedCore.genericEffective, if_pos hz]
    have hb : (UnreachedCore.genericEffectiveFour arc p).ule (12 : BitVec 8) = true := by
      unfold UnreachedCore.genericEffectiveFour effectiveAt
      bv_decide
    rw [BitVec.ule_eq_decide] at hb
    norm_num [BitVec.toNat_ofNat] at hb
    exact hb
  · rw [UnreachedCore.genericEffective, if_neg hz]
    have hb : (UnreachedCore.genericEffectiveFive arc p).ule (12 : BitVec 8) = true := by
      unfold UnreachedCore.genericEffectiveFive effectiveAt
      bv_decide
    rw [BitVec.ule_eq_decide] at hb
    norm_num [BitVec.toNat_ofNat] at hb
    exact hb

theorem externalMissing_bound {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hRootDegree : G.outdegree C.s = 8)
    (hHCard : C.H.card = 6) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 3) (hy : BSevenKThree.y G C = 0)
    (hz : zCount = 4 ∨ zCount = 5) :
    (UnreachedCore.externalMissing zCount
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L))).toNat ≤ 9 := by
  have hQCard : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hRCard : C.R.card = 1 := by
    rw [BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk, hx]
  have hHCap := BSixKThree.H_degree_capacity_general G C hG hMin hk
  have hPCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hySix : BSixKThree.y G C = 0 := by
    simpa [BSixKThree.y, BSixKThree.Y, BSevenKThree.y,
      BSevenKThree.reachedQ] using hy
  rw [hHCard, hx, hRCard, hQCard, hySix] at hHCap
  rw [hHCard] at hPCap
  simp [Nat.choose] at hHCap
  have hReachedEq : edgeCount G C.P (reachedQ G C) =
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
  have hReachedCard : (reachedQ G C).card = 0 := hy
  have hReachedZero : edgeCount G C.P (reachedQ G C) = 0 := by
    have hCap := edgeCount_le_card_mul_card G C.P (reachedQ G C)
    rw [hReachedCard] at hCap
    omega
  have hAuxEdge : 21 ≤ edgeCount G C.P (auxiliarySet G C) := by
    dsimp [auxiliarySet]
    omega
  rw [externalMissing_toNat G C L hG (by omega)]
  omega

set_option maxHeartbeats 5000000 in
-- The interval enumeration below checks all small missing-edge and row-size cases.
theorem genericEffective_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hz : zCount = 4 ∨ zCount = 5)
    (hmBound :
      (UnreachedCore.externalMissing zCount
        (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L))).toNat ≤ 9)
    (p : Nat) (hp : p < 6) :
    (UnreachedCore.genericEffective zCount
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C)
        (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  let e := zCount
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
      (UnreachedCore.externalMissing zCount
        (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L))).toNat = m := by
    simpa [m, e, E] using externalMissing_toNat G C L hG (by omega)
  have hSN :
      (pZOut zCount
        (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat = s := by
    rw [pZOut_toNat G C L hG (by omega) p hp]
    rfl
  have hMBV : UnreachedCore.externalMissing zCount
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hMN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hmCap := edgeCount_le_card_mul_card G C.P E
    rw [hPCard, hECard] at hmCap
    rcases hz with rfl | rfl <;> omega
  have hSBV : pZOut zCount (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p =
      BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hSN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rcases hz with rfl | rfl <;> omega
  have hm : m ≤ 30 := by
    have hmCap := edgeCount_le_card_mul_card G C.P E
    rw [hPCard, hECard] at hmCap
    rcases hz with rfl | rfl <;> omega
  have hmTight : m ≤ 9 := by
    simpa [hMN] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (e - s) at hToP
  change (UnreachedCore.genericEffective zCount
    (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat ≤ U.card
  rcases hz with rfl | rfl
  · rw [UnreachedCore.genericEffective, if_pos rfl]
    simp only [UnreachedCore.genericEffectiveFour]
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
  · rw [UnreachedCore.genericEffective, if_neg (show 5 ≠ 4 by decide)]
    simp only [UnreachedCore.genericEffectiveFive]
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

set_option maxHeartbeats 5000000 in
-- Establishing every row condition expands the finite Boolean definitions substantially.
theorem pGenericEffective_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 6) (hy : BSevenKThree.y G C = 0)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3)
    (hz : zCount = 4 ∨ zCount = 5) :
    UnreachedCore.pGenericEffective zCount
      (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) = true := by
  rw [UnreachedCore.pGenericEffective, all_eq_true_iff]
  intro p hp
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hP := pOut_toNat G C L hG (by omega) p hp
  have hH := pHOut_toNat G C L hG (by omega) hHCard p hp
  have hAux := pZOut_toNat G C L hG (by omega) p hp
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
  have hQU := qUnreached_true G C L hG (by omega) hy
  have hNotQ : ¬G.Adj v (L.q 0).1 := by
    rw [UnreachedCore.qUnreached] at hQU
    simp only [Bool.and_eq_true, all_eq_true_iff] at hQU
    have hb := hQU.2 p hp
    rw [pToQ_graphBits G C L hG (by omega) p hp] at hb
    simpa [v] using hb
  have hQZero : directCount G C.Q v = 0 := by
    rw [hQ]
    simp [Shared.directCount_singleton, Shared.epsilonAt, hNotQ]
  have hDis : Disjoint C.Q (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  have hAuxSplit := directCount_union_of_disjoint G C.Q
    (externalTargets G C) v hDis
  rw [hQZero, Nat.zero_add] at hAuxSplit
  have hDegree :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG v hvP
  rw [← hQ] at hDegree
  rw [hAuxSplit] at hDegree
  have hNatural :
      (pSecondP (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat +
          (UnreachedCore.genericEffective zCount
            (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat +
            1 ≤
        (pOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat +
          2 * (pHOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat +
            (pZOut zCount
              (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat := by
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
  have hPSLe :
      (pSecondP (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat ≤ 6 :=
    hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hTableLe := genericEffective_toNat_le zCount
    (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p
  have hPLe :
      (pOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat ≤ 6 := by
    rw [hP]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe :
      (pHOut (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat ≤ 6 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hAuxLe :
      (pZOut zCount
        (UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)) p).toNat ≤ 5 := by
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

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedEffectiveBridge
