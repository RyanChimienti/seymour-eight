import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.AugmentedBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.EffectiveBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def auxiliarySet (C : G.LocalConfiguration) : Finset V :=
  BSevenKThree.reachedQ G C ∪ externalTargets G C

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

theorem pAuxOut_to_auxiliary {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (p : Nat) (hp : p < 5) :
    (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat =
      directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1 := by
  rw [pAuxOut_toNat G C L hG hzLe p hp,
    directCount_union_of_disjoint G C.Q (externalTargets G C) _
      (by
        apply Finset.disjoint_of_subset_left
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
        exact BSixKThree.disjoint_B_externalTargets G C),
    directCount_Q_eq_reachedQ G C _ (L.p _).2]
  rw [auxiliarySet]
  exact (directCount_union_of_disjoint G _ _ _ (by
    apply Finset.disjoint_of_subset_left Finset.inter_subset_left
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C)).symm

theorem totalPAux_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3) :
    (totalPAux zCount (encodedArc (graphBits G L))).toNat =
      edgeCount G C.P (auxiliarySet G C) := by
  rw [totalPAux, AugmentedBridge.toNat_sumCount]
  have hEq : (∑ i ∈ Finset.range 5,
      (pAuxOut zCount (encodedArc (graphBits G L)) i).toNat) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [← Fin.sum_univ_eq_sum_range,
      edgeCount_eq_sum_fin G C.P (auxiliarySet G C) L.p]
    apply Finset.sum_congr rfl
    intro p _
    exact pAuxOut_to_auxiliary G C L hG hzLe p p.isLt
  rw [Nat.mod_eq_of_lt, hEq]
  rw [hEq]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQ : (BSevenKThree.reachedQ G C).card ≤ 2 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (by simpa using (Fintype.card_congr L.q).symm)
  have hZ : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hAux : (auxiliarySet G C).card ≤ 5 := by
    rw [auxiliarySet, Finset.card_union_of_disjoint (by
      apply Finset.disjoint_of_subset_left Finset.inter_subset_left
      apply Finset.disjoint_of_subset_left
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      exact BSixKThree.disjoint_B_externalTargets G C), hZ]
    omega
  rw [hp] at hCap
  omega

theorem externalMissing_toNat {zCount yValue : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hy : BSevenKThree.y G C = yValue) (heLe : yValue + zCount ≤ 4) :
    (externalMissing yValue zCount (encodedArc (graphBits G L))).toNat =
      5 * (yValue + zCount) - edgeCount G C.P (auxiliarySet G C) := by
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  rw [hp, auxiliarySet_card G C L hy] at hCap
  have hConst : (BitVec.ofNat 8 (5 * (yValue + zCount))).toNat =
      5 * (yValue + zCount) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hLe : totalPAux zCount (encodedArc (graphBits G L)) ≤
      BitVec.ofNat 8 (5 * (yValue + zCount)) := by
    rw [BitVec.le_def, totalPAux_toNat G C L hG hzLe, hConst]
    omega
  rw [externalMissing, BitVec.toNat_sub_of_le hLe,
    totalPAux_toNat G C L hG hzLe, hConst]

abbrev directAuxNeighbors (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxNeighbors G E p

abbrev directAuxEffectiveUnion (C : G.LocalConfiguration)
    (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffectiveUnion G C E p

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

def effectiveThreeNat (m s : Nat) : BitVec 8 :=
  if BitVec.ofNat 8 m == 0 then effectiveAt (BitVec.ofNat 8 s) 10 8 7 7
  else if BitVec.ofNat 8 m == 1 then effectiveAt (BitVec.ofNat 8 s) 9 8 7 7
  else if BitVec.ofNat 8 m == 2 then effectiveAt (BitVec.ofNat 8 s) 8 7 7 7
  else if BitVec.ofNat 8 m == 3 then effectiveAt (BitVec.ofNat 8 s) 7 7 6 6
  else effectiveAt (BitVec.ofNat 8 s) 6 6 6 6

def effectiveFourNat (m s : Nat) : BitVec 8 :=
  if BitVec.ofNat 8 m == 0 then effectiveAt (BitVec.ofNat 8 s) 11 9 8 7
  else if BitVec.ofNat 8 m == 1 then effectiveAt (BitVec.ofNat 8 s) 10 8 7 7
  else if BitVec.ofNat 8 m == 2 then effectiveAt (BitVec.ofNat 8 s) 9 8 7 6
  else if BitVec.ofNat 8 m == 3 then effectiveAt (BitVec.ofNat 8 s) 8 7 7 6
  else if BitVec.ofNat 8 m == 4 then effectiveAt (BitVec.ofNat 8 s) 7 7 6 6
  else effectiveAt (BitVec.ofNat 8 s) 6 6 6 6

theorem effectiveThreeNat_le (m s u internal toP : Nat)
    (hm : m = 0) (hs : s ≤ 3) (hInternal : internal ≤ s.choose 2)
    (hRow : 3 - s ≤ m)
    (hToP : toP ≤ m - (3 - s))
    (hLower : s * (8 - u) ≤ internal + toP) :
    (effectiveThreeNat m s).toNat ≤ u := by
  subst m
  interval_cases s <;>
    simp [effectiveThreeNat, effectiveAt, Nat.choose, BitVec.toNat_ofNat]
      at hs hInternal hRow hToP hLower ⊢ ;
    omega

theorem effectiveFourNat_le (m s u internal toP : Nat)
    (hm : m ≤ 5) (hs : s ≤ 4) (hInternal : internal ≤ s.choose 2)
    (hRow : 4 - s ≤ m)
    (hToP : toP ≤ m - (4 - s))
    (hLower : s * (8 - u) ≤ internal + toP) :
    (effectiveFourNat m s).toNat ≤ u := by
  interval_cases m <;> interval_cases s <;>
    simp [effectiveFourNat, effectiveAt, Nat.choose, BitVec.toNat_ofNat]
      at hm hs hInternal hRow hToP hLower ⊢ <;>
    omega

theorem effective_toNat_le_union {zCount yValue : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hzLe : zCount ≤ 3) (hy : BSevenKThree.y G C = yValue)
    (hyz : (yValue = 1 ∧ zCount = 3) ∨
      (yValue = 2 ∧ (zCount = 1 ∨ zCount = 2)))
    (hmBound :
      (externalMissing yValue zCount (encodedArc (graphBits G L))).toNat ≤
        capacity yValue zCount)
    (p : Nat) (hp : p < 5) :
    (effective yValue zCount (encodedArc (graphBits G L)) p).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C)
        (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  let e := yValue + zCount
  let m := 5 * e - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = e := by
    simpa [E, e] using auxiliarySet_card G C L hy
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have heCases : e = 3 ∨ e = 4 := by
    rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> simp [e]
  have heLe : e ≤ 4 := by omega
  have hs : s ≤ e := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hm : m ≤ 5 * e := Nat.sub_le _ _
  have hRow : e - s ≤ m := by
    have hOther : ∑ q ∈ C.P.erase v, directCount G E q ≤ 4 * e := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase v, e := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 4 * e := by simp [Finset.card_erase_of_mem hvP, hPCard]
    have hEdge : edgeCount G C.P E =
        (∑ q ∈ C.P.erase v, directCount G E q) + directCount G E v := by
      unfold edgeCount
      have hSplit := Finset.sum_erase_add C.P (directCount G E) hvP
      omega
    have hsEq : s = directCount G E v := rfl
    dsimp only [m]
    omega
  have hLower :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffective_capacity_lower
      G C hMin E (auxiliarySet_disjoint_P G C) v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directAux_to_P_capacity G C hG E hPCard e hECard v hvP
  have hMN :
      (externalMissing yValue zCount (encodedArc (graphBits G L))).toNat = m := by
    simpa [m, e, E] using
      externalMissing_toNat G C L hG hzLe hy heLe
  have hmCap : m ≤ capacity yValue zCount := by simpa [hMN] using hmBound
  have hSN :
      (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat = s := by
    rw [pAuxOut_to_auxiliary G C L hG hzLe p hp]
    rfl
  have hMBV : externalMissing yValue zCount (encodedArc (graphBits G L)) =
      BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hMN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hSBV : pAuxOut zCount (encodedArc (graphBits G L)) p =
      BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hSN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (e - s) at hToP
  change (effective yValue zCount (encodedArc (graphBits G L)) p).toNat ≤ U.card
  simp only [effective, effectiveFour, effectiveThree]
  rw [hMBV, hSBV]
  dsimp only [e] at heCases heLe hs hm hRow hToP
  have hmFive : m ≤ 5 := by
    have hCapFive : capacity yValue zCount ≤ 5 := by
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide
    omega
  rcases heCases with he3 | he4
  · rw [if_neg (by omega)]
    have hmZero : m = 0 := by
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
        simp [capacity] at he3 hmCap ⊢ ; omega
    rw [he3] at hs hm hRow hToP
    change (effectiveThreeNat m s).toNat ≤ U.card
    exact effectiveThreeNat_le m s U.card (edgeCount G S S)
      (edgeCount G S C.P) hmZero hs hInternal hRow hToP hLower
  · rw [if_pos he4]
    rw [he4] at hs hm hRow hToP
    change (effectiveFourNat m s).toNat ≤ U.card
    exact effectiveFourNat_le m s U.card (edgeCount G S S)
      (edgeCount G S C.P) hmFive hs hInternal hRow hToP hLower

theorem effective_toNat_le_eleven (y zCount : Nat)
    (arc : Nat → Nat → Bool) (p : Nat) :
    (effective y zCount arc p).toNat ≤ 11 := by
  have h : (effective y zCount arc p).ule (11 : BitVec 8) = true := by
    unfold effective effectiveFour effectiveThree effectiveAt
    split <;> bv_decide
  simpa [BitVec.ule_eq_decide] using h

theorem externalMissing_le_capacity_of_arithmetic {yValue zCount : Nat}
    (arc : Nat → Nat → Bool) (hArithmetic : arithmetic yValue zCount arc = true) :
    (externalMissing yValue zCount arc).toNat ≤ capacity yValue zCount := by
  simp only [arithmetic, Bool.and_eq_true] at hArithmetic
  have hCap := hArithmetic.2
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat] at hCap
  exact hCap.trans (Nat.mod_le _ _)

theorem pEffective_true {zCount yValue : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 6)
    (hzLe : zCount ≤ 3) (hy : BSevenKThree.y G C = yValue)
    (hyz : (yValue = 1 ∧ zCount = 3) ∨
      (yValue = 2 ∧ (zCount = 1 ∨ zCount = 2)))
    (hmBound :
      (externalMissing yValue zCount (encodedArc (graphBits G L))).toNat ≤
        capacity yValue zCount) :
    pEffective yValue zCount (encodedArc (graphBits G L)) = true := by
  rw [pEffective, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hP := pOut_toNat G C L hG hzLe p hp
  have hH := pHOut_toNat G C L hG hzLe hHCard p hp
  have hAux := pAuxOut_to_auxiliary G C L hG hzLe p hp
  have hTable := effective_toNat_le_union G C L hG hMin hzLe hy hyz hmBound p hp
  have hPS := pSecondP_le_graph G C L hG hzLe p hp
  have hEeq : auxiliarySet G C =
      SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet G C := by rfl
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
    rw [auxiliarySet, directCount_union_of_disjoint G _ _ _ hDis]
    omega
  have hNatural :
      (pSecondP (encodedArc (graphBits G L)) p).toNat +
          (effective yValue zCount (encodedArc (graphBits G L)) p).toNat + 1 ≤
        (pOut (encodedArc (graphBits G L)) p).toNat +
          2 * (pHOut (encodedArc (graphBits G L)) p).toNat +
            (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat := by
    have hUnion' := hUnion
    change (C.P.filter fun w ↦ w ∈ G.secondOutNeighborFinset v).card +
        (directAuxEffectiveUnion G C (auxiliarySet G C) v).card ≤
          G.secondOutdegree v + directCount G C.H v at hUnion'
    dsimp only [v] at hPS hTable hNS hAux hDegreeE hUnion' ⊢
    rw [hP, hH, hAux]
    omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  have hTableLe := effective_toNat_le_eleven yValue zCount
    (encodedArc (graphBits G L)) p
  have hPSLe : (pSecondP (encodedArc (graphBits G L)) p).toNat ≤ 5 :=
    hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hPLe : (pOut (encodedArc (graphBits G L)) p).toNat ≤ 5 := by
    rw [hP]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut (encodedArc (graphBits G L)) p).toNat ≤ 6 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hAuxLe : (pAuxOut zCount (encodedArc (graphBits G L)) p).toNat ≤ 4 := by
    rw [hAux]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (by rw [auxiliarySet_card G C L hy]; omega)
  have h1 : (1 : BitVec 8).toNat = 1 := by decide
  have h2 : (2 : BitVec 8).toNat = 2 := by decide
  rw [h1, h2]
  repeat' rw [Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.EffectiveBridge
