import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.Assembly
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.FourDefs
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourAssembly

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pZOut_five_eq_four (C : G.LocalConfiguration) (L : Labels G 4 C)
    (p : Nat) (hp : p < 7) :
    pZOut 5 (graphBits G L) p = pZOut 4 (graphBits G L) p := by
  simp [pZOut, count,
    SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToZ_coreBits_inactive,
    bitCount, hp]

theorem pMinimumDegree_five_of_four (C : G.LocalConfiguration)
    (L : Labels G 4 C) (hMin : pMinimumDegree 4 (graphBits G L) = true) :
    pMinimumDegree 5 (graphBits G L) = true := by
  simp only [pMinimumDegree, all_eq_true_iff] at hMin ⊢
  intro p hp
  rw [pZOut_five_eq_four G C L p hp]
  exact hMin p hp

theorem coreArc_five_eq_four (bits : Encoding) (u v : Nat)
    (hu : u < 15) (hv : v < 15) :
    coreArc 5 bits u v = coreArc 4 bits u v := by
  simp [coreArc, hu, hv]

theorem reachesLocal_five_eq_four (bits : Encoding) (u v : Nat)
    (hu : u < 15) (hv : v < 15) :
    reachesLocal 5 bits u v = reachesLocal 4 bits u v := by
  apply Bool.eq_iff_iff.mpr
  simp only [reachesLocal, any_eq_true_iff]
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rwa [coreArc_five_eq_four bits u m hu hm,
      coreArc_five_eq_four bits m v hm hv] at h
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rwa [coreArc_five_eq_four bits u m hu hm,
      coreArc_five_eq_four bits m v hm hv]

theorem strictSecondLocal_five_eq_four (bits : Encoding) (u v : Nat)
    (hu : u < 15) (hv : v < 15) :
    strictSecondLocal 5 bits u v = strictSecondLocal 4 bits u v := by
  simp only [strictSecondLocal, coreArc_five_eq_four bits u v hu hv,
    reachesLocal_five_eq_four bits u v hu hv]

theorem pSecondPCount_five_eq_four (bits : Encoding) (p : Nat) (hp : p < 7) :
    pSecondPCount 5 bits p = pSecondPCount 4 bits p := by
  apply BitVec.eq_of_toNat_eq
  rw [pSecondPCount, pSecondPCount,
    toNat_count_eq_fin_sum 7 _ (by omega),
    toNat_count_eq_fin_sum 7 _ (by omega)]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [strictSecondLocal_five_eq_four bits (8 + p) (8 + q)]
  · omega
  · omega

theorem totalPToZ_five_toNat (C : G.LocalConfiguration) (L : Labels G 4 C)
    (hG : G.IsOriented) :
    (totalPToZ 5 (graphBits G L)).toNat =
      edgeCount G C.P (externalTargets G C) := by
  rw [totalPToZ, Assembly.toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pZOut 5 (graphBits G L) i).toNat =
      Shared.directCount G (externalTargets G C) (L.p i).1 := by
    intro i
    rw [pZOut_five_eq_four G C L i i.isLt]
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
  have hz : (externalTargets G C).card = 4 := by
    simpa using (Fintype.card_congr L.z).symm
  rw [hp, hz] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_five_toNat (C : G.LocalConfiguration) (L : Labels G 4 C)
    (hG : G.IsOriented) :
    (externalMissing 5 (graphBits G L)).toNat =
      35 - edgeCount G C.P (externalTargets G C) := by
  rw [externalMissing, BitVec.toNat_sub, totalPToZ_five_toNat G C L hG]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hz : (externalTargets G C).card = 4 := by
    simpa using (Fintype.card_congr L.z).symm
  rw [hp, hz] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.P (externalTargets G C) + 35) % 256) = _
  omega

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
theorem individualEffectiveLower_graph (C : G.LocalConfiguration)
    (L : Labels G 4 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hmBound : (externalMissing 5 (graphBits G L)).toNat ≤ 12)
    (p : Nat) (hp : p < 7)
    (hps : ¬G.Adj (L.p ⟨p, hp⟩).1 C.s) :
    (individualEffectiveLower (graphBits G L) p).toNat ≤
      (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G L
  let v := (L.p ⟨p, hp⟩).1
  let S := FiveZUnionEightCapacity.directZNeighbors G C v
  let m := 28 - edgeCount G C.P (externalTargets G C)
  let s := S.card
  let U := directZEffectiveUnion G C v
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = 4 := by
    simpa using (Fintype.card_congr L.z).symm
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hM : (externalMissing 5 bits).toNat = 7 + m := by
    rw [externalMissing_five_toNat G C L hG]
    have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
    rw [hPCard, hZCard] at hCap
    dsimp [m]
    omega
  have hm : m ≤ 5 := by
    have h := hmBound
    rw [hM] at h
    omega
  have hs : s ≤ 4 := by
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
  have hRow : 4 - s ≤ m := by
    simpa [m, hES] using
      (SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly.external_row_missing_le_total
        G C hPCard hZCard v hvP)
  have hToP : edgeCount G S C.P ≤ m - (4 - s) :=
    SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly.directZ_to_P_capacity_external
      G C hG hPCard hZCard v hvP hps
  have hS : (pZOut 5 bits p).toNat = s := by
    rw [pZOut_five_eq_four G C L p hp,
      pZOut_toNat G C L hG (by omega) p hp]
    exact hES
  have hMBV : externalMissing 5 bits = BitVec.ofNat 8 (7 + m) := by
    apply BitVec.eq_of_toNat_eq
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hSBV : pZOut 5 bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change (individualEffectiveLower bits p).toNat ≤ U.card
  simp only [individualEffectiveLower]
  rw [hMBV, hSBV]
  interval_cases m <;> interval_cases s <;>
    simp [effectiveAtRowSize, Nat.choose] at hInternal hRow hToP hLower ⊢ <;>
    first | omega | exact Finset.card_pos.mp (by omega)

theorem pEffectiveCondition_all_true (C : G.LocalConfiguration)
    (L : Labels G 4 C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hHCard : C.H.card = 7)
    (hmBound : (externalMissing 5 (graphBits G L)).toNat ≤ 12) :
    all 7 (pEffectiveCondition (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let bits := graphBits G L
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hP := pOut_toNat G C L hG p hp
  have hH := pHOut_toNat G C L hG hHCard p hp
  have hZ : (pZOut 5 bits p).toNat =
      Shared.directCount G (externalTargets G C) v := by
    rw [pZOut_five_eq_four G C L p hp,
      pZOut_toNat G C L hG (by omega) p hp]
  have hNatural : (pSecondPCount 5 bits p).toNat +
      (individualEffectiveLower bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut 5 bits p).toNat := by
    by_cases hps : G.Adj v C.s
    · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
        G C hG hPB hNoSeymour hRootDegree v hvP hps
      have hSecond4 := Assembly.pSecondPCount_le_qCount G C L hG
        (by omega) p hp
      have hSecond : (pSecondPCount 5 bits p).toNat ≤
          TerminalAlphaBeta.qCount G C.P C.H v := by
        rw [pSecondPCount_five_eq_four bits p hp]
        exact hSecond4
      let m := (externalMissing 5 bits).toNat
      let s := Shared.directCount G (externalTargets G C) v
      have hm : m ≤ 12 := by simpa [m] using hmBound
      have hs : s ≤ 4 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (by simpa using (Fintype.card_congr L.z).symm)
      have hMNat : (externalMissing 5 bits).toNat = m := rfl
      have hSNat : (pZOut 5 bits p).toNat = s := hZ
      have hMGe : 7 ≤ m := by
        have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
        have hECard : (externalTargets G C).card = 4 := by
          simpa using (Fintype.card_congr L.z).symm
        rw [hPCard, hECard] at hCap
        rw [externalMissing_five_toNat G C L hG] at hMNat
        omega
      have hMBV : externalMissing 5 bits = BitVec.ofNat 8 m := by
        apply BitVec.eq_of_toNat_eq
        rw [hMNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hSBV : pZOut 5 bits p = BitVec.ofNat 8 s := by
        apply BitVec.eq_of_toNat_eq
        rw [hSNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hTable : (individualEffectiveLower bits p).toNat ≤ 8 := by
        simp only [individualEffectiveLower]
        rw [hMBV, hSBV]
        interval_cases m <;> interval_cases s <;>
          simp [effectiveAtRowSize] at hMGe ⊢
      have hEpsilon : epsilonAt G v C.s = 1 := by simp [epsilonAt, hps]
      rw [hEpsilon] at hEquation
      dsimp [v, bits] at hSecond hEquation hTable hps hP hH hZ ⊢
      rw [hP, hH, hZ]
      rw [SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
        G C (L.p ⟨p, hp⟩).1 hvP]
      simp [epsilonAt, hps]
      omega
    · have hTable := individualEffectiveLower_graph G C L hG hMin
        hmBound p hp (by simpa [v] using hps)
      have hPS4 := Assembly.pSecondPCount_le_graphPSecond G C L hG
        (by omega) p hp
      have hPS : (pSecondPCount 5 bits p).toNat ≤
          (C.P.filter fun w ↦ w ∈ G.secondOutNeighborFinset v).card := by
        rw [pSecondPCount_five_eq_four bits p hp]
        exact hPS4
      have hUnion :=
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.PSecond_add_directZEffective_card_le_second_add_H
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
      dsimp [v, bits] at hPS hUnion hNS hDegree hTable hP hH hZ ⊢
      rw [hP, hH, hZ]
      omega
  simp only [pEffectiveCondition, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pSecondPCount 5 bits p).toNat +
      (individualEffectiveLower bits p).toNat + 1) % 256 ≤
    ((pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pZOut 5 bits p).toNat) % 256
  have hRightSmall : (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pZOut 5 bits p).toNat < 256 := by
    have hpLe : (pOut bits p).toNat ≤ 7 := by
      rw [hP]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hhLe : (pHOut bits p).toNat ≤ 7 := by
      rw [hH]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hzLe : (pZOut 5 bits p).toNat ≤ 4 := by
      rw [hZ]
      have hZCard : (externalTargets G C).card = 4 := by
        simpa using (Fintype.card_congr L.z).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
    omega
  rw [Nat.mod_eq_of_lt hRightSmall,
    Nat.mod_eq_of_lt (hNatural.trans_lt hRightSmall)]
  exact hNatural

theorem commonCore_true (C : G.LocalConfiguration) (L : Labels G 4 C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hA1Card : C.A1.card = 3) (hHCard : C.H.card = 7) :
    FourCore.commonCore (graphBits G L) = true := by
  let bits := graphBits G L
  have hOrA : orientedA bits = true := Assembly.orientedA_true G C L hG (by omega)
  have hOrP : orientedP bits = true := Assembly.orientedP_true G C L hG
  have hOrPH : orientedPH bits = true := Assembly.orientedPH_true G C L hG
  have hX : everyXReached bits = true := Assembly.everyXReached_true G C L hA1Card
  have hZ : allZReached 4 bits = true := Assembly.allZReached_true G C L (by omega)
  have hInactive : inactiveZZero 4 bits = true :=
    Assembly.inactiveZZero_true G C L (by omega)
  have hAMin : aMinimumAndDegree bits = true :=
    Assembly.aMinimumAndDegree_true G C L hG hPB hPivot hMin hk (by omega)
  have hANon : all 8 (aNonSeymour 4 bits) = true :=
    Assembly.aNonSeymour_all_true G C L hG hPB hNoSeymour (by omega)
  have hPMin : pMinimumDegree 4 bits = true :=
    Assembly.pMinimumDegree_true G C L hG hPB hHCard hMin (by omega)
  have hPMinFive : pMinimumDegree 5 bits = true :=
    pMinimumDegree_five_of_four G C L hPMin
  have hTie : all 8 (degreeThreeTieCondition bits) = true :=
    Assembly.degreeThreeTie_all_true G C L hG hPivot hk hPB (by omega)
  have hAMinEach : ∀ a < 8, (3 : BitVec 8).ule (aOut bits a) = true := by
    rw [aMinimumAndDegree, all_eq_true_iff] at hAMin
    intro a ha
    have hRow := hAMin a ha
    simp only [Bool.and_eq_true] at hRow
    exact hRow.1.1
  have hDegreeThree := Assembly.degreeThreeConsequences_true G C L hOrA hAMinEach
  change degreeThreeClassification bits = true ∧
    threeInnerWitnesses bits = true at hDegreeThree
  have hHall : all 8 (hallCondition 4 bits) = true :=
    Assembly.hallCondition_all_true G C L hG hPB hMin hNoSeymour (by omega)
  have hDual : degreeAndDualConditions bits = true :=
    degreeAndDual_of_local bits hOrA hOrPH hAMin
  have hMissing : (externalMissing 5 bits).ule 12 = true :=
    externalMissing_le_twelve bits hOrA hOrP hAMin hPMinFive hDual
  have hmNat : (externalMissing 5 bits).toNat ≤ 12 := by
    simpa [BitVec.ule_eq_decide] using hMissing
  have hPEff : all 7 (pEffectiveCondition bits) = true :=
    pEffectiveCondition_all_true G C L hG hPB hMin hNoSeymour
      hRootDegree hHCard hmNat
  have hSharp : sharpKing bits = true := sharpKing_of_orientedP bits hOrP
  change FourCore.commonCore bits = true
  simp only [FourCore.commonCore, hOrA, hOrP, hOrPH, hX, hZ, hInactive,
    hAMin, hANon, hPMin, hPEff, hHall, hTie, hDegreeThree.1,
    hDegreeThree.2, hDual, hSharp, Bool.and_self]

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourAssembly
