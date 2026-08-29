import SeymourEight.Cases.BSevenKTwo.RSix.XFourRoot.LowCoreBridge
import SeymourEight.Cases.BSevenKTwo.Counting

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourRoot

open CertificateBridge Shared
open RSix.XFourNoRoot
open RSix.XFourNoRoot.Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem reachedQ_eq_empty (C : G.LocalConfiguration)
    (hy : y G C = 0) : reachedQ G C = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa [y] using hy

private theorem reachedQ_eq_singleton (C : G.LocalConfiguration) (q : V)
    (hy : y G C = 1) (hq : q ∈ reachedQ G C) : reachedQ G C = {q} := by
  change (reachedQ G C).card = 1 at hy
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hy
  have haq : a = q := (by simpa [ha] using hq : q = a).symm
  simpa [haq] using ha

private theorem Q_eq_singleton (C : G.LocalConfiguration) (q : V)
    (hQCard : C.Q.card = 1) (hqQ : q ∈ C.Q) : C.Q = {q} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hQCard
  have haq : a = q := (by simpa [ha] using hqQ : q = a).symm
  simpa [haq] using ha

private theorem p_to_Q_zero_of_unreached (C : G.LocalConfiguration)
    (hy : y G C = 0) : edgeCount G C.P C.Q = 0 := by
  have hEmpty := reachedQ_eq_empty G C hy
  unfold edgeCount directCount internalFirstNeighbors
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq hpq
  have hReached : q ∈ reachedQ G C := Finset.mem_inter.mpr ⟨hq,
    (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      ⟨p, Finset.mem_union_right C.A1 hp, hpq⟩⟩
  simp [hEmpty] at hReached

private theorem auxiliary_disjoint_P (C : G.LocalConfiguration) :
    Disjoint (auxiliarySet G C) C.P := by
  rw [Finset.disjoint_left]
  intro v hvE hvP
  rcases Finset.mem_union.mp hvE with hvQ | hvExternal
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
      (Finset.mem_inter.mp hvQ).1
  · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExternal

private theorem auxiliary_card_three (C : G.LocalConfiguration)
    (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 2) ∨ (y G C = 1 ∧ C.z = 1)) :
    (auxiliarySet G C).card = 3 := by
  have hDisjoint : Disjoint (reachedQ G C) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvE
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C
        (Finset.mem_inter.mp hvQ).1) hvE
  rw [auxiliarySet, Finset.card_union_of_disjoint hDisjoint,
    card_externalTargets]
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · change (reachedQ G C).card = 0 at hy
    omega
  · change (reachedQ G C).card = 1 at hy
    omega

private theorem P_outgoingCaptured_auxiliary (C : G.LocalConfiguration)
    (hG : G.IsOriented) : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ auxiliarySet G C := by
  intro p hp v hv
  have hvCaptured := BSixKThree.P_outgoingCaptured_general G C hG p hp hv
  rcases Finset.mem_union.mp hvCaptured with hvLocal | hvExternal
  · rcases Finset.mem_union.mp hvLocal with hvHP | hvQ
    · rcases Finset.mem_union.mp hvHP with hvH | hvP
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvH)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvP)
    · have hpv := (Digraph.mem_outNeighborFinset (G := G)).mp hv
      have hvReached : v ∈ reachedQ G C := Finset.mem_inter.mpr ⟨hvQ,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_union_left _ hvReached)
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ hvExternal)

set_option maxHeartbeats 2000000 in
-- The final case split unfolds several shared counting and labeling bridges.
theorem impossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (_hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 2) ∨ (y G C = 1 ∧ C.z = 1)) : False := by
  have hPCard : C.P.card = 6 := hr
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hAOneCard : C.A1.card = 2 := hk
  have hXCard : C.X.card = 4 := hx
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 1 := by omega
  have hECard := auxiliary_card_three G C hRoot hyz
  have hEP := auxiliary_disjoint_P G C
  have hCaptured := P_outgoingCaptured_auxiliary G C hG
  have hPPLe : edgeCount G C.P C.P ≤ 15 := by
    have h := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at h
    norm_num [Nat.choose] at h
    exact h
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · have hReachedEmpty := reachedQ_eq_empty G C hy
    have hAux : auxiliarySet G C = externalTargets G C := by
      simp [auxiliarySet, hReachedEmpty]
    have hExternalCard : (externalTargets G C).card = 3 := by
      rw [card_externalTargets, hz, hRoot]
    have hPQ := p_to_Q_zero_of_unreached G C hy
    have hHP : 21 ≤ edgeCount G C.H C.P := by
      have hCap := BSevenKTwo.H_degree_capacity G C hG hMin hk
      rw [hHCard, hx, hRCard, hQCard, hy] at hCap
      norm_num [Nat.choose] at hCap
      omega
    have hPELe : edgeCount G C.P (externalTargets G C) ≤ 18 :=
      (edgeCount_le_card_mul_card G C.P (externalTargets G C)).trans_eq (by
        rw [hPCard, hExternalCard])
    have hPE : edgeCount G C.P (externalTargets G C) = 18 := by
      have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
      rw [hHCard, hPQ] at hCap
      omega
    have hPH : edgeCount G C.P C.H = 15 := by
      have hPHLe : edgeCount G C.P C.H ≤ 15 := by omega
      have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
      rw [hPQ, hPE] at hAccounting
      have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
        calc
          48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            exact hMin p
      omega
    have hPP : edgeCount G C.P C.P = 15 := by
      have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
      rw [hPQ, hPE, hPH] at hAccounting
      have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
        calc
          48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            exact hMin p
      omega
    let L := Labels.unreachedLabels G C hPCard hHCard hAOneCard hXCard
      hExternalCard
    have hPOrder : ∀ i : Fin 5,
        pKey G C (externalTargets G C) (L.p ⟨i.val + 1, by omega⟩).1 ≤
          pKey G C (externalTargets G C) (L.p ⟨i.val, by omega⟩).1 := by
      intro i
      exact sortedP_key_anti G C (externalTargets G C) _
        (Fin.mk_le_mk.mpr (by omega))
    have hAOrder := canonicalH_a_order G C hHCard hAOneCard hXCard
    have hXOrder := canonicalH_x_order G C hHCard hAOneCard hXCard
    have hEOrder : eIncoming G (fun i => (L.p i).1) (L.e 2).1 ≤
        eIncoming G (fun i => (L.p i).1) (L.e 1).1 := by
      exact sortedE_degree_anti G _ (externalTargets G C) _
        (show (1 : Fin 3) ≤ 2 by decide)
    have hEight : ∀ p ∈ C.P,
        8 ≤ (directAuxEffectiveUnion G C (externalTargets G C) p).card := by
      intro p hp
      exact effective_eight_of_one_defect G C (externalTargets G C) hAux.symm
        hG hMin hRootDegree hRoot hPCard hExternalCard
        (by simpa [hAux] using hEP) (by omega) p hp
    exact RSix.XFourNoRoot.LowCoreBridge.case_false G C (externalTargets G C) L
      hG hMin hNoSeymour hAux.symm (by simpa [hAux] using hCaptured)
      hEight 0 0 0 0 (by omega) (by omega) (by omega) (by omega)
      hPE hPH hPP hPOrder hAOrder hXOrder hEOrder
  · have hReachedCard : (reachedQ G C).card = 1 := hy
    obtain ⟨q, hqReached⟩ := Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
    have hqQ : q ∈ C.Q := (Finset.mem_inter.mp hqReached).1
    have hReached : reachedQ G C = {q} := reachedQ_eq_singleton G C q hy hqReached
    have hQ : C.Q = {q} := Q_eq_singleton G C q hQCard hqQ
    have hExternalCard : (externalTargets G C).card = 2 := by
      rw [card_externalTargets, hz, hRoot]
    have hAux : auxiliarySet G C = {q} ∪ externalTargets G C := by
      simp [auxiliarySet, hReached]
    let E := {q} ∪ externalTargets G C
    let c := edgeCount G C.A1 {q}
    have hc : c ≤ 2 := by
      dsimp [c]
      exact (edgeCount_le_card_mul_card G C.A1 {q}).trans_eq (by
        rw [hAOneCard]
        simp)
    have hHQ : edgeCount G C.H C.Q ≤ 4 + c := by
      have hSplit := BSixKThree.edgeCount_source_union G C.A1 C.X C.Q
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
      have hXQ := edgeCount_le_card_mul_card G C.X C.Q
      rw [hXCard, hQCard] at hXQ
      have hSplit' : edgeCount G C.H C.Q =
          edgeCount G C.A1 C.Q + edgeCount G C.X C.Q := by
        simpa only [Digraph.LocalConfiguration.H] using hSplit
      have hcEq : edgeCount G C.A1 C.Q = c := by simp [c, hQ]
      omega
    have hHPc : 21 ≤ edgeCount G C.H C.P + c := by
      have hLower : 48 ≤ ∑ h ∈ C.H, G.outdegree h := by
        calc
          48 = ∑ _h ∈ C.H, 8 := by simp [hHCard]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro h hh
            exact hMin h
      have hSplit := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
      have hA := Shared.H_to_A_le_internal_add_x_add_xR G C hG
      rw [hHCard, hx, hRCard] at hA
      norm_num [Nat.choose] at hA
      omega
    have hPELe : edgeCount G C.P E ≤ 18 :=
      (edgeCount_le_card_mul_card G C.P E).trans_eq (by
        rw [hPCard]
        have : E.card = 3 := by simpa [E, hAux] using hECard
        rw [this])
    have hPESplit : edgeCount G C.P E =
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
      rw [hQ]
      apply edgeCount_union_of_disjoint
      rw [Finset.disjoint_left]
      intro v hvq hvE
      exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C
          (Finset.mem_singleton.mp hvq ▸ hqQ)) hvE
    have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
    have hDegreeAux : 48 ≤ edgeCount G C.P C.H +
        edgeCount G C.P C.P + edgeCount G C.P E := by
      rw [hPESplit]
      have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
        calc
          48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            exact hMin p
      omega
    let m := 18 - edgeCount G C.P E
    let alpha := 15 + c - edgeCount G C.P C.H
    let beta := 15 - edgeCount G C.P C.P
    have hPE : edgeCount G C.P E = 18 - m := by dsimp [m]; omega
    have hPH : edgeCount G C.P C.H = 15 + c - alpha := by dsimp [alpha]; omega
    have hPP : edgeCount G C.P C.P = 15 - beta := by dsimp [beta]; omega
    have hdefect : m + alpha + beta ≤ c := by omega
    have hm : m ≤ 2 := by omega
    let L := Labels.reachedLabels G C q hqQ hPCard hHCard hAOneCard
      hXCard hExternalCard
    have hPOrder : ∀ i : Fin 5,
        pKey G C E (L.p ⟨i.val + 1, by omega⟩).1 ≤
          pKey G C E (L.p ⟨i.val, by omega⟩).1 := by
      intro i
      exact sortedP_key_anti G C E _ (Fin.mk_le_mk.mpr (by omega))
    have hAOrder := canonicalH_a_order G C hHCard hAOneCard hXCard
    have hXOrder := canonicalH_x_order G C hHCard hAOneCard hXCard
    have hEOrder : eIncoming G (fun i => (L.p i).1) (L.e 2).1 ≤
        eIncoming G (fun i => (L.p i).1) (L.e 1).1 := by
      exact sortedE_degree_anti G _ (externalTargets G C) _
        (show (0 : Fin 2) ≤ 1 by decide)
    by_cases hmLow : m ≤ 1
    · have hPELower : 17 ≤ edgeCount G C.P E := by omega
      have hEight : ∀ p ∈ C.P,
          8 ≤ (directAuxEffectiveUnion G C E p).card := by
        intro p hp
        exact effective_eight_of_one_defect G C E (by simpa [E] using hAux.symm)
          hG hMin hRootDegree hRoot hPCard (by simpa [E, hAux] using hECard)
          (by simpa [E, hAux] using hEP) hPELower p hp
      exact RSix.XFourNoRoot.LowCoreBridge.case_false G C E L hG hMin
        hNoSeymour (by simpa [E] using hAux.symm)
        (by simpa [E, hAux] using hCaptured) hEight c m alpha beta hc hmLow
        hdefect hHPc hPE hPH hPP hPOrder hAOrder hXOrder hEOrder
    · have hmTwo : m = 2 := by omega
      have hcTwo : c = 2 := by omega
      have hAlphaZero : alpha = 0 := by omega
      have hBetaZero : beta = 0 := by omega
      have hPE16 : edgeCount G C.P E = 16 := by omega
      have hPH17 : edgeCount G C.P C.H = 17 := by omega
      have hPP15 : edgeCount G C.P C.P = 15 := by omega
      have hHP19 : 19 ≤ edgeCount G C.H C.P := by omega
      have hPCond := pConditions_true G C E L hG hMin hNoSeymour
        hRootDegree hRoot (by simpa [E] using hAux.symm)
        (by simpa [E, hAux] using hCaptured)
      exact LowCoreBridge.caseTwo_false G C E L hG
        (by simpa [E] using hAux.symm) (by simpa [E, hAux] using hCaptured)
        hPCond hHP19 hPE16 hPH17 hPP15 hPOrder hAOrder hXOrder hEOrder

end SeymourEight.BSevenKTwo.RSix.XFourRoot
