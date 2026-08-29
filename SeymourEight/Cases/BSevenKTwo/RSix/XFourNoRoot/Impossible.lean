import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.LowCoreBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.EffectiveEightBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.LowExactBridge

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# The no-root `r = 6`, `x = 4` family

The graph-level counting leaves an auxiliary set of three vertices.  We split
by its missing `P` incidences.  Defect zero is discharged by the common
seven-vertex effective-union obstruction, defect two by the projected exact
certificate, and defect one by the low core plus its two small exact tails.
-/

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot

open CertificateBridge Shared Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem edgeCount_P_root_zero (C : G.LocalConfiguration)
    (hNoRoot : epsilonS G C = 0) : edgeCount G C.P {C.s} = 0 := by
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  unfold edgeCount directCount internalFirstNeighbors
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s hs hps
  have hsEq : s = C.s := Finset.mem_singleton.mp hs
  subst s
  have hReach : ∃ q ∈ C.P, G.Adj q C.s := ⟨p, hp, hps⟩
  simp [rootSecondFinset, hReach] at hRootEmpty

private theorem externalTargets_eq_Z (C : G.LocalConfiguration)
    (hNoRoot : epsilonS G C = 0) : externalTargets G C = C.Z := by
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  simp [externalTargets, hRootEmpty]

private theorem reachedQ_eq_empty (C : G.LocalConfiguration)
    (hy : y G C = 0) : reachedQ G C = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa [y] using hy

private theorem Q_eq_singleton (C : G.LocalConfiguration) (q : V)
    (hQCard : C.Q.card = 1) (hqQ : q ∈ C.Q) : C.Q = {q} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hQCard
  have haq : a = q := (by simpa [ha] using hqQ : q = a).symm
  simpa [haq] using ha

private theorem reachedQ_eq_singleton (C : G.LocalConfiguration) (q : V)
    (hy : y G C = 1) (hq : q ∈ reachedQ G C) : reachedQ G C = {q} := by
  change (reachedQ G C).card = 1 at hy
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hy
  have haq : a = q := (by simpa [ha] using hq : q = a).symm
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
  rcases Finset.mem_union.mp hvE with hvQ | hvZ
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
        (Finset.mem_inter.mp hvQ).1
  · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvZ

private theorem auxiliary_card_three (C : G.LocalConfiguration)
    (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2)) :
    (auxiliarySet G C).card = 3 := by
  have hDisjoint : Disjoint (reachedQ G C) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvE
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C
        (Finset.mem_inter.mp hvQ).1) hvE
  rw [auxiliarySet, Finset.card_union_of_disjoint hDisjoint,
    card_externalTargets, hNoRoot]
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · change (reachedQ G C).card = 0 at hy
    omega
  · change (reachedQ G C).card = 1 at hy
    omega

private theorem P_outgoingCaptured_auxiliary (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ auxiliarySet G C := by
  intro p hp v hv
  have hvCaptured := BSixKThree.P_outgoingCaptured_general G C hG p hp hv
  rcases Finset.mem_union.mp hvCaptured with hvLocal | hvExternal
  · rcases Finset.mem_union.mp hvLocal with hvHP | hvQ
    · rcases Finset.mem_union.mp hvHP with hvH | hvP
      · exact Finset.mem_union_left (auxiliarySet G C)
          (Finset.mem_union_right C.P hvH)
      · exact Finset.mem_union_left (auxiliarySet G C)
          (Finset.mem_union_left C.H hvP)
    · have hpv : G.Adj p v :=
          (Digraph.mem_outNeighborFinset (G := G)).mp hv
      have hvReached : v ∈ reachedQ G C := Finset.mem_inter.mpr ⟨hvQ,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_union_left _ hvReached)
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ hvExternal)

private theorem defectZero_false
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (E : Finset V) (hPCard : C.P.card = 6) (hECard : E.card = 3)
    (hEP : Disjoint E C.P) (hPE : edgeCount G C.P E = 18)
    (p : V) (hp : p ∈ C.P)
    (hUCard : (directAuxEffectiveUnion G C E p).card = 7) : False := by
  let S := directAuxNeighbors G E p
  let W := directAuxEffectiveUnion G C E p
  have hEach : ∀ q ∈ C.P, directCount G E q ≤ 3 := by
    intro q hq
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hRow : directCount G E p = 3 := by
    apply Nat.le_antisymm (hEach p hp)
    by_contra hn
    have hStrict : directCount G E p < 3 := by omega
    have hSumStrict :
        (∑ q ∈ C.P, directCount G E q) < ∑ _q ∈ C.P, 3 := by
      apply Finset.sum_lt_sum hEach
      exact ⟨p, hp, hStrict⟩
    change (∑ q ∈ C.P, directCount G E q) = 18 at hPE
    simp [hPCard] at hSumStrict
    omega
  have hSE : S = E := by
    apply Finset.eq_of_subset_of_card_le (directAuxNeighbors_subset G E p)
    change E.card ≤ S.card
    simpa [S, directAuxNeighbors, directCount, internalFirstNeighbors,
      hECard] using hRow.symm.le
  have hEW : Disjoint E W := by
    rw [Finset.disjoint_left]
    intro v hvE hvW
    have hvNot := (Finset.mem_sdiff.mp hvW).2
    apply hvNot
    apply Finset.mem_union_right
    change v ∈ S
    exact hSE.symm ▸ hvE
  have hPW : Disjoint C.P W := by
    rw [Finset.disjoint_left]
    intro v hvP hvW
    exact (Finset.mem_sdiff.mp hvW).2 (Finset.mem_union_left S hvP)
  have hCaptured : ∀ e ∈ E, G.outNeighborFinset e ⊆ E ∪ C.P ∪ W := by
    intro e he v hev
    by_cases hvE : v ∈ E
    · exact Finset.mem_union_left W (Finset.mem_union_left C.P hvE)
    by_cases hvP : v ∈ C.P
    · exact Finset.mem_union_left W (Finset.mem_union_right E hvP)
    · apply Finset.mem_union_right
      apply Finset.mem_sdiff.mpr
      constructor
      · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        refine ⟨e, ?_, (Digraph.mem_outNeighborFinset (G := G)).mp hev⟩
        change e ∈ S
        exact hSE.symm ▸ he
      · intro hv
        rcases Finset.mem_union.mp hv with hvP' | hvS
        · exact hvP hvP'
        · exact hvE (hSE ▸ hvS)
  exact EffectiveEightBridge.exactSevenAuxiliaryUnion_false G hBound hG hMin
    hNoSeymour C.P E W hPCard hECard (by simpa [W] using hUCard)
    hEP hEW hPW hPE hCaptured

private theorem aOne_eq_labeled_pair (C : G.LocalConfiguration)
    (E : Finset V) (L : LowLabels G C E) (hAOneCard : C.A1.card = 2) :
    C.A1 = {(L.h 0).1, (L.h 1).1} := by
  have hne : (L.h 0).1 ≠ (L.h 1).1 := by
    intro h
    have : (0 : Fin 6) = 1 := L.h.injective (Subtype.ext h)
    omega
  have hSubset : ({(L.h 0).1, (L.h 1).1} : Finset V) ⊆ C.A1 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact L.h_aOne 0
    · exact L.h_aOne 1
  symm
  apply Finset.eq_of_subset_of_card_le hSubset
  simp [hAOneCard, hne]

private theorem aOne_exact_one_labeled (C : G.LocalConfiguration)
    (q : V) (E : Finset V) (L : LowLabels G C E)
    (hAOneCard : C.A1.card = 2)
    (hCount : edgeCount G C.A1 {q} = 1) :
    (G.Adj (L.h 0).1 q ∧ ¬G.Adj (L.h 1).1 q) ∨
      (¬G.Adj (L.h 0).1 q ∧ G.Adj (L.h 1).1 q) := by
  let F := C.A1.filter (fun a => G.Adj a q)
  have hFCard : F.card = 1 := by
    rw [edgeCount_eq_sum_incoming] at hCount
    simpa [F, internalInDegree] using hCount
  have hne : (L.h 0).1 ≠ (L.h 1).1 := by
    intro h
    have : (0 : Fin 6) = 1 := L.h.injective (Subtype.ext h)
    omega
  by_cases h0 : G.Adj (L.h 0).1 q <;>
    by_cases h1 : G.Adj (L.h 1).1 q
  · have hPair : ({(L.h 0).1, (L.h 1).1} : Finset V) ⊆ F := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨L.h_aOne 0, h0⟩
      · exact Finset.mem_filter.mpr ⟨L.h_aOne 1, h1⟩
    have := Finset.card_le_card hPair
    simp [hne, hFCard] at this
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · have hFEmpty : F = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hvA hvAdj
      rw [aOne_eq_labeled_pair G C E L hAOneCard] at hvA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvA
      rcases hvA with rfl | rfl
      · exact h0 hvAdj
      · exact h1 hvAdj
    rw [hFEmpty] at hFCard
    simp at hFCard

private theorem aOne_both_labeled (C : G.LocalConfiguration)
    (q : V) (E : Finset V) (L : LowLabels G C E)
    (hAOneCard : C.A1.card = 2)
    (hCount : edgeCount G C.A1 {q} = 2) :
    G.Adj (L.h 0).1 q ∧ G.Adj (L.h 1).1 q := by
  let F := C.A1.filter (fun a => G.Adj a q)
  have hFCard : F.card = 2 := by
    rw [edgeCount_eq_sum_incoming] at hCount
    simpa [F, internalInDegree] using hCount
  have hEq : F = C.A1 := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [hAOneCard, hFCard]
  constructor
  · have hm : (L.h 0).1 ∈ F := by rw [hEq]; exact L.h_aOne 0
    exact (Finset.mem_filter.mp hm).2
  · have hm : (L.h 1).1 ∈ F := by rw [hEq]; exact L.h_aOne 1
    exact (Finset.mem_filter.mp hm).2

private theorem outsideSet_card_le_of_effective_seven
    (C : G.LocalConfiguration) (q p : V) (E : Finset V)
    (hE : E = {q} ∪ C.Z) (hPCard : C.P.card = 6) (hECard : E.card = 3)
    (hPE : 17 ≤ edgeCount G C.P E) (hpP : p ∈ C.P)
    (hTwo : (directAuxNeighbors G E p).card = 2 →
      8 ≤ (directAuxEffectiveUnion G C E p).card)
    (hSeven : (directAuxEffectiveUnion G C E p).card = 7) :
    (MTwoProjectedBridge.outsideSet G C q).card ≤ 7 := by
  let S := directAuxNeighbors G E p
  let U := directAuxEffectiveUnion G C E p
  have hSLe : S.card ≤ 3 :=
    (Finset.card_le_card (directAuxNeighbors_subset G E p)).trans_eq hECard
  have hOther : ∑ u ∈ C.P.erase p, directCount G E u ≤ 15 := by
    calc
      _ ≤ ∑ _u ∈ C.P.erase p, 3 := by
        apply Finset.sum_le_sum
        intro u hu
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
      _ = 15 := by simp [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit := Finset.sum_erase_add C.P (directCount G E) hpP
  have hSLower : 2 ≤ S.card := by
    have hSDirect : S.card = directCount G E p := rfl
    change 17 ≤ ∑ u ∈ C.P, directCount G E u at hPE
    omega
  have hSCard : S.card = 3 := by
    have hNotTwo : S.card ≠ 2 := by
      intro hs
      have := hTwo (by simpa [S] using hs)
      rw [hSeven] at this
      omega
    omega
  have hSE : S = E := by
    apply Finset.eq_of_subset_of_card_le (directAuxNeighbors_subset G E p)
    rw [hSCard, hECard]
  have hSubset : MTwoProjectedBridge.outsideSet G C q ⊆ U := by
    intro v hv
    rcases Finset.mem_sdiff.mp hv with ⟨hvReach, hvOutside⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · change v ∈ G.outNeighborFinsetOf S
      rw [hSE]
      simpa [hE] using hvReach
    · intro hvLocal
      apply hvOutside
      rcases Finset.mem_union.mp hvLocal with hvP | hvS
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hvP))
      · have hvE : v ∈ E := hSE ▸ hvS
        exact Finset.mem_union_left {C.s}
          (Finset.mem_union_right (C.A ∪ C.P) (hE ▸ hvE))
  have := Finset.card_le_card hSubset
  simpa [U, hSeven] using this

set_option maxHeartbeats 2000000 in
-- Canonical label definitions are intentionally unfolded by the bridge calls.
theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2)) : False := by
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
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hRootZero := edgeCount_P_root_zero G C hNoRoot
  have hECard := auxiliary_card_three G C hNoRoot hyz
  have hEP := auxiliary_disjoint_P G C
  have hCaptured := P_outgoingCaptured_auxiliary G C hG
  have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hPPLe : edgeCount G C.P C.P ≤ 15 := by
    have h := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at h
    norm_num [Nat.choose] at h
    exact h
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · have hReachedEmpty := reachedQ_eq_empty G C hy
    have hExternal := externalTargets_eq_Z G C hNoRoot
    have hAux : auxiliarySet G C = C.Z := by
      simp [auxiliarySet, hReachedEmpty, hExternal]
    have hZCard : C.Z.card = 3 := hz
    have hPQ := p_to_Q_zero_of_unreached G C hy
    have hHP : 21 ≤ edgeCount G C.H C.P := by
      have hCap := BSevenKTwo.H_degree_capacity G C hG hMin hk
      rw [hHCard, hx, hRCard, hQCard, hy] at hCap
      norm_num [Nat.choose] at hCap
      omega
    have hPZLe : edgeCount G C.P C.Z ≤ 18 :=
      (edgeCount_le_card_mul_card G C.P C.Z).trans_eq (by
        rw [hPCard, hZCard])
    have hPZ : edgeCount G C.P C.Z = 18 := by
      have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
      rw [hHCard, hPQ, hExternal] at hCap
      omega
    have hPH : edgeCount G C.P C.H = 15 := by
      have hPHLe : edgeCount G C.P C.H ≤ 15 := by omega
      have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
      rw [hPQ, hExternal, hPZ] at hAccounting
      omega
    have hPP : edgeCount G C.P C.P = 15 := by
      have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
      rw [hPQ, hExternal, hPZ, hPH] at hAccounting
      omega
    let L := Labels.unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard
    have hPOrder : ∀ i : Fin 5,
        pKey G C C.Z (L.p ⟨i.val + 1, by omega⟩).1 ≤
          pKey G C C.Z (L.p ⟨i.val, by omega⟩).1 := by
      intro i
      exact Labels.unreachedLabels_p_order G C hPCard hHCard hAOneCard
        hXCard hZCard i
    have hAOrder :
        RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 1).1 ≤
          RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 0).1 := by
      exact Labels.unreachedLabels_a_order G C hPCard hHCard hAOneCard
        hXCard hZCard
    have hXOrder : ∀ i : Fin 3,
        RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
            (L.h ⟨i.val + 3, by omega⟩).1 ≤
          RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
            (L.h ⟨i.val + 2, by omega⟩).1 := by
      intro i
      exact Labels.unreachedLabels_x_order G C hPCard hHCard hAOneCard
        hXCard hZCard i
    have hEOrder : eIncoming G (fun i => (L.p i).1) (L.e 2).1 ≤
        eIncoming G (fun i => (L.p i).1) (L.e 1).1 := by
      exact Labels.unreachedLabels_e_order G C hPCard hHCard hAOneCard
        hXCard hZCard
    by_cases hEight : ∀ p ∈ C.P,
        8 ≤ (directAuxEffectiveUnion G C C.Z p).card
    · exact LowCoreBridge.case_false G C C.Z L hG hMin hNoSeymour
        hAux.symm (by simpa [hAux] using hCaptured) hEight 0 0 0 0
        (by omega) (by omega) (by omega) (by omega)
        (by simpa [hAux] using hPZ) hPH hPP hPOrder hAOrder hXOrder hEOrder
    · push Not at hEight
      obtain ⟨p, hp, hSmall⟩ := hEight
      have hEffective := effective_seven_or_eight G C hG hMin C.Z
        (by simpa [hAux] using hEP) hPCard hZCard (by omega) p hp
      have hUCard : (directAuxEffectiveUnion G C C.Z p).card = 7 := by omega
      exact defectZero_false G hBound C hG hMin hNoSeymour C.Z hPCard
        hZCard (by simpa [hAux] using hEP) hPZ p hp hUCard
  · have hReachedCard : (reachedQ G C).card = 1 := hy
    obtain ⟨q, hqReached⟩ := Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
    have hqQ : q ∈ C.Q := (Finset.mem_inter.mp hqReached).1
    have hReached : reachedQ G C = {q} := reachedQ_eq_singleton G C q hy hqReached
    have hQ : C.Q = {q} := Q_eq_singleton G C q hQCard hqQ
    have hZCard : C.Z.card = 2 := hz
    have hExternal := externalTargets_eq_Z G C hNoRoot
    have hAux : auxiliarySet G C = {q} ∪ C.Z := by
      simp [auxiliarySet, hReached, hExternal]
    let E := {q} ∪ C.Z
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
    have hPELe : edgeCount G C.P E ≤ 18 := by
      exact (edgeCount_le_card_mul_card G C.P E).trans_eq (by
        rw [hPCard]
        have : E.card = 3 := by simpa [E, hAux] using hECard
        rw [this])
    have hPHLe : edgeCount G C.P C.H ≤ 15 + c := by omega
    have hExternal := externalTargets_eq_Z G C hNoRoot
    have hqZ : q ∉ C.Z := by
      intro hqZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqZ
        (Finset.mem_union_right ({C.s} ∪ C.A)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
    have hPESplit : edgeCount G C.P E =
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
      rw [hQ, hExternal]
      apply edgeCount_union_of_disjoint
      rw [Finset.disjoint_left]
      simpa using hqZ
    have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
    have hDegreeAux : 48 ≤ edgeCount G C.P C.H +
        edgeCount G C.P C.P + edgeCount G C.P E := by
      rw [hPESplit]
      omega
    let m := 18 - edgeCount G C.P E
    let alpha := 15 + c - edgeCount G C.P C.H
    let beta := 15 - edgeCount G C.P C.P
    have hPE : edgeCount G C.P E = 18 - m := by
      dsimp [m]
      omega
    have hPH : edgeCount G C.P C.H = 15 + c - alpha := by
      dsimp [alpha]
      omega
    have hPP : edgeCount G C.P C.P = 15 - beta := by
      dsimp [beta]
      omega
    have hdefect : m + alpha + beta ≤ c := by omega
    have hm : m ≤ 2 := by omega
    have hPELower : 16 ≤ edgeCount G C.P E := by omega
    by_cases hmLow : m ≤ 1
    · have hPELower17 : 17 ≤ edgeCount G C.P E := by omega
      let L := Labels.reachedLabels G C q hqQ hPCard hHCard hAOneCard
        hXCard hZCard
      have hPOrder : ∀ i : Fin 5,
          pKey G C E (L.p ⟨i.val + 1, by omega⟩).1 ≤
            pKey G C E (L.p ⟨i.val, by omega⟩).1 := by
        intro i
        exact Labels.reachedLabels_p_order G C q hqQ hPCard hHCard
          hAOneCard hXCard hZCard i
      have hAOrder :
          RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 1).1 ≤
            RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 0).1 := by
        exact Labels.reachedLabels_a_order G C q hqQ hPCard hHCard
          hAOneCard hXCard hZCard
      have hXOrder : ∀ i : Fin 3,
          RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
              (L.h ⟨i.val + 3, by omega⟩).1 ≤
            RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
              (L.h ⟨i.val + 2, by omega⟩).1 := by
        intro i
        exact Labels.reachedLabels_x_order G C q hqQ hPCard hHCard
          hAOneCard hXCard hZCard i
      have hEOrder : eIncoming G (fun i => (L.p i).1) (L.e 2).1 ≤
          eIncoming G (fun i => (L.p i).1) (L.e 1).1 := by
        exact Labels.reachedLabels_e_order G C q hqQ hPCard hHCard
          hAOneCard hXCard hZCard
      by_cases hEight : ∀ p ∈ C.P,
          8 ≤ (directAuxEffectiveUnion G C E p).card
      · exact LowCoreBridge.case_false G C E L hG hMin hNoSeymour
          hAux.symm (by simpa [E, hAux] using hCaptured) hEight c m alpha beta
          hc hmLow hdefect hHPc hPE hPH hPP hPOrder hAOrder hXOrder hEOrder
      · push Not at hEight
        obtain ⟨p, hp, hSmall⟩ := hEight
        have hEffective := effective_seven_or_eight G C hG hMin E
          (by simpa [E, hAux] using hEP) hPCard (by simpa [E, hAux] using hECard)
          hPELower17 p hp
        have hUCard : (directAuxEffectiveUnion G C E p).card = 7 := by omega
        by_cases hmZero : m = 0
        · have hPE18 : edgeCount G C.P E = 18 := by omega
          exact defectZero_false G hBound C hG hMin hNoSeymour E hPCard
            (by simpa [E, hAux] using hECard) (by simpa [E, hAux] using hEP)
            hPE18 p hp hUCard
        · have hmOne : m = 1 := by omega
          have hPE17 : edgeCount G C.P ({q} ∪ C.Z) = 17 := by
            simpa [E] using (show edgeCount G C.P E = 17 by omega)
          have hCaptured' : ∀ u ∈ C.P,
              G.outNeighborFinset u ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z) := by
            simpa [hAux] using hCaptured
          have hB : C.B = C.P ∪ {q} := by
            rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C, hQ]
          let W := MTwoProjectedBridge.outsideSet G C q
          have hWCard : W.card ≤ 7 := by
            simpa [W] using outsideSet_card_le_of_effective_seven G C q p E
              (by rfl) hPCard (by simpa [E, hAux] using hECard)
              (by omega) hp hEffective.2 hUCard
          by_cases hcOne : c = 1
          · have hAlphaZero : alpha = 0 := by omega
            have hBetaZero : beta = 0 := by omega
            have hPP15 : edgeCount G C.P C.P = 15 := by omega
            have hPH16 : edgeCount G C.P C.H = 16 := by omega
            have hHP20 : 20 ≤ edgeCount G C.H C.P := by omega
            let low := Labels.reachedLabels G C q hqQ hPCard hHCard
              hAOneCard hXCard hZCard
            have heZeroLow : (low.e 0).1 = q := by
              exact Labels.reachedLabels_e_zero G C q hqQ hPCard hHCard
                hAOneCard hXCard hZCard
            have hAOneQ : edgeCount G C.A1 {q} = 1 := by
              dsimp [c] at hcOne
              exact hcOne
            have hExactly := aOne_exact_one_labeled G C q ({q} ∪ C.Z) low
              hAOneCard hAOneQ
            have finish (low' : LowLabels G C ({q} ∪ C.Z))
                (heZero' : (low'.e 0).1 = q)
                (hq0' : G.Adj (low'.h 0).1 q)
                (hq1' : ¬G.Adj (low'.h 1).1 q)
                (hPOrder' : ∀ i : Fin 5,
                  pKey G C ({q} ∪ C.Z)
                      (low'.p ⟨i.val + 1, by omega⟩).1 ≤
                    pKey G C ({q} ∪ C.Z)
                      (low'.p ⟨i.val, by omega⟩).1)
                (hXOrder' : ∀ i : Fin 3,
                  RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
                      (low'.h ⟨i.val + 3, by omega⟩).1 ≤
                    RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
                      (low'.h ⟨i.val + 2, by omega⟩).1)
                (hEOrder' : eIncoming G (fun i => (low'.p i).1)
                    (low'.e 2).1 ≤
                  eIncoming G (fun i => (low'.p i).1) (low'.e 1).1) : False := by
              let L' := MTwoProjectedBridge.labelsFromLow G C q low' hRCard
                hACard (MTwoProjectedBridge.paddedOutsideLabels W)
              have heZero'Full : (L'.low.e 0).1 = q := by exact heZero'
              have hRSingleton : C.R = {(L'.a 7).1} := by
                obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hRCard
                have heq : (L'.a 7).1 = r0 := by simpa [hr0] using L'.a_r
                simp [hr0, heq]
              have hDegrees := LowExactBridge.pDegrees_eight_of_totals G C q
                L' hqQ hMin hCaptured' (by omega)
              have hOrderedP := LowExactBridge.orderedP_true_of_exact_degrees
                G C q L' hG hPOrder' hDegrees
              have hOrderedX := LowExactBridge.orderedXOnly_true G C q L'
                hXOrder'
              have hOrderedE := LowExactBridge.orderedETail_true G C q L'
                hEOrder'
              exact LowExactBridge.cOneMOne_false G hBound C q L' hqQ hG hMin
                hPivot hNoSeymour hNoRoot hRootZero heZero'Full hB hRSingleton
                hk hr hXCard hQ hAOneQ hAux.symm hq0' hq1' hOrderedP
                hOrderedX hOrderedE hCaptured' hPE17 hPP15 hPH16 hHP20 W rfl
                hWCard rfl
            rcases hExactly with hFirst | hSecond
            · exact finish low heZeroLow hFirst.1 hFirst.2 hPOrder hXOrder
                hEOrder
            · let low' := Labels.swapAOne G C ({q} ∪ C.Z) low
              have heZero' : (low'.e 0).1 = q := by
                change ((Labels.swapAOne G C ({q} ∪ C.Z) low).e 0).1 = q
                rw [Labels.swapAOne_e]
                exact heZeroLow
              have hq0' : G.Adj (low'.h 0).1 q := by
                change G.Adj
                  ((Labels.swapAOne G C ({q} ∪ C.Z) low).h 0).1 q
                rw [Labels.swapAOne_h_zero]
                exact hSecond.2
              have hq1' : ¬G.Adj (low'.h 1).1 q := by
                change ¬G.Adj
                  ((Labels.swapAOne G C ({q} ∪ C.Z) low).h 1).1 q
                rw [Labels.swapAOne_h_one]
                exact hSecond.1
              have hPOrder' : ∀ i : Fin 5,
                  pKey G C ({q} ∪ C.Z)
                      (low'.p ⟨i.val + 1, by omega⟩).1 ≤
                    pKey G C ({q} ∪ C.Z)
                      (low'.p ⟨i.val, by omega⟩).1 := by
                intro i
                change pKey G C ({q} ∪ C.Z)
                    ((Labels.swapAOne G C ({q} ∪ C.Z) low).p
                      ⟨i.val + 1, by omega⟩).1 ≤
                  pKey G C ({q} ∪ C.Z)
                    ((Labels.swapAOne G C ({q} ∪ C.Z) low).p
                      ⟨i.val, by omega⟩).1
                rw [Labels.swapAOne_p]
                simpa [low, L, E] using hPOrder i
              have hXOrder' : ∀ i : Fin 3,
                  RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
                      (low'.h ⟨i.val + 3, by omega⟩).1 ≤
                    RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
                      (low'.h ⟨i.val + 2, by omega⟩).1 := by
                intro i
                have hFix (j : Fin 6) (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
                    (Labels.swapAOne G C ({q} ∪ C.Z) low).h j = low.h j := by
                  change low.h ((Equiv.swap 0 1) j) = low.h j
                  rw [Equiv.swap_apply_of_ne_of_ne hj0 hj1]
                have hx3 :
                    (Labels.swapAOne G C ({q} ∪ C.Z) low).h
                        ⟨i.val + 3, by omega⟩ =
                      low.h ⟨i.val + 3, by omega⟩ := by
                  apply hFix
                  · intro h
                    have hv := congrArg Fin.val h
                    norm_num at hv
                  · intro h
                    have hv := congrArg Fin.val h
                    norm_num at hv
                    omega
                have hx2 :
                    (Labels.swapAOne G C ({q} ∪ C.Z) low).h
                        ⟨i.val + 2, by omega⟩ =
                      low.h ⟨i.val + 2, by omega⟩ := by
                  apply hFix
                  · intro h
                    have hv := congrArg Fin.val h
                    norm_num at hv
                  · intro h
                    have hv := congrArg Fin.val h
                    norm_num at hv
                    omega
                change RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
                    ((Labels.swapAOne G C ({q} ∪ C.Z) low).h
                      ⟨i.val + 3, by omega⟩).1 ≤
                  RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
                    ((Labels.swapAOne G C ({q} ∪ C.Z) low).h
                      ⟨i.val + 2, by omega⟩).1
                rw [hx3, hx2]
                simpa [low, L, E] using hXOrder i
              have hEOrder' : eIncoming G (fun i => (low'.p i).1)
                    (low'.e 2).1 ≤
                  eIncoming G (fun i => (low'.p i).1) (low'.e 1).1 := by
                change eIncoming G
                    (fun i => ((Labels.swapAOne G C ({q} ∪ C.Z) low).p i).1)
                    ((Labels.swapAOne G C ({q} ∪ C.Z) low).e 2).1 ≤
                  eIncoming G
                    (fun i => ((Labels.swapAOne G C ({q} ∪ C.Z) low).p i).1)
                    ((Labels.swapAOne G C ({q} ∪ C.Z) low).e 1).1
                rw [Labels.swapAOne_p, Labels.swapAOne_e]
                simpa [low, L, E] using hEOrder
              exact finish low' heZero' hq0' hq1' hPOrder' hXOrder' hEOrder'
          · have hcTwo : c = 2 := by omega
            have hab : alpha + beta ≤ 1 := by omega
            have hPH17 : edgeCount G C.P C.H = 17 - alpha := by omega
            let L' := MTwoProjectedBridge.labels G C q hqQ hPCard hHCard
              hAOneCard hXCard hZCard hRCard hACard
              (MTwoProjectedBridge.paddedOutsideLabels W)
            have heZero : (L'.low.e 0).1 = q := by
              change ((Labels.reachedLabels G C q hqQ hPCard hHCard
                hAOneCard hXCard hZCard).e 0).1 = q
              exact Labels.reachedLabels_e_zero G C q hqQ hPCard hHCard
                hAOneCard hXCard hZCard
            have hRSingleton : C.R = {(L'.a 7).1} := by
              obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hRCard
              have heq : (L'.a 7).1 = r0 := by simpa [hr0] using L'.a_r
              simp [hr0, heq]
            have hAOneQ : edgeCount G C.A1 {q} = 2 := by
              dsimp [c] at hcTwo
              exact hcTwo
            have hqBoth := aOne_both_labeled G C q ({q} ∪ C.Z) L'.low
              hAOneCard hAOneQ
            exact LowExactBridge.cTwoMOne_false G hBound C q L' hqQ hG hMin
              hPivot hNoSeymour hRootZero heZero hB hRSingleton hk hr
              hqBoth.1 hqBoth.2 hCaptured' alpha beta hab hPE17 hPP hPH17
              (by omega) W rfl hWCard rfl
    · have hmTwo : m = 2 := by omega
      have hcTwo : c = 2 := by omega
      have hAlphaZero : alpha = 0 := by omega
      have hBetaZero : beta = 0 := by omega
      have hPE16 : edgeCount G C.P ({q} ∪ C.Z) = 16 := by
        simpa [E] using (show edgeCount G C.P E = 16 by omega)
      have hPP15 : edgeCount G C.P C.P = 15 := by omega
      have hPH17 : edgeCount G C.P C.H = 17 := by omega
      have hHP19 : 19 ≤ edgeCount G C.H C.P := by omega
      let W := MTwoProjectedBridge.outsideSet G C q
      let L := MTwoProjectedBridge.labels G C q hqQ hPCard hHCard
        hAOneCard hXCard hZCard hRCard hACard
        (MTwoProjectedBridge.paddedOutsideLabels W)
      have heZero : (L.low.e 0).1 = q := by
        change ((Labels.reachedLabels G C q hqQ hPCard hHCard hAOneCard
          hXCard hZCard).e 0).1 = q
        exact Labels.reachedLabels_e_zero G C q hqQ hPCard hHCard
          hAOneCard hXCard hZCard
      have hB : C.B = C.P ∪ {q} := by
        rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C, hQ]
      have hRSingleton : C.R = {(L.a 7).1} := by
        obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hRCard
        have heq : (L.a 7).1 = r0 := by simpa [hr0] using L.a_r
        simp [hr0, heq]
      have hAOneQ : edgeCount G C.A1 {q} = 2 := by
        dsimp [c] at hcTwo
        exact hcTwo
      have hqBoth := aOne_both_labeled G C q ({q} ∪ C.Z) L.low
        hAOneCard hAOneQ
      have hCaptured' : ∀ p ∈ C.P,
          G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z) := by
        simpa [hAux] using hCaptured
      have hDegrees := LowExactBridge.pDegrees_eight_of_totals G C q L hqQ
        hMin hCaptured' (by omega)
      have hWCard : W.card ≤ 7 := by
        simpa [W] using MTwoProjectedBridge.outsideSet_card_le_seven G C q L
          hqQ hMin hNoSeymour hCaptured' hPE16 hPP15 hPH17
      exact MTwoProjectedBridge.exactTwo_false G hBound C q L hqQ hG hMin
        hPivot hNoSeymour hRootZero heZero hB hRSingleton hk hr hqBoth.1
        hqBoth.2 hCaptured' hPE16 hPP15 hPH17 hHP19 hDegrees W rfl
        hWCard rfl

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot
