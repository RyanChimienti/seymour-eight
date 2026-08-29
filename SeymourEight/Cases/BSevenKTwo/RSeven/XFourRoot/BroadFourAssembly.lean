import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.BroadFourGraphFacts
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge
import SeymourEight.Cases.BSevenKTwo.Counting
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Assembly of the broad four-`Z` certificate

This file projects a genuine local configuration to the symmetry-normalized
Boolean core.  The certificate itself remains isolated in `BroadFour`.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge

open Shared XFourNoRoot.BroadFourCore BroadFourLabels
open XFourNoRoot.IndividualEffective XFourNoRoot.RepeatedSharedOmissionBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (C : G.LocalConfiguration) (L : Labels G C) :=
  XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem orientedA_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) :
    orientedA (graphBits G C L) = true := by
  rw [orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true, XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ i i hi hi]
  constructor
  · simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ i j hi hj,
      XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    · by_cases h : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
      · simp [h, hG.2 h]
      · simp [h]

theorem orientedP_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) :
    orientedP (graphBits G C L) = true := by
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [XFourNoRoot.BroadFourBridge.pArc_coreBits G.Adj _ _ _ i j hi hj,
    XFourNoRoot.BroadFourBridge.pArc_coreBits G.Adj _ _ _ j i hj hi]
  by_cases hij : i = j
  · simp [hij]
  · by_cases h : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
    · simp [hij, h, hG.2 h]
    · simp [hij, h]

theorem orientedPH_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) :
    orientedPH (graphBits G C L) = true := by
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  rw [XFourNoRoot.BroadFourBridge.pToH_coreBits G.Adj _ _ _ p h hp hh,
    XFourNoRoot.BroadFourBridge.hToP_coreBits G.Adj _ _ _ h p hh hp]
  by_cases ha : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1
  · simp [ha, hG.2 ha]
  · simp [ha]

theorem fixedA_true (C : G.LocalConfiguration)
    (L : Labels G C) (_hG : G.IsOriented) :
    fixedA (graphBits G C L) = true := by
  let bits := graphBits G C L
  have h01 : aArc bits 0 1 = true := by
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 0 1 (by omega) (by omega)]
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      simpa using L.a_zero
    rw [ha0]
    simpa using (Finset.mem_filter.mp (L.a_aOne 0)).2
  have h02 : aArc bits 0 2 = true := by
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 0 2 (by omega) (by omega)]
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      simpa using L.a_zero
    rw [ha0]
    simpa using (Finset.mem_filter.mp (L.a_aOne 1)).2
  have hTail : all 5 (fun i => !aArc bits 0 (3 + i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 0 (3 + i) (by omega) (by omega)]
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      simpa using L.a_zero
    rw [ha0]
    by_cases hi4 : i < 4
    · have hx := L.a_x ⟨i, hi4⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hA1
            (by simpa [Nat.add_comm] using hx)
      simp [hn]
    · have hiEq : i = 4 := by omega
      subst i
      have hn : ¬G.Adj C.a1 (L.a 7).1 := by
        intro ha
        have hA1 : (L.a 7).1 ∈ C.A1 := Finset.mem_filter.mpr ⟨(L.a 7).2, ha⟩
        exact (Finset.mem_sdiff.mp L.a_r).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
      simp [hn]
  have h17Arc : aArc bits 1 7 = false := by
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 1 7 (by omega) (by omega)]
    exact decide_eq_false (by
      simpa using A1_not_adj_R G C _ _ (L.a_aOne 0) L.a_r)
  have h27Arc : aArc bits 2 7 = false := by
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 2 7 (by omega) (by omega)]
    exact decide_eq_false (by
      simpa using A1_not_adj_R G C _ _ (L.a_aOne 1) L.a_r)
  have h17 : (!aArc bits 1 7) = true := by simp [h17Arc]
  have h27 : (!aArc bits 2 7) = true := by simp [h27Arc]
  simp only [fixedA, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h01, h02⟩, hTail⟩, h17⟩, h27⟩

theorem everyXReached_true (C : G.LocalConfiguration)
    (L : Labels G C) (hk : C.k = 2) :
    everyXReached (graphBits G C L) = true := by
  rw [everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    have hPairSubset : ({(L.a (1 : Fin 8)).1, (L.a (2 : Fin 8)).1} :
        Finset V) ⊆ C.A1 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact L.a_aOne 0
      · exact L.a_aOne 1
    have hPairCard : ({(L.a (1 : Fin 8)).1, (L.a (2 : Fin 8)).1} :
        Finset V).card = 2 := by
      have hne : (L.a (1 : Fin 8)).1 ≠ (L.a (2 : Fin 8)).1 := by
        intro h
        have := L.a.injective (Subtype.ext h)
        omega
      simp [hne]
    have hA1Card : C.A1.card = 2 := hk
    have hEq := Finset.eq_of_subset_of_card_le hPairSubset (by omega)
    have huCases : u = (L.a (1 : Fin 8)).1 ∨
        u = (L.a (2 : Fin 8)).1 := by
      rw [← hEq] at huA1
      simpa [eq_comm] using huA1
    rcases huCases with h1 | h2
    · refine ⟨0, by omega, ?_⟩
      rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 1 (3 + x) (by omega) (by omega)]
      simpa [Nat.add_comm, h1] using hux
    · refine ⟨1, by omega, ?_⟩
      rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ 2 (3 + x) (by omega) (by omega)]
      simpa [Nat.add_comm, h2] using hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨pi, hpi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨pi, pi.isLt, ?_⟩
    rw [XFourNoRoot.BroadFourBridge.pToH_coreBits G.Adj _ _ _ pi (2 + x) pi.isLt (by omega)]
    simpa [Nat.add_comm, Nat.add_left_comm, congrArg Subtype.val hpi] using hux

theorem allZReached_true (C : G.LocalConfiguration)
    (L : Labels G C) : allZReached (graphBits G C L) = true := by
  rw [allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := (L.z ⟨z, hz⟩).2
  rcases Finset.mem_union.mp hzMem with hzMem | hRootMem
  · rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
    obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [XFourNoRoot.BroadFourBridge.pToZ_coreBits G.Adj _ _ _ i z i.isLt hz]
    simpa [congrArg Subtype.val hi] using hpz
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · obtain ⟨p, hp, hps⟩ := hReach
      have hLabel : (L.z ⟨z, hz⟩).1 = C.s := by
        simpa [rootSecondFinset, show ∃ q ∈ C.P, G.Adj q C.s from ⟨p, hp, hps⟩]
          using hRootMem
      obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [XFourNoRoot.BroadFourBridge.pToZ_coreBits G.Adj _ _ _ i z i.isLt hz]
      simpa [hLabel, congrArg Subtype.val hi] using hps
    · simp [rootSecondFinset, hReach] at hRootMem

noncomputable def xLabelEquiv (C : G.LocalConfiguration)
    (L : Labels G C) (hXCard : C.X.card = 4) :
    Fin 4 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 4 → {v : V // v ∈ C.X} := fun i =>
    ⟨(L.a ⟨i.1 + 3, by omega⟩).1, L.a_x i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.1 + 3, by omega⟩ : Fin 8) = ⟨j.1 + 3, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval : i.1 + 3 = j.1 + 3 := congrArg Fin.val ha
    omega
  · simpa using hXCard.symm

noncomputable def aOneLabelEquiv (C : G.LocalConfiguration)
    (L : Labels G C) (hk : C.k = 2) :
    Fin 2 ≃ {v : V // v ∈ C.A1} := by
  let f : Fin 2 → {v : V // v ∈ C.A1} := fun i =>
    ⟨(L.a ⟨i.1 + 1, by omega⟩).1, L.a_aOne i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.1 + 1, by omega⟩ : Fin 8) = ⟨j.1 + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval : i.1 + 1 = j.1 + 1 := congrArg Fin.val ha
    omega
  · change C.A1.card = 2 at hk
    simpa using hk.symm

theorem three_le_aOneToXCount (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hXCard : C.X.card = 4) :
    3 ≤ (count 8 fun q =>
      let a := q / 4
      let x := q % 4
      aArc (graphBits G C L) (1 + a) (3 + x)).toNat := by
  have hA1Card : C.A1.card = 2 := hk
  have hA1Internal : edgeCount G C.A1 C.A1 ≤ 1 := by
    have h := internal_edgeCount_le_choose_two G C.A1 hG
    norm_num [hA1Card, Nat.choose] at h ⊢
    exact h
  have hA1A : 4 ≤ edgeCount G C.A1 C.A := by
    unfold edgeCount
    calc
      4 = ∑ _u ∈ C.A1, 2 := by simp [hA1Card]
      _ ≤ ∑ u ∈ C.A1, Shared.directCount G C.A u := by
        apply Finset.sum_le_sum
        intro u hu
        have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C hu
        simpa [hk, Shared.directCount,
          CertificateBridge.internalFirstNeighbors] using
          (hPivot u huA).1
  have hA1RZero : edgeCount G C.A1 C.R = 0 := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr
    exact A1_not_adj_R G C u r hu hr
  have hA1a1Zero : edgeCount G C.A1 {C.a1} = 0 := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro u hu
    have hnot : ¬G.Adj u C.a1 := hG.2 (Finset.mem_filter.mp hu).2
    simp [hnot]
  have hPartsR := Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hHa1 : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hv
    rcases Finset.mem_singleton.mp hv with rfl
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  have hADecomp : edgeCount G C.A1 C.A =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X := by
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C,
      edgeCount_union_of_disjoint G C.A1 (C.A1 ∪ C.X ∪ {C.a1}) C.R hPartsR,
      edgeCount_union_of_disjoint G C.A1 (C.A1 ∪ C.X) {C.a1} hHa1,
      edgeCount_union_of_disjoint G C.A1 C.A1 C.X
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C),
      hA1RZero, hA1a1Zero]
    omega
  have hThree : 3 ≤ edgeCount G C.A1 C.X := by omega
  have hRow (a : Fin 2) :
      Shared.directCount G C.X (L.a ⟨a.1 + 1, by omega⟩).1 =
        ∑ x : Fin 4, if aArc (graphBits G C L)
          (1 + a.1) (3 + x.1) then 1 else 0 := by
    apply directCount_eq_sum_bool G C.X (xLabelEquiv G C L hXCard)
    intro x
    rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ (1 + a.1) (3 + x.1)
      (by omega) (by omega)]
    simp [xLabelEquiv, Nat.add_comm]
  have hCount : (count 8 fun q =>
      let a := q / 4
      let x := q % 4
      aArc (graphBits G C L) (1 + a) (3 + x)).toNat =
      edgeCount G C.A1 C.X := by
    rw [toNat_count_eq_fin_sum 8 _ (by omega),
      edgeCount_eq_sum_fin G C.A1 C.X (aOneLabelEquiv G C L hk)]
    simp_rw [show ∀ i : Fin 2,
      (aOneLabelEquiv G C L hk i).1 = (L.a ⟨i.1 + 1, by omega⟩).1 by
        intro i; rfl]
    simp_rw [hRow]
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  omega

theorem A_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = Shared.directCount G C.A u +
      Shared.directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hCap := A_outgoingCaptured G C hG u hu
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.P) u (by
    intro v hv
    simpa [hPB] using hCap hv)
  rw [directCount_union_of_disjoint G C.A C.P u hAP] at hEq
  exact hEq

theorem aMinimumAndDegree_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 2) :
    aMinimumAndDegree (graphBits G C L) = true := by
  let bits := graphBits G C L
  rw [aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L a ha
  have hPO := aPOut_toNat G C L hG a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 2 ≤ (aOut bits a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut bits a).toNat = 2 →
      7 ≤ (aPOut bits a).toNat := by
    intro heq
    rw [hPO]
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change Shared.directCount G C.A (L.a ⟨a, ha⟩).1 = 2
      rw [← hAO]
      exact heq
    have hTieB := hPivotA.2 hCardEq
    change C.r ≤ Shared.directCount G C.B (L.a ⟨a, ha⟩).1 at hTieB
    rw [← hPB] at hTieB
    have hr : C.r = 7 := by
      change C.P.card = 7
      simpa using (Fintype.card_congr L.p).symm
    simpa [hr] using hTieB
  have hTotal : 8 ≤ (aOut bits a).toNat + (aPOut bits a).toNat := by
    rw [hAO, hPO,
      ← A_outdegree_eq_A_add_P G C hG hPB _ (L.a _).2]
    exact hMin _
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
      exact hAmin
    · rw [Bool.or_eq_true]
      by_cases heq : aOut bits a = 2
      · right
        norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
        exact hTie (congrArg BitVec.toNat heq)
      · left
        simpa using heq
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [BitVec.toNat_add]
    have hlt : (aOut bits a).toNat + (aPOut bits a).toNat < 256 := by
      have hA : Shared.directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hP : Shared.directCount G C.P (L.a ⟨a, ha⟩).1 ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [hAO, hPO]
      have hcA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
      have hcP : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
      omega
    rw [Nat.mod_eq_of_lt hlt]
    exact hTotal

theorem pMinimumDegree_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 6)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    pMinimumDegree (graphBits G C L) = true := by
  let bits := graphBits G C L
  rw [pMinimumDegree, all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C L hG hHCard p hp
  have hCaptured : G.outNeighborFinset (L.p ⟨p, hp⟩).1 ⊆
      (externalTargets G C) ∪ C.H ∪ C.P := by
    intro v hv
    have huv := (Digraph.mem_outNeighborFinset (G := G)).mp hv
    have hc := outgoingCaptured_of_p_eq_B G C hG hPB _ (L.p _).2 hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hc ⊢
    rcases hc with ((hz | hs) | hh) | hp'
    · exact Or.inl (Or.inl (Finset.mem_union_left _ hz))
    · subst v
      exact Or.inl (Or.inl (Finset.mem_union_right _ (by
        simp [rootSecondFinset,
          show ∃ q ∈ C.P, G.Adj q C.s from ⟨(L.p ⟨p, hp⟩).1, (L.p _).2, huv⟩])))
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hp'
  have hZH : Disjoint (externalTargets G C) C.H := by
    rw [Finset.disjoint_left]
    intro v hvE hvH
    rcases Finset.mem_union.mp hvE with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
      · simp [rootSecondFinset, hReach] at hvRoot
  have hZHP : Disjoint ((externalTargets G C) ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hvZH hvP
    rcases Finset.mem_union.mp hvZH with hvZ | hvH
    · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
      · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
        · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
        · simp [rootSecondFinset, hReach] at hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  have hGraph : G.outdegree (L.p ⟨p, hp⟩).1 =
      Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.P (L.p ⟨p, hp⟩).1 := by
    have h := outdegree_eq_directCount_of_captured G ((externalTargets G C) ∪ C.H ∪ C.P)
      (L.p ⟨p, hp⟩).1 hCaptured
    rw [directCount_union_of_disjoint G ((externalTargets G C) ∪ C.H) C.P _ hZHP,
      directCount_union_of_disjoint G (externalTargets G C) C.H _ hZH] at h
    exact h
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have hSmall : (pOut bits p).toNat + (pHOut bits p).toNat < 256 := by
    have hP : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hH : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [hBlocks.1, hBlocks.2.1]
    have hcP : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    omega
  rw [Nat.mod_eq_of_lt hSmall]
  have hSmall' : (pOut bits p).toNat + (pHOut bits p).toNat +
      (pZOut bits p).toNat < 256 := by
    have hP : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hH : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hZ : Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    have hcP : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hcZ : (externalTargets G C).card = 4 := by simpa using (Fintype.card_congr L.z).symm
    omega
  rw [Nat.mod_eq_of_lt hSmall']
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  change 8 ≤ _
  have hDegree := hMin (L.p ⟨p, hp⟩).1
  omega

theorem aNonSeymour_all_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 8 (aNonSeymour (graphBits G C L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  exact nonSeymour_coreBits_true G C L hG hPB hNoSeymour a (by omega)

theorem pNonSeymour_all_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 7 (pNonSeymour (graphBits G C L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  exact nonSeymour_coreBits_true G C L hG hPB hNoSeymour (8 + p)
    (by omega)

theorem directZEffectiveStrict_subset_second (C : G.LocalConfiguration)
    (p : V) (hpP : p ∈ C.P) :
    directZEffectiveUnion G C p \ G.outNeighborFinset p ⊆
      G.secondOutNeighborFinset p := by
  intro v hv
  rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvNotDirect⟩
  rcases Finset.mem_sdiff.mp hvU with ⟨hvReached, hvOutside⟩
  obtain ⟨z, hzS, hzv⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached
  have hpz : G.Adj p z := (Finset.mem_filter.mp hzS).2
  have hpv : ¬G.Adj p v := by
    simpa only [Digraph.mem_outNeighborFinset] using hvNotDirect
  have hvp : v ≠ p := by
    intro hEq
    subst v
    exact hvOutside (Finset.mem_union_left _ hpP)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨z, hpz, hzv⟩, hpv, hvp⟩

theorem directZEffective_direct_subset_H (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : V) (hpP : p ∈ C.P) (hps : ¬G.Adj p C.s) :
    directZEffectiveUnion G C p ∩ G.outNeighborFinset p ⊆
      C.H.filter (G.Adj p) := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvU, hvDirect⟩
  have hpv : G.Adj p v := by
    simpa only [Digraph.mem_outNeighborFinset] using hvDirect
  have hvCaptured := outgoingCaptured_of_p_eq_B G C hG hPB p hpP hvDirect
  have hvOutside := (Finset.mem_sdiff.mp hvU).2
  simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
  apply Finset.mem_filter.mpr
  refine ⟨?_, hpv⟩
  rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
  · have hvS : v ∈ FiveZUnionEightCapacity.directZNeighbors G C p :=
      Finset.mem_filter.mpr ⟨hvZ, hpv⟩
    exact (hvOutside (Finset.mem_union_right _ hvS)).elim
  · subst v
    exact (hps hpv).elim
  · exact hvH
  · exact (hvOutside (Finset.mem_union_left _ hvP)).elim

theorem PSecond_add_directZEffective_card_le_second_add_H
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : V) (hpP : p ∈ C.P) (hps : ¬G.Adj p C.s) :
    (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset p).card +
        (directZEffectiveUnion G C p).card ≤
      G.secondOutdegree p + Shared.directCount G C.H p := by
  let U := directZEffectiveUnion G C p
  let N := G.outNeighborFinset p
  let PS := C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset p
  let Strict := U \ N
  let Direct := U ∩ N
  have hStrict : Strict ⊆ G.secondOutNeighborFinset p := by
    simpa [Strict, U, N] using
      directZEffectiveStrict_subset_second G C p hpP
  have hPS : PS ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hDisjoint : Disjoint PS Strict := by
    rw [Finset.disjoint_left]
    intro v hvPS hvStrict
    have hvP := (Finset.mem_filter.mp hvPS).1
    have hvU := (Finset.mem_sdiff.mp hvStrict).1
    exact (Finset.mem_sdiff.mp hvU).2 (Finset.mem_union_left _ hvP)
  have hSecondUnion : PS ∪ Strict ⊆ G.secondOutNeighborFinset p :=
    Finset.union_subset hPS hStrict
  have hSecondCard : PS.card + Strict.card ≤ G.secondOutdegree p := by
    change PS.card + Strict.card ≤ (G.secondOutNeighborFinset p).card
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hSecondUnion
  have hDirect : Direct ⊆ C.H.filter (G.Adj p) := by
    simpa [Direct, U, N] using
      directZEffective_direct_subset_H G C hG hPB p hpP hps
  have hDirectCard : Direct.card ≤ Shared.directCount G C.H p := by
    unfold Shared.directCount CertificateBridge.internalFirstNeighbors
    exact Finset.card_le_card hDirect
  have hSplit := Finset.card_sdiff_add_card_inter U N
  change Strict.card + Direct.card = U.card at hSplit
  change PS.card + U.card ≤
    G.secondOutdegree p + Shared.directCount G C.H p
  omega

theorem pSecondPCount_le_graphPSecond (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (p : Nat) (hp : p < 7) :
    (pSecondPCount (graphBits G C L) p).toNat ≤
      (C.P.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply count_le_filterCard C.P L.p
    (fun q ↦ strictSecondLocal (graphBits G C L) (8 + p) (8 + q))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro j hj
  have hmem := strictSecondLocal_true_mem G C L hG (8 + p) (8 + j)
    (by omega) (by omega) hj
  simpa [labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
    show 8 + j.val < 15 by omega] using hmem

theorem pSecondPCount_le_qCount (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (p : Nat) (hp : p < 7) :
    (pSecondPCount (graphBits G C L) p).toNat ≤
      TerminalAlphaBeta.qCount G C.P C.H (L.p ⟨p, hp⟩).1 := by
  unfold pSecondPCount TerminalAlphaBeta.qCount
  unfold TerminalAlphaBeta.secondNeighborsThrough
  apply count_le_filterCard C.P L.p
    (fun q => strictSecondLocal (graphBits G C L) (8 + p) (8 + q))
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
    have hTrue : coreArc (graphBits G C L) (8 + p) (8 + j.val) = true := by
      rw [coreArc_coreBits G C L hG (8 + p) (8 + j.val) (by omega) (by omega)]
      exact decide_eq_true (by
        simpa [labelledVertex, show ¬8 + p < 8 by omega,
          show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
          show 8 + j.val < 15 by omega] using hAdj)
    simp [hTrue] at hNotDirect
  have hFirstGraph : G.Adj (L.p ⟨p, hp⟩).1 (labelledVertex G L middle) := by
    have hFirst' := hFirst
    rw [coreArc_coreBits G C L hG (8 + p) middle (by omega) (by omega)] at hFirst'
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 15 by omega] using hFirst'
  have hSecondGraph : G.Adj (labelledVertex G L middle) (L.p j).1 := by
    have hSecond' := hSecond
    rw [coreArc_coreBits G C L hG middle (8 + j.val) (by omega) (by omega)] at hSecond'
    simpa [labelledVertex, show ¬8 + j.val < 8 by omega,
      show 8 + j.val < 15 by omega] using hSecond'
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
      have hmSeven : middle ≠ 7 := by
        intro hm
        subst middle
        exact (XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R G C
          (L.p ⟨p, hp⟩).1 (L.a 7).1 (L.p _).2 L.a_r) hFirstGraph
      by_cases hmSmall : middle < 3
      · have hi : middle - 1 < 2 := by omega
        have hIdx : (⟨middle, hmA⟩ : Fin 8) = ⟨(middle - 1) + 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [hIdx]
        exact Finset.mem_union_left C.X (L.a_aOne ⟨middle - 1, hi⟩)
      · have hi : middle - 3 < 4 := by omega
        have hIdx : (⟨middle, hmA⟩ : Fin 8) = ⟨(middle - 3) + 3, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [hIdx]
        exact Finset.mem_union_right C.A1 (L.a_x ⟨middle - 3, hi⟩)
    · apply Finset.mem_union_left
      simp [labelledVertex, hmA, show middle < 15 by omega]
  exact ⟨hNotAdj, hTargetNe,
    labelledVertex G L middle, hMiddle, hFirstGraph, hSecondGraph⟩


theorem external_row_missing_le_total (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hECard : (externalTargets G C).card = 4)
    (p : V) (hpP : p ∈ C.P) :
    4 - directCount G (externalTargets G C) p ≤
      28 - edgeCount G C.P (externalTargets G C) := by
  have hOther : ∑ q ∈ C.P.erase p,
      directCount G (externalTargets G C) q ≤ 24 := by
    calc
      _ ≤ ∑ _q ∈ C.P.erase p, 4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
      _ = 24 := by simp [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit := Finset.sum_erase_add C.P
    (fun q => directCount G (externalTargets G C) q) hpP
  have hBound : edgeCount G C.P (externalTargets G C) ≤
      24 + directCount G (externalTargets G C) p := by
    unfold edgeCount
    omega
  have hTotal := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, hECard] at hTotal
  omega

theorem directZ_to_P_capacity_external (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 7)
    (hECard : (externalTargets G C).card = 4)
    (p : V) (hpP : p ∈ C.P) (hps : ¬G.Adj p C.s) :
    edgeCount G (FiveZUnionEightCapacity.directZNeighbors G C p) C.P ≤
      (28 - edgeCount G C.P (externalTargets G C)) -
        (4 - (FiveZUnionEightCapacity.directZNeighbors G C p).card) := by
  let S := FiveZUnionEightCapacity.directZNeighbors G C p
  let E := externalTargets G C
  let T := E \ S
  have hS : S ⊆ E := fun z hz => Finset.mem_union_left _
    (FiveZUnionEightCapacity.directZNeighbors_subset_Z G C p hz)
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = E := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 4 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hECard]
  have hpT : Shared.directCount G T p = 0 := by
    unfold Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.card_eq_zero.mpr
    ext z
    simp only [Finset.notMem_empty, iff_false]
    intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzT, hpz⟩
    have hzE := (Finset.mem_sdiff.mp hzT).1
    rcases Finset.mem_union.mp hzE with hzZ | hzRoot
    · exact (Finset.mem_sdiff.mp hzT).2 (Finset.mem_filter.mpr ⟨hzZ, hpz⟩)
    · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
      · have hzs : z = C.s := by simpa [rootSecondFinset, hReach] using hzRoot
        exact hps (hzs ▸ hpz)
      · simp [rootSecondFinset, hReach] at hzRoot
  have hPT : edgeCount G C.P T ≤ 6 * T.card := by
    calc
      _ ≤ ∑ q ∈ C.P, if q = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqp : q = p
        · subst q; simp [hpT]
        · simp only [hqp, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 * T.card := by
        rw [← Finset.sum_erase_add C.P
          (fun q => if q = p then 0 else T.card) hpP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ x ∈ C.P.erase p, if x = p then 0 else T.card) =
              ∑ _x ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_neg (Finset.mem_erase.mp hx).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 6 * T.card := by rw [Finset.card_erase_of_mem hpP, hPCard]
  have hPESplit : edgeCount G C.P E =
      edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = 4 := by
    rw [hTCard]
    have := (Finset.card_le_card hS).trans_eq hECard
    omega
  have hPEUpper := edgeCount_le_card_mul_card G C.P E
  rw [hPCard, hECard] at hPEUpper
  change edgeCount G S C.P ≤
    (28 - edgeCount G C.P E) - (4 - S.card)
  omega

theorem totalPToZ_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 6) :
    (totalPToZ (graphBits G C L)).toNat = edgeCount G C.P (externalTargets G C) := by
  let bits := graphBits G C L
  rw [totalPToZ, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pZOut bits i).toNat =
      Shared.directCount G (externalTargets G C) (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hG hHCard i i.isLt).2.2
  have hSum : (∑ i ∈ Finset.range 7, (pZOut bits i).toNat) =
      edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_eq_sum_fin G C.P (externalTargets G C) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = 4 := by simpa using (Fintype.card_congr L.z).symm
  rw [hPCard, hZCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 6) :
    (externalMissing (graphBits G C L)).toNat =
      28 - edgeCount G C.P (externalTargets G C) := by
  rw [externalMissing, BitVec.toNat_sub, totalPToZ_toNat G C L hG hHCard]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = 4 := by simpa using (Fintype.card_congr L.z).symm
  rw [hPCard, hZCard] at hCap
  change ((256 - edgeCount G C.P (externalTargets G C) + 28) % 256) =
    28 - edgeCount G C.P (externalTargets G C)
  omega

theorem individualEffectiveLower_toNat (bits : Encoding) (p m s : Nat)
    (hm : m ≤ 10) (hs : s ≤ 4)
    (hM : (externalMissing bits).toNat = m)
    (hS : (pZOut bits p).toNat = s) :
    (individualEffectiveLower bits p).toNat = effectiveLowerNat m s := by
  have hMBV : externalMissing bits = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hSBV : pZOut bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  interval_cases m <;> interval_cases s <;>
    simp_all [individualEffectiveLower, effectiveLowerNat,
      effectiveAtRowSize]

set_option maxHeartbeats 1000000 in
-- Exhaustively normalize the bounded arithmetic table for effective capacity.
private theorem effectiveLowerNat_of_external_capacity
    (m s u eZ eP : Nat) (hm : m ≤ 10) (hs : s ≤ 4)
    (hFeasible : 4 - s ≤ m)
    (hLower : s * (8 - u) ≤ eZ + eP)
    (hZ : eZ ≤ s.choose 2) (hP : eP ≤ m - (4 - s)) :
    effectiveLowerNat m s ≤ u := by
  by_cases hu : 8 ≤ u
  · interval_cases m <;> interval_cases s <;>
      simp_all [effectiveLowerNat, Nat.choose] <;> omega
  · have hu' : u ≤ 7 := by omega
    interval_cases m <;> interval_cases s <;> interval_cases u <;>
      simp_all [effectiveLowerNat, Nat.choose] <;> omega

set_option maxHeartbeats 1000000 in
-- The graph bridge expands the same bounded table in each canonical row.
theorem individualEffectiveLower_graph (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 6) (hPCard : C.P.card = 7)
    (hECard : (externalTargets G C).card = 4)
    (hmBound : 28 - edgeCount G C.P (externalTargets G C) ≤ 10)
    (p : Nat) (hp : p < 7)
    (hps : ¬G.Adj (L.p ⟨p, hp⟩).1 C.s) :
    (individualEffectiveLower (graphBits G C L) p).toNat ≤
      (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G C L
  let v := (L.p ⟨p, hp⟩).1
  let S := FiveZUnionEightCapacity.directZNeighbors G C v
  let U := directZEffectiveUnion G C v
  let m := 28 - edgeCount G C.P (externalTargets G C)
  let s := S.card
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ 4 := by
    have hZSubE : C.Z ⊆ externalTargets G C := Finset.subset_union_left
    exact (Finset.card_le_card ((FiveZUnionEightCapacity.directZNeighbors_subset_Z
      G C v).trans hZSubE)).trans_eq hECard
  have hCapacity := directZ_effective_capacity_lower G C hMin v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directZ_to_P_capacity_external G C hG hPCard hECard v hvP hps
  have hRow := external_row_missing_le_total G C hPCard hECard v hvP
  have hM : (externalMissing bits).toNat = m :=
    externalMissing_toNat G C L hG hHCard
  have hS : (pZOut bits p).toNat = s := by
    rw [(pBlockCounts G C L hG hHCard p hp).2.2,
      SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets G C v hvP]
    have hps' : ¬G.Adj v C.s := by simpa [v] using hps
    rw [show epsilonAt G v C.s = 0 by simp [epsilonAt, hps'], Nat.add_zero]
    exact (FiveZUnionEightCapacity.card_directZNeighbors G C v).symm
  have hES : Shared.directCount G (externalTargets G C) v = s := by
    rw [← (pBlockCounts G C L hG hHCard p hp).2.2, hS]
  rw [hES] at hRow
  have hTable := individualEffectiveLower_toNat bits p m s
    (by simpa [m] using hmBound) hs hM hS
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hCapacity
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (4 - s) at hToP
  change 4 - s ≤ m at hRow
  change (individualEffectiveLower bits p).toNat ≤ U.card
  rw [hTable]
  have hm : m ≤ 10 := by simpa [m] using hmBound
  exact effectiveLowerNat_of_external_capacity m s U.card
    (edgeCount G S S) (edgeCount G S C.P) hm hs hRow hCapacity
    hInternal hToP

theorem pEffectiveCondition_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hHCard : C.H.card = 6)
    (hPCard : C.P.card = 7) (hECard : (externalTargets G C).card = 4)
    (hmBound : 28 - edgeCount G C.P (externalTargets G C) ≤ 10) :
    all 7 (pEffectiveCondition (graphBits G C L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hBlocks := pBlockCounts G C L hG hHCard p hp
  have hNatural : (pSecondPCount (graphBits G C L) p).toNat +
      (individualEffectiveLower (graphBits G C L) p).toNat + 1 ≤
      (pOut (graphBits G C L) p).toNat + 2 * (pHOut (graphBits G C L) p).toNat +
        (pZOut (graphBits G C L) p).toNat := by
    by_cases hps : G.Adj v C.s
    · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
        G C hG hPB hNoSeymour hRootDegree v hvP hps
      have hSecond := pSecondPCount_le_qCount G C L hG p hp
      let m := 28 - edgeCount G C.P (externalTargets G C)
      let rowSize := Shared.directCount G (externalTargets G C) v
      have hm : m ≤ 10 := by simpa [m] using hmBound
      have hs : rowSize ≤ 4 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
      have hRow := external_row_missing_le_total G C hPCard hECard v hvP
      have hMNat : (externalMissing (graphBits G C L)).toNat = m :=
        externalMissing_toNat G C L hG hHCard
      have hSNat : (pZOut (graphBits G C L) p).toNat = rowSize := hBlocks.2.2
      have hTableEq := individualEffectiveLower_toNat (graphBits G C L) p m rowSize
        hm hs hMNat hSNat
      have hTable : (individualEffectiveLower (graphBits G C L) p).toNat ≤ 8 := by
        rw [hTableEq]
        change 4 - rowSize ≤ m at hRow
        interval_cases m <;> interval_cases rowSize <;>
          simp [effectiveLowerNat] at hRow ⊢
      have hEpsilon : epsilonAt G v C.s = 1 := by simp [epsilonAt, hps]
      rw [hEpsilon] at hEquation
      dsimp [v] at hSecond hEquation hTable
      change G.Adj (L.p ⟨p, hp⟩).1 C.s at hps
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      rw [SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets G C
        (L.p ⟨p, hp⟩).1 hvP]
      simp [epsilonAt, hps]
      omega
    · have hTable := individualEffectiveLower_graph G C L hG hMin hHCard
        hPCard hECard hmBound p hp hps
      have hPS := pSecondPCount_le_graphPSecond G C L hG p hp
      have hUnion := PSecond_add_directZEffective_card_le_second_add_H
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
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      omega
  simp only [pEffectiveCondition, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pSecondPCount (graphBits G C L) p).toNat +
      (individualEffectiveLower (graphBits G C L) p).toNat + 1) % 256 ≤
    ((pOut (graphBits G C L) p).toNat +
      2 * (pHOut (graphBits G C L) p).toNat +
      (pZOut (graphBits G C L) p).toNat) % 256
  have hLeftSmall : (pSecondPCount (graphBits G C L) p).toNat +
      (individualEffectiveLower (graphBits G C L) p).toNat + 1 < 256 := by
    have hSecondLe : (pSecondPCount (graphBits G C L) p).toNat ≤ 7 := by
      exact (pSecondPCount_le_graphPSecond G C L hG p hp).trans
        ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
    have hTableLe : (individualEffectiveLower (graphBits G C L) p).toNat ≤ 11 := by
      have hM := externalMissing_toNat G C L hG hHCard
      have hS := (pBlockCounts G C L hG hHCard p hp).2.2
      have hm : 28 - edgeCount G C.P (externalTargets G C) ≤ 10 := hmBound
      have hs : Shared.directCount G (externalTargets G C)
          (L.p ⟨p, hp⟩).1 ≤ 4 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
      rw [individualEffectiveLower_toNat (graphBits G C L) p
        (28 - edgeCount G C.P (externalTargets G C))
        (Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1)
        hm hs hM hS]
      interval_cases 28 - edgeCount G C.P (externalTargets G C) <;>
        interval_cases Shared.directCount G (externalTargets G C)
          (L.p ⟨p, hp⟩).1 <;> simp_all [effectiveLowerNat]
    omega
  have hRightSmall : (pOut (graphBits G C L) p).toNat +
      2 * (pHOut (graphBits G C L) p).toNat +
      (pZOut (graphBits G C L) p).toNat < 256 := by
    have hpLe : (pOut (graphBits G C L) p).toNat ≤ 7 := by
      rw [hBlocks.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hhLe : (pHOut (graphBits G C L) p).toNat ≤ 6 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have heLe : (pZOut (graphBits G C L) p).toNat ≤ 4 := by
      rw [hBlocks.2.2]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
    omega
  rw [Nat.mod_eq_of_lt hLeftSmall, Nat.mod_eq_of_lt hRightSmall]
  exact hNatural

theorem edgeCount_P_root_zero (C : G.LocalConfiguration)
    (hNoRoot : epsilonS G C = 0) : edgeCount G C.P {C.s} = 0 := by
  unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro s hs
  have hsEq : s = C.s := Finset.mem_singleton.mp hs
  subst s
  exact FiveZExactPBridge.no_P_to_s_of_epsilonS_zero G C hNoRoot p hp

theorem pRowKey_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 6)
    (p : Nat) (hp : p < 7) :
    (pRowKey (graphBits G C L) p).toNat =
      BroadFourLabels.pKey G C (L.p ⟨p, hp⟩).1 := by
  let bits := graphBits G C L
  have hBlocks := pBlockCounts G C L hG hHCard p hp
  have hDirect := directCount_coreBits_toNat G C L hG hPB (8 + p)
    (by omega)
  have hD : (XFourNoRoot.BroadFourCore.directCount bits (8 + p)).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 15 by omega] using hDirect
  unfold pRowKey BroadFourLabels.pKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pZOut bits p).toNat * 4096 +
      (XFourNoRoot.BroadFourCore.directCount bits (8 + p)).toNat * 256 +
      (pOut bits p).toNat * 16 + (pHOut bits p).toNat) % 65536 = _
  have hPLe : (pOut bits p).toNat ≤ 7 := by
    rw [hBlocks.1]
    have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut bits p).toNat ≤ 6 := by
    rw [hBlocks.2.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hZLe : (pZOut bits p).toNat ≤ 4 := by
    rw [hBlocks.2.2]
    have hZCard : (externalTargets G C).card = 4 := by simpa using (Fintype.card_congr L.z).symm
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hDLe : G.outdegree (L.p ⟨p, hp⟩).1 ≤ 19 := by
    rw [← hD]
    have h := toNat_count 19 (coreArc bits (8 + p)) (by omega)
    rw [XFourNoRoot.BroadFourCore.directCount, h]
    calc
      ∑ i ∈ Finset.range 19, (bitCount (coreArc bits (8 + p) i)).toNat ≤
          ∑ _i ∈ Finset.range 19, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases coreArc bits (8 + p) i <;> decide
      _ = 19 := by simp
  have hPGraphLe : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 7 := by
    have hc : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
  have hHGraphLe : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hZGraphLe : Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ 4 := by
    have hc : (externalTargets G C).card = 4 := by simpa using (Fintype.card_congr L.z).symm
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2, hD]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem orderedP_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 6)
    (hOrder : ∀ q : Fin 6,
      BroadFourLabels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.pKey G C (L.p ⟨q.val, by omega⟩).1) :
    orderedP (graphBits G C L) = true := by
  rw [orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pRowKey_toNat G C L hG hPB hHCard (p + 1) (by omega),
    pRowKey_toNat G C L hG hPB hHCard p (by omega)]
  exact hOrder ⟨p, hp⟩

theorem zColumnCode_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (z : Nat) (hz : z < 4) :
    (zColumnCode (graphBits G C L) z).toNat =
      BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
        (L.z ⟨z, hz⟩).1 := by
  rw [zColumnCode, toNat_count_eq_fin_sum 7 _ (by omega),
    BroadFourLabels.zColumnDegree]
  apply Finset.sum_congr rfl
  intro p hp
  rw [XFourNoRoot.BroadFourBridge.pToZ_coreBits G.Adj _ _ _ p z p.isLt hz]
  have hp8 : p.val < 8 := by omega
  simp [hp8]

theorem orderedZ_true (C : G.LocalConfiguration) (L : Labels G C)
    (hOrder : ∀ q : Fin 3,
      BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val, by omega⟩).1) :
    orderedZ (graphBits G C L) = true := by
  rw [orderedZ, all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zColumnCode_toNat G C L (z + 1) (by omega),
    zColumnCode_toNat G C L z (by omega)]
  exact hOrder ⟨z, hz⟩

theorem totalHToP_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hHCard : C.H.card = 6) :
    (totalHToP (graphBits G C L)).toNat = edgeCount G C.H C.P := by
  let bits := graphBits G C L
  rw [totalHToP, toNat_sumCount]
  have hEach : ∀ i : Fin 6, (hPOut bits i).toNat =
      Shared.directCount G C.P (L.a ⟨i + 1, by omega⟩).1 := by
    intro i
    exact hPOut_toNat G C L hHCard i i.isLt
  have hSum : (∑ i ∈ Finset.range 6, (hPOut bits i).toNat) =
      edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hLabelEquiv G C L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ by simpa using hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hPCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem totalPToH_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 6) :
    (totalPToH (graphBits G C L)).toNat = edgeCount G C.P C.H := by
  let bits := graphBits G C L
  rw [totalPToH, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pHOut bits i).toNat =
      Shared.directCount G C.H (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hG hHCard i i.isLt).2.1
  have hSum : (∑ i ∈ Finset.range 7, (pHOut bits i).toNat) =
      edgeCount G C.P C.H := by
    rw [edgeCount_eq_sum_fin G C.P C.H L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  rw [hPCard, hHCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem twentyFive_le_H_to_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 2) (hx : C.x = 4) (hy : BSevenKTwo.y G C = 0)
    (hPB : C.P = C.B) : 25 ≤ edgeCount G C.H C.P := by
  have hCap := BSevenKTwo.H_degree_capacity G C hG hMin hk
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  have hR := BSevenKTwo.x_add_card_R_eq_five G C hG
    hRootDegree hk
  have hQ : C.Q.card = 0 := by
    simp [Digraph.LocalConfiguration.Q, hPB]
  rw [hx] at hHCard hR
  have hRCard : C.R.card = 1 := by omega
  rw [hHCard, hx, hRCard, hQ, hy] at hCap
  norm_num [Nat.choose] at hCap
  omega

theorem H_to_P_add_externalMissing_le_thirtyFive
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (hPCard : C.P.card = 7)
    (hZCard : (externalTargets G C).card = 4) (hHCard : C.H.card = 6) :
    edgeCount G C.H C.P + (28 - edgeCount G C.P (externalTargets G C)) ≤ 35 := by
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternal := edgeCount_externalTargets G C
  rw [← hExternal] at hAccounting
  have hPP := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hPP
  norm_num [Nat.choose] at hPP
  have hPZCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, hZCard] at hPZCap
  have hPHLower : 7 + (28 - edgeCount G C.P (externalTargets G C)) ≤
      edgeCount G C.P C.H := by omega
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  omega

theorem broadCore_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hPB : C.P = C.B) (hk : C.k = 2) (hXCard : C.X.card = 4)
    (hRootDegree : G.outdegree C.s = 8) (hHCard : C.H.card = 6)
    (hPCard : C.P.card = 7) (hZCard : (externalTargets G C).card = 4)
    (hm : 28 - edgeCount G C.P (externalTargets G C) ≤ 10)
    (hPOrder : ∀ q : Fin 6,
      BroadFourLabels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.pKey G C (L.p ⟨q.val, by omega⟩).1)
    (hZOrder : ∀ q : Fin 3,
      BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val, by omega⟩).1) :
    broadCore (graphBits G C L) = true := by
  let bits := graphBits G C L
  have hOrA := orientedA_true G C L hG
  have hOrP := orientedP_true G C L hG
  have hOrPH := orientedPH_true G C L hG
  have hFixed := fixedA_true G C L hG
  have hXReach := everyXReached_true G C L hk
  have hZReach := allZReached_true G C L
  have hThree := three_le_aOneToXCount G C L hG hPivot hk hXCard
  have hThreeBool : (3 : BitVec 8).ule (count 8 fun q =>
      aArc bits (1 + q / 4) (3 + q % 4)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    simpa [bits] using hThree
  have hAMin := aMinimumAndDegree_true G C L hG hPB hPivot hMin hk
  have hANon := aNonSeymour_all_true G C L hG hPB hNoSeymour
  have hPMin := pMinimumDegree_true G C L hG hPB hHCard hMin
  have hPNon := pNonSeymour_all_true G C L hG hPB hNoSeymour
  have hEff := pEffectiveCondition_true G C L hG hPB hMin hNoSeymour
    hRootDegree hHCard hPCard hZCard hm
  have hOP := orderedP_true G C L hG hPB hHCard hPOrder
  have hOZ := orderedZ_true G C L hZOrder
  have hThreeBool' : (3 : BitVec 8).ule (count 8 fun q =>
      aArc (graphBits G C L) (1 + q / 4) (3 + q % 4)) = true := by
    simpa only [bits] using hThreeBool
  simp only [broadCore, Bool.and_eq_true]
  refine ⟨?_, hOZ⟩
  refine ⟨?_, hOP⟩
  refine ⟨?_, hEff⟩
  refine ⟨?_, hPNon⟩
  refine ⟨?_, hPMin⟩
  refine ⟨?_, hANon⟩
  refine ⟨?_, hAMin⟩
  refine ⟨?_, hThreeBool'⟩
  refine ⟨?_, hZReach⟩
  refine ⟨?_, hXReach⟩
  refine ⟨?_, hFixed⟩
  refine ⟨?_, hOrPH⟩
  exact ⟨hOrA, hOrP⟩

end SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge
