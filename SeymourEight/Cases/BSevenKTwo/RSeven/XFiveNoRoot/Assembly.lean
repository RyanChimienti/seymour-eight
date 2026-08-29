import SeymourEight.Cases.BSevenKTwo.RSeven.XFiveNoRoot.GraphFacts
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeAssembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.SharpKing
import SeymourEight.Cases.BSevenKTwo.Counting
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Assembly

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open RSeven.XFourNoRoot IndividualEffective

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (L : Labels G C) : Encoding :=
  coreBits G.Adj (fun i => (L.p i).1) (fun i => (L.a i).1) (fun i => (L.z i).1)

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat = (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem orientedA_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) : orientedA (graphBits G L) = true := by
  rw [orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true, aArc_coreBits G.Adj _ _ _ i i hi hi]
  constructor
  · simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [aArc_coreBits G.Adj _ _ _ i j hi hj,
      aArc_coreBits G.Adj _ _ _ j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    · by_cases h : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
      · simp [h, hG.2 h]
      · simp [h]

theorem orientedP_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) : orientedP (graphBits G L) = true := by
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [pArc_coreBits G.Adj _ _ _ i j hi hj,
    pArc_coreBits G.Adj _ _ _ j i hj hi]
  by_cases hij : i = j
  · simp [hij]
  · by_cases h : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
    · simp [hij, h, hG.2 h]
    · simp [hij, h]

theorem orientedPH_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) : orientedPH (graphBits G L) = true := by
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  simp only [pToH_coreBits G.Adj _ _ _ p h hp hh,
    hToP_coreBits G.Adj _ _ _ h p hh hp]
  by_cases ha : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1
  · simp [ha, hG.2 ha]
  · simp [ha]

theorem fixedA_true (C : G.LocalConfiguration) (L : Labels G C) :
    fixedA (graphBits G L) = true := by
  let bits := graphBits G L
  have h01 : aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj _ _ _ 0 1 (by omega) (by omega)]
    exact decide_eq_true (by
      have ht : (⟨(0 : Fin 2).val + 1, by omega⟩ : Fin 8) = ⟨1, by omega⟩ :=
        Fin.ext (by simp)
      rw [← ht]
      have hzero : (⟨0, by omega⟩ : Fin 8) = 0 := Fin.ext rfl
      rw [hzero, L.a_zero]
      exact (Finset.mem_filter.mp (L.a_aOne 0)).2)
  have h02 : aArc bits 0 2 = true := by
    rw [aArc_coreBits G.Adj _ _ _ 0 2 (by omega) (by omega)]
    exact decide_eq_true (by
      have ht : (⟨(1 : Fin 2).val + 1, by omega⟩ : Fin 8) = ⟨2, by omega⟩ :=
        Fin.ext (by simp)
      rw [← ht]
      have hzero : (⟨0, by omega⟩ : Fin 8) = 0 := Fin.ext rfl
      rw [hzero, L.a_zero]
      exact (Finset.mem_filter.mp (L.a_aOne 1)).2)
  have hTail : all 5 (fun i => !aArc bits 0 (3 + i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [aArc_coreBits G.Adj _ _ _ 0 (3 + i) (by omega) (by omega)]
    have hzero : (⟨0, by omega⟩ : Fin 8) = 0 := Fin.ext rfl
    rw [hzero, L.a_zero]
    have hx := L.a_x ⟨i, hi⟩
    have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
      intro ha
      have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
        Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hA1
          (by simpa [Nat.add_comm] using hx)
    simp [hn]
  change fixedA bits = true
  simp only [fixedA, h01, h02, hTail, Bool.and_self]

theorem everyXReached_true (C : G.LocalConfiguration) (L : Labels G C)
    (hk : C.k = 2) : everyXReached (graphBits G L) = true := by
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
    have huCases : u = (L.a (1 : Fin 8)).1 ∨ u = (L.a (2 : Fin 8)).1 := by
      rw [← hEq] at huA1
      simpa [eq_comm] using huA1
    rcases huCases with h1 | h2
    · refine ⟨0, by omega, ?_⟩
      rw [aArc_coreBits G.Adj _ _ _ 1 (3 + x) (by omega) (by omega)]
      simpa [Nat.add_comm, h1] using hux
    · refine ⟨1, by omega, ?_⟩
      rw [aArc_coreBits G.Adj _ _ _ 2 (3 + x) (by omega) (by omega)]
      simpa [Nat.add_comm, h2] using hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨pi, hpi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨pi, pi.isLt, ?_⟩
    rw [pToH_coreBits G.Adj _ _ _ pi (2 + x) pi.isLt (by omega)]
    simpa [Nat.add_comm, Nat.add_left_comm, congrArg Subtype.val hpi] using hux

theorem allZReached_true (C : G.LocalConfiguration) (L : Labels G C) :
    allZReached (graphBits G L) = true := by
  rw [allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := (L.z ⟨z, hz⟩).2
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt hz]
  simpa [congrArg Subtype.val hi] using hpz

noncomputable def xLabelEquiv (C : G.LocalConfiguration) (L : Labels G C)
    (hXCard : C.X.card = 5) : Fin 5 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 5 → {v : V // v ∈ C.X} := fun i =>
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
    exact Nat.add_right_cancel (congrArg Fin.val ha)
  · simpa using hXCard.symm

noncomputable def aOneLabelEquiv (C : G.LocalConfiguration) (L : Labels G C)
    (hk : C.k = 2) : Fin 2 ≃ {v : V // v ∈ C.A1} := by
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
    exact Nat.add_right_cancel (congrArg Fin.val ha)
  · change C.A1.card = 2 at hk
    simpa using hk.symm

theorem three_le_aOneToXCount (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C) (hk : C.k = 2)
    (hXCard : C.X.card = 5) (hRZero : C.R = ∅) :
    3 ≤ (count 10 fun q => aArc (graphBits G L)
      (1 + q / 5) (3 + q % 5)).toNat := by
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
          CertificateBridge.internalFirstNeighbors] using (hPivot u huA).1
  have hA1a1Zero : edgeCount G C.A1 {C.a1} = 0 := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro u hu
    have hnot : ¬G.Adj u C.a1 := hG.2 (Finset.mem_filter.mp hu).2
    simp [hnot]
  have hHa1 : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hv
    rcases Finset.mem_singleton.mp hv with rfl
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  have hADecomp : edgeCount G C.A1 C.A =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X := by
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
    rw [hRZero]
    simp only [Finset.union_empty]
    rw [edgeCount_union_of_disjoint G C.A1 (C.A1 ∪ C.X) {C.a1} hHa1,
      edgeCount_union_of_disjoint G C.A1 C.A1 C.X
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C), hA1a1Zero]
    simp
  have hThree : 3 ≤ edgeCount G C.A1 C.X := by omega
  have hRow (a : Fin 2) :
      Shared.directCount G C.X (L.a ⟨a.1 + 1, by omega⟩).1 =
        ∑ x : Fin 5, if aArc (graphBits G L)
          (1 + a.1) (3 + x.1) then 1 else 0 := by
    apply directCount_eq_sum_bool G C.X (xLabelEquiv G C L hXCard) _
    intro x
    rw [aArc_coreBits G.Adj _ _ _ (1 + a.1) (3 + x.1) (by omega) (by omega)]
    simp [xLabelEquiv, Nat.add_comm]
  have hCount : (count 10 fun q =>
      aArc (graphBits G L) (1 + q / 5) (3 + q % 5)).toNat =
      edgeCount G C.A1 C.X := by
    rw [toNat_count_eq_fin_sum 10 _ (by omega),
      edgeCount_eq_sum_fin G C.A1 C.X (aOneLabelEquiv G C L hk)]
    simp_rw [show ∀ i : Fin 2,
      (aOneLabelEquiv G C L hk i).1 = (L.a ⟨i.1 + 1, by omega⟩).1 by
        intro i; rfl]
    simp_rw [hRow]
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  rw [hCount]
  exact hThree

theorem A_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = Shared.directCount G C.A u + Shared.directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hCap := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
    G C hG u hu
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.P) u (by
    intro v hv
    simpa [hPB] using hCap hv)
  rw [directCount_union_of_disjoint G C.A C.P u hAP] at hEq
  exact hEq

theorem aMinimumAndDegree_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hk : C.k = 2) :
    aMinimumAndDegree (graphBits G L) = true := by
  rw [aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L a ha
  have hPO := aPOut_toNat G C L a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 2 ≤ (aOut (graphBits G L) a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut (graphBits G L) a).toNat = 2 →
      7 ≤ (aPOut (graphBits G L) a).toNat := by
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
  have hTotal : 8 ≤ (aOut (graphBits G L) a).toNat +
      (aPOut (graphBits G L) a).toNat := by
    rw [hAO, hPO, ← A_outdegree_eq_A_add_P G C hG hPB _ (L.a _).2]
    exact hMin _
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
      exact hAmin
    · rw [Bool.or_eq_true]
      by_cases heq : aOut (graphBits G L) a = 2
      · right
        norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
        exact hTie (congrArg BitVec.toNat heq)
      · left
        simpa using heq
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by
      have hA : (aOut (graphBits G L) a).toNat ≤ 8 := by
        rw [hAO]
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (by simpa using (Fintype.card_congr L.a).symm)
      have hP : (aPOut (graphBits G L) a).toNat ≤ 7 := by
        rw [hPO]
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (by simpa using (Fintype.card_congr L.p).symm)
      omega)]
    exact hTotal

theorem pMinimumDegree_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hRoot : edgeCount G C.P {C.s} = 0) (hHCard : C.H.card = 7)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    pMinimumDegree (graphBits G L) = true := by
  rw [pMinimumDegree, all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C L hG hHCard p hp
  have hCaptured : G.outNeighborFinset (L.p ⟨p, hp⟩).1 ⊆
      C.Z ∪ C.H ∪ C.P := by
    intro v hv
    have hc := outgoingCaptured_of_p_eq_B G C hG hPB _ (L.p _).2 hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hc ⊢
    rcases hc with ((hz | hs) | hh) | hp'
    · exact Or.inl (Or.inl hz)
    · subst v
      exact (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.root_tail_absent
        G C hRoot (L.p _).2
        ((Digraph.mem_outNeighborFinset (G := G)).mp hv)).elim
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hp'
  have hZH : Disjoint C.Z C.H :=
    Digraph.LocalConfiguration.disjoint_Z_H (G := G) C
  have hZHP : Disjoint (C.Z ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hvZH hvP
    rcases Finset.mem_union.mp hvZH with hvZ | hvH
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  have hGraph : G.outdegree (L.p ⟨p, hp⟩).1 =
      Shared.directCount G C.Z (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.P (L.p ⟨p, hp⟩).1 := by
    have h := outdegree_eq_directCount_of_captured G (C.Z ∪ C.H ∪ C.P)
      (L.p ⟨p, hp⟩).1 hCaptured
    rw [directCount_union_of_disjoint G (C.Z ∪ C.H) C.P _ hZHP,
      directCount_union_of_disjoint G C.Z C.H _ hZH] at h
    exact h
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add]
  have hSmall : (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat < 256 := by
    have hP : (pOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hBlocks.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.p).symm)
    have hH : (pHOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    omega
  rw [Nat.mod_eq_of_lt hSmall]
  have hSmall' : (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat +
      (pZOut (graphBits G L) p).toNat < 256 := by
    have hP : (pOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hBlocks.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.p).symm)
    have hH : (pHOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hZ : (pZOut (graphBits G L) p).toNat ≤ 3 := by
      rw [hBlocks.2.2]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.z).symm)
    omega
  rw [Nat.mod_eq_of_lt hSmall']
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  change 8 ≤ _
  have hDegree := hMin (L.p ⟨p, hp⟩).1
  omega

theorem aNonSeymour_all_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRoot : edgeCount G C.P {C.s} = 0) :
    all 8 (aNonSeymour (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  exact nonSeymour_graphBits_true G C L hG hPB hNoSeymour hRoot a (by omega)

theorem pNonSeymour_all_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRoot : edgeCount G C.P {C.s} = 0) :
    all 7 (pNonSeymour (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  exact nonSeymour_graphBits_true G C L hG hPB hNoSeymour hRoot (8 + p)
    (by omega)

theorem totalPToZ_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (totalPToZ (graphBits G L)).toNat = edgeCount G C.P C.Z := by
  rw [totalPToZ, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pZOut (graphBits G L) i).toNat =
      Shared.directCount G C.Z (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hG hHCard i i.isLt).2.2
  have hSum : (∑ i ∈ Finset.range 7, (pZOut (graphBits G L) i).toNat) =
      edgeCount G C.P C.Z := by
    rw [edgeCount_eq_sum_fin G C.P C.Z L.p, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.Z
  rw [show C.P.card = 7 by simpa using (Fintype.card_congr L.p).symm,
    show C.Z.card = 3 by simpa using (Fintype.card_congr L.z).symm] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (externalMissing (graphBits G L)).toNat = 21 - edgeCount G C.P C.Z := by
  rw [externalMissing, BitVec.toNat_sub, totalPToZ_toNat G C L hG hHCard]
  have hCap := edgeCount_le_card_mul_card G C.P C.Z
  rw [show C.P.card = 7 by simpa using (Fintype.card_congr L.p).symm,
    show C.Z.card = 3 by simpa using (Fintype.card_congr L.z).symm] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.P C.Z + 21) % 256) = _
  omega

theorem totalPToH_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (totalPToH (graphBits G L)).toNat = edgeCount G C.P C.H := by
  rw [totalPToH, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pHOut (graphBits G L) i).toNat =
      Shared.directCount G C.H (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hG hHCard i i.isLt).2.1
  have hSum : (∑ i ∈ Finset.range 7, (pHOut (graphBits G L) i).toNat) =
      edgeCount G C.P C.H := by
    rw [edgeCount_eq_sum_fin G C.P C.H L.p, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  rw [show C.P.card = 7 by simpa using (Fintype.card_congr L.p).symm, hHCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem totalHToP_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hHCard : C.H.card = 7) :
    (totalHToP (graphBits G L)).toNat = edgeCount G C.H C.P := by
  rw [totalHToP, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (hPOut (graphBits G L) i).toNat =
      Shared.directCount G C.P (L.a ⟨i + 1, by omega⟩).1 := by
    intro i
    exact hPOut_toNat G C L i i.isLt
  have hSum : (∑ i ∈ Finset.range 7, (hPOut (graphBits G L) i).toNat) =
      edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (GraphFacts.hLabelEquiv G C L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simpa [GraphFacts.hLabelEquiv] using hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  rw [hHCard, show C.P.card = 7 by simpa using (Fintype.card_congr L.p).symm] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem totalPOut_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (totalPOut (graphBits G L)).toNat = edgeCount G C.P C.P := by
  rw [totalPOut, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pOut (graphBits G L) i).toNat =
      Shared.directCount G C.P (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hG hHCard i i.isLt).1
  have hSum : (∑ i ∈ Finset.range 7, (pOut (graphBits G L) i).toNat) =
      edgeCount G C.P C.P := by
    rw [edgeCount_eq_sum_fin G C.P C.P L.p, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hEach i)
  rw [hSum]
  have hCap := internal_edgeCount_le_choose_two G C.P hG
  rw [show C.P.card = 7 by simpa using (Fintype.card_congr L.p).symm] at hCap
  norm_num [Nat.choose] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem pRowKey_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hRoot : edgeCount G C.P {C.s} = 0) (hHCard : C.H.card = 7)
    (p : Nat) (hp : p < 7) :
    (pRowKey (graphBits G L) p).toNat = Labels.pKey G C (L.p ⟨p, hp⟩).1 := by
  have hBlocks := pBlockCounts G C L hG hHCard p hp
  have hD : (Core.directCount (graphBits G L) (8 + p)).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
    have hDirect := directCount_graphBits_toNat G C L hG hPB hRoot (8 + p) (by omega)
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 15 by omega] using hDirect
  have hDegreeNat := congrArg BitVec.toNat
    (pDegree_eq_directCount (graphBits G L) p hp)
  rw [hD] at hDegreeNat
  simp only [BitVec.toNat_add] at hDegreeNat
  have hDegreeNat' : ((pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat + (pZOut (graphBits G L) p).toNat) % 256 =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
    simpa [Nat.add_mod] using hDegreeNat
  unfold pRowKey Labels.pKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  rw [hDegreeNat', hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  congr 1
  simp only [show ((4096 : BitVec 16).toNat) = 4096 by decide,
    show ((256 : BitVec 16).toNat) = 256 by decide,
    show ((16 : BitVec 16).toNat) = 16 by decide]
  omega

theorem orderedP_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hRoot : edgeCount G C.P {C.s} = 0) (hHCard : C.H.card = 7)
    (hOrder : ∀ q : Fin 6,
      Labels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pKey G C (L.p ⟨q.val, by omega⟩).1) :
    orderedP (graphBits G L) = true := by
  rw [orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pRowKey_toNat G C L hG hPB hRoot hHCard (p + 1) (by omega),
    pRowKey_toNat G C L hG hPB hRoot hHCard p (by omega)]
  exact hOrder ⟨p, hp⟩

theorem zColumnCode_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (z : Nat) (hz : z < 3) :
    (zColumnCode (graphBits G L) z).toNat =
      Labels.zKey G (fun i => (L.p i).1) (L.z ⟨z, hz⟩).1 := by
  rw [zColumnCode, toNat_count_eq_fin_sum 7 _ (by omega), Labels.zKey]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pToZ_coreBits G.Adj _ _ _ p z p.isLt hz]
  simp

theorem orderedZ_true (C : G.LocalConfiguration) (L : Labels G C)
    (hOrder : ∀ q : Fin 2,
      Labels.zKey G (fun i => (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
        Labels.zKey G (fun i => (L.p i).1) (L.z ⟨q.val, by omega⟩).1) :
    orderedZ (graphBits G L) = true := by
  rw [orderedZ, all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zColumnCode_toNat G C L (z + 1) (by omega),
    zColumnCode_toNat G C L z (by omega)]
  exact hOrder ⟨z, hz⟩

theorem orderedStructuralClasses_true (C : G.LocalConfiguration) (L : Labels G C)
    (hAOne : Labels.structuralKey G C (L.a 2).1 ≤
      Labels.structuralKey G C (L.a 1).1)
    (hX : ∀ q : Fin 4,
      Labels.structuralKey G C (L.a ⟨q.val + 4, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 3, by omega⟩).1) :
    orderedStructuralClasses (graphBits G L) = true := by
  have hAP (a : Nat) (ha : a < 8) :
      (aPOut (graphBits G L) a).toNat =
        Labels.structuralKey G C (L.a ⟨a, ha⟩).1 :=
    aPOut_toNat G C L a ha
  simp only [orderedStructuralClasses, Bool.and_eq_true,
    BitVec.ule_eq_decide, decide_eq_true_eq]
  constructor
  · simpa [hAP 2 (by omega), hAP 1 (by omega)] using hAOne
  · rw [all_eq_true_iff]
    intro x hx
    simp only [decide_eq_true_eq]
    rw [hAP (4 + x) (by omega), hAP (3 + x) (by omega)]
    simpa [Nat.add_comm] using hX ⟨x, hx⟩

theorem pSecondPCount_le_graphPSecond (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (p : Nat) (hp : p < 7) :
    (pSecondPCount (graphBits G L) p).toNat ≤
      (C.P.filter fun v => v ∈
        G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply XThreeNoRoot.GraphFacts.count_le_filterCard C.P L.p
    (fun q => strictSecondLocal (graphBits G L) (8 + p) (8 + q))
    (fun v => v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1) (by omega)
  intro j hj
  have hmem := strictSecondLocal_true_mem G C L hG (8 + p) (8 + j)
    (by omega) (by omega) hj
  simpa [labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
    show 8 + j.val < 15 by omega] using hmem

theorem directZEffectiveStrict_subset_second (C : G.LocalConfiguration)
    (p : V) (hpP : p ∈ C.P) :
    directZEffectiveUnion G C p \ G.outNeighborFinset p ⊆
      G.secondOutNeighborFinset p :=
  BroadFourBridge.directZEffectiveStrict_subset_second G C p hpP

theorem directZEffective_direct_subset_H (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoRoot : epsilonS G C = 0) (p : V) (hpP : p ∈ C.P) :
    directZEffectiveUnion G C p ∩ G.outNeighborFinset p ⊆
      C.H.filter (G.Adj p) :=
  BroadFourBridge.directZEffective_direct_subset_H G C hG hPB hNoRoot p hpP

theorem PSecond_add_directZEffective_card_le_second_add_H
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoRoot : epsilonS G C = 0) (p : V) (hpP : p ∈ C.P) :
    (C.P.filter fun v => v ∈ G.secondOutNeighborFinset p).card +
        (directZEffectiveUnion G C p).card ≤
      G.secondOutdegree p + Shared.directCount G C.H p :=
  BroadFourBridge.PSecond_add_directZEffective_card_le_second_add_H
    G C hG hPB hNoRoot p hpP

set_option linter.flexible false in
set_option maxHeartbeats 1000000 in
theorem individualEffectiveLower_graph (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hmBound : 21 - edgeCount G C.P C.Z ≤ 5)
    (p : Nat) (hp : p < 7) :
    (individualEffectiveLower (graphBits G L) p).toNat ≤
      (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G L
  let v := (L.p ⟨p, hp⟩).1
  let S := FiveZUnionEightCapacity.directZNeighbors G C v
  let U := directZEffectiveUnion G C v
  let m := 21 - edgeCount G C.P C.Z
  let s := S.card
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : C.Z.card = 3 := by simpa using (Fintype.card_congr L.z).symm
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ 3 :=
    (Finset.card_le_card
      (FiveZUnionEightCapacity.directZNeighbors_subset_Z G C v)).trans_eq hZCard
  have hLower := directZ_effective_capacity_lower G C hMin v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hRow := ZThreeBridge.row_missing_le_total_missing_three
    G C hPCard hZCard v hvP
  have hToP := ZThreeBridge.directZ_to_P_capacity_three
    G C hG hPCard hZCard v hvP
  have hM' : (externalMissing bits).toNat = m :=
    externalMissing_toNat G C L hG hHCard
  have hS : (pZOut bits p).toNat = s := by
    rw [(pBlockCounts G C L hG hHCard p hp).2.2]
    rfl
  have hMBV : externalMissing bits = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hM', BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hSBV : pZOut bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hm : m ≤ 5 := by simpa [m] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (3 - s) at hToP
  change 3 - s ≤ m at hRow
  change (individualEffectiveLower bits p).toNat ≤ U.card
  simp only [individualEffectiveLower]
  rw [hMBV, hSBV]
  by_cases hU : 8 ≤ U.card
  · interval_cases m <;> interval_cases s <;>
      simp [effectiveAtRowSize, Nat.choose] at hInternal hToP hRow hLower ⊢ <;>
      omega
  · have hUle : U.card ≤ 7 := by omega
    have hUSum : U.card + (8 - U.card) = 8 := by omega
    have hUeq : 8 - (8 - U.card) = U.card := by omega
    interval_cases m <;> interval_cases s <;>
      simp [effectiveAtRowSize, Nat.choose] at hInternal hToP hRow hLower hUSum ⊢ <;>
      rw [← hUeq] <;> omega

theorem pEffectiveCondition_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hNoRoot : epsilonS G C = 0) (hHCard : C.H.card = 7)
    (hmBound : 21 - edgeCount G C.P C.Z ≤ 5) :
    all 7 (pEffectiveCondition (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hBlocks := pBlockCounts G C L hG hHCard p hp
  have hTable := individualEffectiveLower_graph G C L hG hMin hHCard
    hmBound p hp
  have hPS := pSecondPCount_le_graphPSecond G C L hG p hp
  have hUnion := PSecond_add_directZEffective_card_le_second_add_H
    G C hG hPB hNoRoot v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun h => hNoSeymour ⟨v, h⟩)
  have hRoot := BroadFourBridge.edgeCount_P_root_zero G C hNoRoot
  have hDegree : G.outdegree v = Shared.directCount G C.Z v +
      Shared.directCount G C.H v + Shared.directCount G C.P v := by
    have hCaptured : G.outNeighborFinset v ⊆ C.Z ∪ C.H ∪ C.P := by
      intro w hw
      have hc := outgoingCaptured_of_p_eq_B G C hG hPB v hvP hw
      simp only [Finset.mem_union, Finset.mem_singleton] at hc ⊢
      rcases hc with ((hwZ | hws) | hwH) | hwP
      · exact Or.inl (Or.inl hwZ)
      · subst w
        exact (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.root_tail_absent
          G C hRoot hvP ((Digraph.mem_outNeighborFinset (G := G)).mp hw)).elim
      · exact Or.inl (Or.inr hwH)
      · exact Or.inr hwP
    have hZH : Disjoint C.Z C.H :=
      Digraph.LocalConfiguration.disjoint_Z_H (G := G) C
    have hZHP : Disjoint (C.Z ∪ C.H) C.P := by
      rw [Finset.disjoint_left]
      intro w hw hwP
      rcases Finset.mem_union.mp hw with hwZ | hwH
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hwH hwP
    have h := outdegree_eq_directCount_of_captured G (C.Z ∪ C.H ∪ C.P)
      v hCaptured
    rw [directCount_union_of_disjoint G (C.Z ∪ C.H) C.P v hZHP,
      directCount_union_of_disjoint G C.Z C.H v hZH] at h
    exact h
  have hNatural : (pSecondPCount (graphBits G L) p).toNat +
      (individualEffectiveLower (graphBits G L) p).toNat + 1 ≤
      (pOut (graphBits G L) p).toNat +
        2 * (pHOut (graphBits G L) p).toNat +
        (pZOut (graphBits G L) p).toNat := by
    dsimp [v] at hPS hUnion hNS hDegree hTable
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    omega
  simp only [pEffectiveCondition, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pSecondPCount (graphBits G L) p).toNat +
      (individualEffectiveLower (graphBits G L) p).toNat + 1) % 256 ≤
    ((pOut (graphBits G L) p).toNat +
      2 * (pHOut (graphBits G L) p).toNat +
      (pZOut (graphBits G L) p).toNat) % 256
  have hRightSmall : (pOut (graphBits G L) p).toNat +
      2 * (pHOut (graphBits G L) p).toNat +
      (pZOut (graphBits G L) p).toNat < 256 := by
    have hpLe : (pOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hBlocks.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.p).symm)
    have hhLe : (pHOut (graphBits G L) p).toNat ≤ 7 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hzLe : (pZOut (graphBits G L) p).toNat ≤ 3 := by
      rw [hBlocks.2.2]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.z).symm)
    omega
  rw [Nat.mod_eq_of_lt hRightSmall,
    Nat.mod_eq_of_lt (hNatural.trans_lt hRightSmall)]
  exact hNatural

theorem deletionReached_good (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (x : Nat) (hx : x < 5) (source : V)
    (hSourceLabel : labelledVertex G L (3 + x) = source)
    (S : Finset V) (hS : S = (G.outNeighborFinset source).erase C.a1)
    (bits : Encoding) (hbits : bits = graphBits G L)
    (target : Fin 18) (htNotS : labelledVertex G L target ∉ S)
    (htNeSource : labelledVertex G L target ≠ source)
    (middle : V) (middleIndex : Nat) (hmIndex : middleIndex < 15)
    (hmLabel : labelledVertex G L middleIndex = middle)
    (_hmS : middle ∈ S) (hmt : G.Adj middle (labelledVertex G L target))
    (hRetMiddle : retainedAfterAOneDeletion bits x middleIndex = true) :
    (decide (target.1 ≠ 3 + x) &&
      !retainedAfterAOneDeletion bits x target.1 &&
      any 15 (fun middle ↦
        retainedAfterAOneDeletion bits x middle &&
          coreArc bits middle target)) = true := by
  have htIndexNe : target.1 ≠ 3 + x := by
    intro heq
    apply htNeSource
    simpa [heq] using hSourceLabel
  have htNotRet : retainedAfterAOneDeletion bits x target = false := by
    apply Bool.eq_false_of_not_eq_true
    intro htRet
    simp only [retainedAfterAOneDeletion, Bool.and_eq_true,
      decide_eq_true_eq] at htRet
    rcases htRet with ⟨htNeZero, htArc⟩
    rw [hbits, coreArc_graphBits G C L hG (3 + x) target
      (by omega) target.isLt] at htArc
    have hGraphArc : G.Adj source (labelledVertex G L target) := by
      rw [← hSourceLabel]
      exact of_decide_eq_true htArc
    have htNeA1 : labelledVertex G L target ≠ C.a1 := by
      intro heq
      have hzero : labelledVertex G L 0 = C.a1 := by
        simpa [labelledVertex] using L.a_zero
      have hFin : target = (0 : Fin 18) := by
        apply (retainedLabelEquiv G C L).injective
        apply Subtype.ext
        simpa [retainedLabelEquiv_val, hzero] using heq
      have htNeZero' : target.val ≠ 0 := by simpa using htNeZero
      exact htNeZero' (Fin.ext_iff.mp hFin)
    apply htNotS
    rw [hS]
    exact Finset.mem_erase.mpr
      ⟨htNeA1, (Digraph.mem_outNeighborFinset (G := G)).mpr hGraphArc⟩
  have hArc : coreArc bits middleIndex target = true := by
    rw [hbits, coreArc_graphBits G C L hG middleIndex target hmIndex
      target.isLt, hmLabel]
    exact decide_eq_true hmt
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    exact ⟨decide_eq_true htIndexNe, by simp [htNotRet]⟩
  · rw [any_eq_true_iff]
    exact ⟨middleIndex, hmIndex, by simp [hRetMiddle, hArc]⟩

theorem deletionTarget_good (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (bits : Encoding) (hbits : bits = graphBits G L)
    (x : Nat) (hx : x < 5) (source : V)
    (hSourceLabel : labelledVertex G L (3 + x) = source)
    (hSourceA : source ∈ C.A)
    (S : Finset V) (hS : S = (G.outNeighborFinset source).erase C.a1)
    (E : Finset V) (hE : E = G.outNeighborFinsetOf S \ (S ∪ {source}))
    (target : Fin 18) (htE : labelledVertex G L target ∈ E) :
    (decide (target.val ≠ 3 + x) &&
      !retainedAfterAOneDeletion bits x target.val &&
      any 15 (fun middle ↦ retainedAfterAOneDeletion bits x middle &&
        coreArc bits middle target.val)) = true := by
  rw [hE] at htE
  rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
  obtain ⟨middle, hmS, hmt⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
  have hmOut : middle ∈ G.outNeighborFinset source :=
    Finset.mem_of_mem_erase (hS ▸ hmS)
  rcases Finset.mem_union.mp
      (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG source hSourceA hmOut) with hmA | hmB
  · obtain ⟨i, hi⟩ := L.a.surjective ⟨middle, hmA⟩
    let mi := i.val
    have hmi : mi < 15 := by omega
    have hmLabel : labelledVertex G L mi = middle := by
      simp [mi, labelledVertex, i.isLt, congrArg Subtype.val hi]
    have hmNeA1 : middle ≠ C.a1 := (Finset.mem_erase.mp (hS ▸ hmS)).1
    have hmNeZero : mi ≠ 0 := by
      intro hz
      apply hmNeA1
      rw [← hmLabel, hz]
      simpa [labelledVertex] using L.a_zero
    have hRet : retainedAfterAOneDeletion bits x mi = true := by
      unfold retainedAfterAOneDeletion
      rw [hbits, coreArc_graphBits G C L hG (3 + x) mi (by omega) (by omega),
        hmLabel]
      have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
      have hadj' : G.Adj (labelledVertex G L (3 + x)) middle := by
        rw [hSourceLabel]
        exact hadj
      simpa [hmNeZero, labelledVertex,
        show 3 + x < 8 by omega] using hadj'
    refine deletionReached_good G C L hG x hx source hSourceLabel S hS bits hbits
      target ?_ ?_ middle mi hmi hmLabel (hS ▸ hmS) hmt hRet
    · intro ht
      exact htOutside (Finset.mem_union_left {source} ht)
    · intro ht
      exact htOutside (Finset.mem_union_right S (Finset.mem_singleton.mpr ht))
  · have hmP : middle ∈ C.P := by simpa [hPB] using hmB
    obtain ⟨i, hi⟩ := L.p.surjective ⟨middle, hmP⟩
    let mi := 8 + i.val
    have hmi : mi < 15 := by omega
    have hmLabel : labelledVertex G L mi = middle := by
      simp [mi, labelledVertex, show ¬8 + i.val < 8 by omega,
        show 8 + i.val < 15 by omega, congrArg Subtype.val hi]
    have hRet : retainedAfterAOneDeletion bits x mi = true := by
      unfold retainedAfterAOneDeletion
      rw [hbits, coreArc_graphBits G C L hG (3 + x) mi (by omega) (by omega),
        hmLabel]
      have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
      have hadj' : G.Adj (labelledVertex G L (3 + x)) middle := by
        rw [hSourceLabel]
        exact hadj
      simpa [mi, labelledVertex, show 3 + x < 8 by omega] using hadj'
    refine deletionReached_good G C L hG x hx source hSourceLabel S hS bits hbits
      target ?_ ?_ middle mi hmi hmLabel (hS ▸ hmS) hmt hRet
    · intro ht
      exact htOutside (Finset.mem_union_left {source} ht)
    · intro ht
      exact htOutside (Finset.mem_union_right S (Finset.mem_singleton.mpr ht))

set_option maxHeartbeats 1000000 in
theorem deletionCount_eq (bits : Encoding) (x : Nat) :
    deletionCount bits x = count 18 (deletionTarget bits x) := rfl

set_option maxHeartbeats 1000000 in
theorem xDeletionExpands_true_aux
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRoot : edgeCount G C.P {C.s} = 0)
    (bits : Encoding) (hbits : bits = graphBits G L)
    (x : Nat) (hx : x < 5)
    (hDegree : G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8)
    (hPivotArc : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1) :
    7 ≤ (count 18 (deletionTarget bits x)).toNat := by
  let source := (L.a ⟨3 + x, by omega⟩).1
  let S := (G.outNeighborFinset source).erase C.a1
  let E := G.outNeighborFinsetOf S \ (S ∪ {source})
  have hExpansion : 7 ≤ E.card := by
    simpa [source, S, E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hPivotArc
  have hSourceA : source ∈ C.A := (L.a ⟨3 + x, by omega⟩).2
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro v hvE
    rcases Finset.mem_sdiff.mp hvE with ⟨hvReach, _⟩
    obtain ⟨middle, hmS, hmv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hmOut : middle ∈ G.outNeighborFinset source := Finset.mem_of_mem_erase hmS
    rcases Finset.mem_union.mp
        (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
          G C hG source hSourceA hmOut) with hmA | hmB
    · exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured_retained
        G C hG hPB middle hmA ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
    · have hmP : middle ∈ C.P := by simpa [hPB] using hmB
      exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_outgoingCaptured_retained
        G C hG hPB hRoot middle hmP
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
  let goodTarget : Nat → Bool := deletionTarget bits x
  have hCount : E.card ≤ (count 18 goodTarget).toNat := by
    have hFilter := XThreeNoRoot.GraphFacts.filterCard_le_count
      (V := V) (retainedVertexSet G C) (retainedLabelEquiv G C L)
      goodTarget
      (fun v ↦ v ∈ E) (by omega) (by
        intro target htE
        dsimp only [goodTarget, deletionTarget]
        rw [retainedLabelEquiv_val] at htE
        exact deletionTarget_good G C L hG hPB bits hbits x hx source
          (by simp [source, labelledVertex, show 3 + x < 8 by omega]) hSourceA
          S rfl E rfl target htE)
    have hFilterEq : ((retainedVertexSet G C).filter fun v ↦ v ∈ E).card =
        E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv ↦ hv.2, fun hv ↦ ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    exact hFilter
  change 7 ≤ (count 18 goodTarget).toNat
  exact hExpansion.trans hCount

set_option maxHeartbeats 1000000 in
theorem xDeletionExpands_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRoot : edgeCount G C.P {C.s} = 0)
    (bits : Encoding) (hbits : bits = graphBits G L)
    (x : Nat) (hx : x < 5)
    (hDegree : G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8)
    (hPivotArc : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1) :
    xDeletionExpands bits x = true := by
  unfold xDeletionExpands
  simp only [atLeastSeven, decide_eq_true_eq]
  rw [deletionCount_eq]
  exact xDeletionExpands_true_aux G hBound C L hG hPB hNoSeymour hRoot
    bits hbits x hx hDegree hPivotArc

theorem xEligible_graph_facts (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B) (x : Nat) (hx : x < 5)
    (hEligible : xEligible (graphBits G L) x = true) :
    G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8 ∧
      G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1 := by
  simp only [xEligible, Bool.and_eq_true, beq_iff_eq] at hEligible
  rcases hEligible with ⟨hDegreeBits, hArcBits⟩
  have hDegreeNat := congrArg BitVec.toNat hDegreeBits
  rw [BitVec.toNat_add,
    aOut_toNat G C L (3 + x) (by omega),
    aPOut_toNat G C L (3 + x) (by omega)] at hDegreeNat
  have hALe : Shared.directCount G C.A (L.a ⟨3 + x, by omega⟩).1 ≤ 8 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by
      simpa using (Fintype.card_congr L.a).symm.le)
  have hPLe : Shared.directCount G C.P (L.a ⟨3 + x, by omega⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by
      simpa using (Fintype.card_congr L.p).symm.le)
  have hDegree := A_outdegree_eq_A_add_P G C hG hPB
    (L.a ⟨3 + x, by omega⟩).1 (L.a _).2
  have hArc : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1 := by
    rw [aArc_coreBits G.Adj _ _ _ (3 + x) 0 (by omega) (by omega)] at hArcBits
    simpa [L.a_zero] using of_decide_eq_true hArcBits
  change (Shared.directCount G C.A (L.a ⟨3 + x, by omega⟩).1 +
      Shared.directCount G C.P (L.a ⟨3 + x, by omega⟩).1) % 256 = 8
    at hDegreeNat
  rw [Nat.mod_eq_of_lt (by omega)] at hDegreeNat
  constructor
  · omega
  · exact hArc

theorem xExactDegree_graph_iff (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B) (x : Nat) (hx : x < 5) :
    xExactDegree (graphBits G L) x = true ↔
      G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8 := by
  have hA := aOut_toNat G C L (3 + x) (by omega)
  have hP := aPOut_toNat G C L (3 + x) (by omega)
  have hDegree := A_outdegree_eq_A_add_P G C hG hPB
    (L.a ⟨3 + x, by omega⟩).1 (L.a _).2
  have hALe : Shared.directCount G C.A (L.a ⟨3 + x, by omega⟩).1 ≤ 8 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.a).symm)
  have hPLe : Shared.directCount G C.P (L.a ⟨3 + x, by omega⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.p).symm)
  simp only [xExactDegree, beq_iff_eq]
  constructor
  · intro hBits
    have hNat := congrArg BitVec.toNat hBits
    rw [BitVec.toNat_add, hA, hP] at hNat
    change (Shared.directCount G C.A (L.a ⟨3 + x, by omega⟩).1 +
      Shared.directCount G C.P (L.a ⟨3 + x, by omega⟩).1) % 256 = 8 at hNat
    rw [Nat.mod_eq_of_lt (by omega)] at hNat
    omega
  · intro hDeg
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hA, hP]
    change (Shared.directCount G C.A (L.a ⟨3 + x, by omega⟩).1 +
      Shared.directCount G C.P (L.a ⟨3 + x, by omega⟩).1) % 256 = 8
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem exactDegreeCount_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hXCard : C.X.card = 5) :
    (exactDegreeCount (graphBits G L)).toNat =
      (C.X.filter fun v ↦ G.outdegree v = 8).card := by
  let e := xLabelEquiv G C L hXCard
  have hLabel (x : Fin 5) : (e x).1 = (L.a ⟨3 + x.val, by omega⟩).1 := by
    simp [e, xLabelEquiv, Nat.add_comm]
  apply Nat.le_antisymm
  · unfold exactDegreeCount
    apply XThreeNoRoot.GraphFacts.count_le_filterCard
      C.X e (xExactDegree (graphBits G L))
        (fun v ↦ G.outdegree v = 8) (by omega)
    intro x hExact
    rw [hLabel]
    exact (xExactDegree_graph_iff G C L hG hPB x x.isLt).mp hExact
  · unfold exactDegreeCount
    apply XThreeNoRoot.GraphFacts.filterCard_le_count
      C.X e (xExactDegree (graphBits G L))
        (fun v ↦ G.outdegree v = 8) (by omega)
    intro x hExact
    rw [hLabel] at hExact
    exact (xExactDegree_graph_iff G C L hG hPB x x.isLt).mpr hExact

theorem exactDegreeTail_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hXCard : C.X.card = 5) (hx : C.x = 5) (hRZero : C.R = ∅)
    (hHP : 30 ≤ edgeCount G C.H C.P) :
    (5 : BitVec 8).ule
      (hDefect (graphBits G L) + exactDegreeCount (graphBits G L)) = true := by
  have hBad := Shared.card_degree_ne_of_lower_le_excess_sum
    C.X (G.outdegree) 8 (fun v hv ↦ hMin v)
  have hXSubH : C.X ⊆ C.H := by
    intro v hv
    exact Finset.mem_union_right C.A1 hv
  have hExcessMono : (∑ v ∈ C.X, (G.outdegree v - 8)) ≤
      ∑ v ∈ C.H, (G.outdegree v - 8) :=
    Finset.sum_le_sum_of_subset hXSubH
  have hDegreeSplit := Shared.degreeSum_H_eq_A_add_P G C hG hPB
  have hATo := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  rw [hHCard, hx, hRZero] at hATo
  norm_num [Nat.choose] at hATo
  have hExcessEq : (∑ v ∈ C.H, (G.outdegree v - 8)) + 56 =
      ∑ v ∈ C.H, G.outdegree v := by
    calc
      _ = (∑ v ∈ C.H, (G.outdegree v - 8)) + ∑ _v ∈ C.H, 8 := by
        simp [hHCard]
      _ = ∑ v ∈ C.H, ((G.outdegree v - 8) + 8) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ v ∈ C.H, G.outdegree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact Nat.sub_add_cancel (hMin v)
  have hBadLe : (C.X.filter fun v ↦ G.outdegree v ≠ 8).card ≤
      edgeCount G C.H C.P - 30 := by
    omega
  have hPartition := C.X.card_filter_add_card_filter_not
    (fun v ↦ G.outdegree v = 8)
  have hFive : 5 ≤ edgeCount G C.H C.P - 30 +
      (C.X.filter fun v ↦ G.outdegree v = 8).card := by
    rw [hXCard] at hPartition
    change (C.X.filter fun v ↦ G.outdegree v = 8).card +
      (C.X.filter fun v ↦ G.outdegree v ≠ 8).card = 5 at hPartition
    omega
  have hHPNat := totalHToP_toNat G C L hHCard
  have hExactNat := exactDegreeCount_toNat G C L hG hPB hXCard
  have hHPLe : edgeCount G C.H C.P ≤ 49 := by
    exact (edgeCount_le_card_mul_card G C.H C.P).trans_eq (by
      rw [hHCard]
      have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
      rw [hPCard])
  have hDefectNat : (hDefect (graphBits G L)).toNat =
      edgeCount G C.H C.P - 30 := by
    simp only [hDefect, BitVec.toNat_sub]
    rw [hHPNat]
    change (256 - 30 + edgeCount G C.H C.P) % 256 =
      edgeCount G C.H C.P - 30
    omega
  have hExactLe : (exactDegreeCount (graphBits G L)).toNat ≤ 5 := by
    rw [hExactNat]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hXCard
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  change 5 ≤ ((hDefect (graphBits G L)).toNat +
    (exactDegreeCount (graphBits G L)).toNat) % 256
  rw [hDefectNat, hExactNat, Nat.mod_eq_of_lt (by omega)]
  exact hFive

theorem dualTail_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0) (hHCard : C.H.card = 7)
    (hXCard : C.X.card = 5) (hx : C.x = 5) (hRZero : C.R = ∅)
    (hHP : 30 ≤ edgeCount G C.H C.P) :
    dualTail (graphBits G L) = true := by
  rw [dualTail, Bool.and_eq_true]
  refine ⟨exactDegreeTail_true G C L hG hPB hMin hHCard hXCard hx hRZero hHP, ?_⟩
  rw [all_eq_true_iff]
  intro x hxNat
  by_cases hEligible : xEligible (graphBits G L) x = true
  · have hFacts := xEligible_graph_facts G C L hG hPB x hxNat hEligible
    simp [hEligible, xDeletionExpands_true G hBound C L hG hPB hNoSeymour
      hRoot (graphBits G L) rfl x hxNat hFacts.1 hFacts.2]
  · have hFalse := Bool.eq_false_of_not_eq_true hEligible
    simp [hFalse]

/-- The scalar capacity calculation used by `baseCore_true`, exposed so the
final certificate dispatcher can split on the exact external defect. -/
theorem externalMissing_le_five
    (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hk : C.k = 2) (hx : C.x = 5)
    (hy : BSevenKTwo.y G C = 0) (hNoRoot : epsilonS G C = 0)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 7)
    (hRZero : C.R = ∅) (hZCard : C.Z.card = 3) :
    (externalMissing (graphBits G L)).toNat ≤ 5 := by
  have hRoot := BroadFourBridge.edgeCount_P_root_zero G C hNoRoot
  have hQZero : C.Q = ∅ := by simp [Digraph.LocalConfiguration.Q, hPB]
  have hHCapacity := BSevenKTwo.H_degree_capacity G C hG hMin hk
  rw [hHCard, hx, hRZero, hQZero, hy] at hHCapacity
  norm_num [Nat.choose] at hHCapacity
  have hHP : 30 ≤ edgeCount G C.H C.P := by omega
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPP := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hPP
  norm_num [Nat.choose] at hPP
  have hPZLe := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hPZLe
  have hRootSum : (∑ p ∈ C.P, epsilonAt G p C.s) = 0 := by
    rw [← edgeCount_singleton G C.P C.s]
    exact hRoot
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  rw [hRootSum] at hAccounting
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hm : 21 - edgeCount G C.P C.Z ≤ 5 := by omega
  rw [externalMissing_toNat G C L hG hHCard]
  exact hm

theorem baseCore_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hx : C.x = 5)
    (hy : BSevenKTwo.y G C = 0) (hNoRoot : epsilonS G C = 0)
    (hPCard : C.P.card = 7) (hXCard : C.X.card = 5)
    (hHCard : C.H.card = 7) (hRZero : C.R = ∅) (hZCard : C.Z.card = 3)
    (hPOrder : ∀ q : Fin 6,
      Labels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pKey G C (L.p ⟨q.val, by omega⟩).1)
    (hZOrder : ∀ q : Fin 2,
      Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
        Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val, by omega⟩).1)
    (hAOneOrder : Labels.structuralKey G C (L.a 2).1 ≤
      Labels.structuralKey G C (L.a 1).1)
    (hXOrder : ∀ q : Fin 4,
      Labels.structuralKey G C (L.a ⟨q.val + 4, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 3, by omega⟩).1) :
    baseCore (graphBits G L) = true := by
  have hRoot := BroadFourBridge.edgeCount_P_root_zero G C hNoRoot
  have hQZero : C.Q = ∅ := by simp [Digraph.LocalConfiguration.Q, hPB]
  have hHCapacity := BSevenKTwo.H_degree_capacity G C hG hMin hk
  rw [hHCard, hx, hRZero, hQZero, hy] at hHCapacity
  norm_num [Nat.choose] at hHCapacity
  have hHP : 30 ≤ edgeCount G C.H C.P := by omega
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPP := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hPP
  norm_num [Nat.choose] at hPP
  have hPZLe := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hPZLe
  have hRootSum : (∑ p ∈ C.P, epsilonAt G p C.s) = 0 := by
    rw [← edgeCount_singleton G C.P C.s]
    exact hRoot
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  rw [hRootSum] at hAccounting
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  let m := 21 - edgeCount G C.P C.Z
  let d := 40 - edgeCount G C.P C.H - edgeCount G C.P C.P
  let theta := edgeCount G C.H C.P - 30
  have hm : m ≤ 5 := by
    dsimp [m]
    omega
  have hPHLe : edgeCount G C.P C.H ≤ 19 := by omega
  have hPHPPLe : edgeCount G C.P C.H + edgeCount G C.P C.P ≤ 40 := by omega
  have hThetaD : theta ≤ d := by
    dsimp [theta, d]
    omega
  have hMD : m + d ≤ 5 := by
    dsimp [m, d]
    omega
  have hHPNat := totalHToP_toNat G C L hHCard
  have hPZNat := externalMissing_toNat G C L hG hHCard
  have hPHNat := totalPToH_toNat G C L hG hHCard
  have hPPNat := totalPOut_toNat G C L hG hHCard
  have hDefectNat : (hDefect (graphBits G L)).toNat = theta := by
    simp only [hDefect, BitVec.toNat_sub]
    rw [hHPNat]
    change (256 - 30 + edgeCount G C.H C.P) % 256 = theta
    dsimp [theta]
    omega
  have hCombinedNat : (combinedDefect (graphBits G L)).toNat = d := by
    simp only [combinedDefect, BitVec.toNat_sub]
    rw [hPHNat, hPPNat]
    have hForty : (40 : BitVec 8).toNat = 40 := by decide
    rw [hForty]
    change (256 - edgeCount G C.P C.P +
      ((256 - edgeCount G C.P C.H + 40) % 256)) % 256 = d
    dsimp [d]
    omega
  have hThree : (3 : BitVec 8).ule (count 10 fun q ↦
      aArc (graphBits G L) (1 + q / 5) (3 + q % 5)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact three_le_aOneToXCount G C L hG hPivot hk hXCard hRZero
  have hOrA := orientedA_true G C L hG
  have hOrP := orientedP_true G C L hG
  have hOrPH := orientedPH_true G C L hG
  have hFixed := fixedA_true G C L
  have hReachedX := everyXReached_true G C L hk
  have hReachedZ := allZReached_true G C L
  have hAMin := aMinimumAndDegree_true G C L hG hPB hPivot hMin hk
  have hANon := aNonSeymour_all_true G C L hG hPB hNoSeymour hRoot
  have hPMin := pMinimumDegree_true G C L hG hPB hRoot hHCard hMin
  have hPNon := pNonSeymour_all_true G C L hG hPB hNoSeymour hRoot
  have hEffective := pEffectiveCondition_true G C L hG hPB hMin hNoSeymour
    hNoRoot hHCard hm
  have hDual := dualTail_true G hBound C L hG hPB hMin hNoSeymour hRoot
    hHCard hXCard hx hRZero hHP
  have hSharp := sharpKing_of_orientedP (graphBits G L) hOrP
  have hOrdP := orderedP_true G C L hG hPB hRoot hHCard hPOrder
  have hOrdZ := orderedZ_true G C L hZOrder
  have hOrdS := orderedStructuralClasses_true G C L hAOneOrder hXOrder
  have hHPBool : (30 : BitVec 8).ule (totalHToP (graphBits G L)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHPNat]
    exact hHP
  have hCapacityBool :
      (totalHToP (graphBits G L) + externalMissing (graphBits G L)).ule 35 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [hHPNat, hPZNat]
    change (edgeCount G C.H C.P + m) % 256 ≤ 35
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hThetaBool : (hDefect (graphBits G L)).ule
      (combinedDefect (graphBits G L)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDefectNat, hCombinedNat]
    exact hThetaD
  have hMDBool : (externalMissing (graphBits G L) +
      combinedDefect (graphBits G L)).ule 5 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [hPZNat, hCombinedNat]
    change (m + d) % 256 ≤ 5
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hMD
  simp only [baseCore, hOrA, hOrP, hOrPH, hFixed, hReachedX, hReachedZ,
    hAMin, hANon, hPMin, hPNon, hEffective, hDual, hSharp, hOrdP,
    hOrdZ, hOrdS, hThetaBool, Bool.true_and]
  simp only [Bool.and_eq_true, and_true]
  exact ⟨⟨⟨hThree, hHPBool⟩, hCapacityBool⟩, hMDBool⟩

end Assembly

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot
