import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoRoot.GraphFacts
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeAssembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.SharpKing
import SeymourEight.Cases.BSevenKTwo.Counting
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly

open Shared Shared.FiniteCore Labels GraphFacts
open XTwoNoRoot.Encoding XTwoNoRoot.Core
open RSeven.XFourNoRoot
open RSeven.XFourNoRoot.IndividualEffective

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits {zCount : Nat} (L : Labels G zCount C) : Encoding :=
  coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem orientedA_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    orientedA (graphBits G L) = true := by
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

theorem orientedP_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    orientedP (graphBits G L) = true := by
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

theorem orientedPH_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    orientedPH (graphBits G L) = true := by
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  simp only [pToH_coreBits G.Adj _ _ _ p h hp hh,
    hToP_coreBits G.Adj _ _ _ h p hh hp]
  by_cases ha : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1
  · simp [ha, hG.2 ha]
  · simp [ha]

theorem fixedA_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (_hG : G.IsOriented) :
    fixedA (graphBits G L) = true := by
  let bits := graphBits G L
  have h01 : aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj _ _ _ 0 1 (by omega) (by omega)]
    exact decide_eq_true (by
      have ht : (⟨(0 : Fin 2).val + 1, by omega⟩ : Fin 8) =
          ⟨1, by omega⟩ := Fin.ext (by simp)
      rw [← ht]
      simpa only [show (L.a ⟨0, by omega⟩).1 = C.a1 by simpa using L.a_zero]
        using (Finset.mem_filter.mp (L.a_aOne 0)).2)
  have h02 : aArc bits 0 2 = true := by
    rw [aArc_coreBits G.Adj _ _ _ 0 2 (by omega) (by omega)]
    exact decide_eq_true (by
      have ht : (⟨(1 : Fin 2).val + 1, by omega⟩ : Fin 8) =
          ⟨2, by omega⟩ := Fin.ext (by simp)
      rw [← ht]
      simpa only [show (L.a ⟨0, by omega⟩).1 = C.a1 by simpa using L.a_zero]
        using (Finset.mem_filter.mp (L.a_aOne 1)).2)
  have hTail : all 5 (fun i ↦ !aArc bits 0 (3 + i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [aArc_coreBits G.Adj _ _ _ 0 (3 + i) (by omega) (by omega)]
    simp only [show (L.a ⟨0, by omega⟩).1 = C.a1 by simpa using L.a_zero]
    by_cases hi2 : i < 2
    · have hx := L.a_x ⟨i, hi2⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hA1
            (by simpa [Nat.add_comm] using hx)
      simp [hn]
    · have hr := L.a_r ⟨i - 2, by omega⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        have heq : (⟨i - 2 + 5, by omega⟩ : Fin 8) = ⟨3 + i, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [heq] at hr
        exact (Finset.mem_sdiff.mp hr).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
      simp [hn]
  have hA1R : all 6 (fun q ↦
      let a := q / 3
      let r := q % 3
      !aArc bits (1 + a) (5 + r)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    dsimp
    rw [aArc_coreBits G.Adj _ _ _ (1 + q / 3) (5 + q % 3)
      (by omega) (by omega)]
    have hn := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
      G C (L.a ⟨1 + q / 3, by omega⟩).1 (L.a ⟨5 + q % 3, by omega⟩).1
      (by
        have heq : (⟨(q / 3 : Nat) + 1, by omega⟩ : Fin 8) =
            ⟨1 + q / 3, by omega⟩ := Fin.ext (by simp; omega)
        rw [← heq]
        exact L.a_aOne ⟨q / 3, by omega⟩)
      (by
        have heq : (⟨(q % 3 : Nat) + 5, by omega⟩ : Fin 8) =
            ⟨5 + q % 3, by omega⟩ := Fin.ext (by simp; omega)
        rw [← heq]
        exact L.a_r ⟨q % 3, by omega⟩)
    exact by simpa using decide_eq_false hn
  simp only [fixedA, Bool.and_eq_true]
  exact ⟨⟨⟨h01, h02⟩, hTail⟩, hA1R⟩

theorem everyXReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hk : C.k = 2) :
    everyXReached (graphBits G L) = true := by
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

theorem allZReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 6) :
    allZReached zCount (graphBits G L) = true := by
  rw [allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := (L.z ⟨z, hz⟩).2
  rcases Finset.mem_union.mp hzMem with hzMem | hRootMem
  · rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
    obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt (by omega) hz]
    simpa [congrArg Subtype.val hi] using hpz
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hReach' := hReach
      obtain ⟨p, hp, hps⟩ := hReach
      have hLabel : (L.z ⟨z, hz⟩).1 = C.s := by
        simpa [rootSecondFinset, hReach'] using hRootMem
      obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt (by omega) hz]
      simpa [hLabel, congrArg Subtype.val hi] using hps
    · simp [rootSecondFinset, hReach] at hRootMem

theorem inactiveZZero_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 6) :
    inactiveZZero zCount (graphBits G L) = true := by
  by_cases hz : zCount = 6
  · simp [inactiveZZero, hz]
  rw [inactiveZZero, if_neg hz, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro j hj
  rw [pToZ_coreBits_inactive G.Adj _ _ _ p (zCount + j) hp
    (by omega) (by omega)]
  decide

noncomputable def xLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 2) :
    Fin 2 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 2 → {v : V // v ∈ C.X} := fun i ↦
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

noncomputable def aOneLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hk : C.k = 2) :
    Fin 2 ≃ {v : V // v ∈ C.A1} := by
  let f : Fin 2 → {v : V // v ∈ C.A1} := fun i ↦
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

theorem three_le_aOneToXCount {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hXCard : C.X.card = 2) :
    3 ≤ (count 4 fun q ↦
      let a := q / 2
      let x := q % 2
      aArc (graphBits G L) (1 + a) (3 + x)).toNat := by
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
  have hA1RZero : edgeCount G C.A1 C.R = 0 := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr
    exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
      G C u r hu hr
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
        ∑ x : Fin 2, if aArc (graphBits G L)
          (1 + a.1) (3 + x.1) then 1 else 0 := by
    apply directCount_eq_sum_bool G C.X (xLabelEquiv G C L hXCard) _
    intro x
    rw [aArc_coreBits G.Adj _ _ _ (1 + a.1) (3 + x.1)
      (by omega) (by omega)]
    simp [xLabelEquiv, Nat.add_comm]
  have hCount : (count 4 fun q ↦
      aArc (graphBits G L) (1 + q / 2) (3 + q % 2)).toNat =
      edgeCount G C.A1 C.X := by
    rw [toNat_count_eq_fin_sum 4 _ (by omega),
      edgeCount_eq_sum_fin G C.A1 C.X (aOneLabelEquiv G C L hk)]
    simp_rw [show ∀ i : Fin 2,
      (aOneLabelEquiv G C L hk i).1 = (L.a ⟨i.1 + 1, by omega⟩).1 by
        intro i; rfl]
    simp_rw [hRow]
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  change 3 ≤ (count 4 fun q ↦
    aArc (graphBits G L) (1 + q / 2) (3 + q % 2)).toNat
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

theorem aMinimumAndDegree_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 2) : aMinimumAndDegree (graphBits G L) = true := by
  let bits := graphBits G L
  rw [aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L a ha
  have hPO := aPOut_toNat G C L a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 2 ≤ (aOut bits a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut bits a).toNat = 2 → 7 ≤ (aPOut bits a).toNat := by
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
    rw [hAO, hPO, ← A_outdegree_eq_A_add_P G C hG hPB _ (L.a _).2]
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

theorem pMinimumDegree_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 4)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hzLe : zCount ≤ 6) :
    pMinimumDegree zCount (graphBits G L) = true := by
  let bits := graphBits G L
  rw [pMinimumDegree, all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C L hG hHCard hzLe p hp
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
    · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
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
      · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
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
      (pZOut zCount bits p).toNat < 256 := by
    have hP : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hH : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hZ : Shared.directCount G (externalTargets G C)
        (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    have hcP : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hcZ : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
    omega
  rw [Nat.mod_eq_of_lt hSmall', hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  change 8 ≤ _
  have hDegree := hMin (L.p ⟨p, hp⟩).1
  omega

theorem aNonSeymour_all_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hzLe : zCount ≤ 6) :
    all 8 (aNonSeymour zCount (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  exact nonSeymour_graphBits_true G C L hG hPB hNoSeymour hzLe a
    (by omega)

theorem pNonSeymour_all_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hzLe : zCount ≤ 6) :
    all 7 (pNonSeymour zCount (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  exact nonSeymour_graphBits_true G C L hG hPB hNoSeymour hzLe
    (8 + p) (by omega)

theorem totalPToZ_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hzLe : zCount ≤ 6) :
    (totalPToZ zCount (graphBits G L)).toNat = edgeCount G C.P (externalTargets G C) := by
  let bits := graphBits G L
  rw [totalPToZ, toNat_sumCount]
  have hEach : ∀ i : Fin 7, (pZOut zCount bits i).toNat =
      Shared.directCount G (externalTargets G C) (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hG hHCard hzLe i i.isLt).2.2
  have hSum : (∑ i ∈ Finset.range 7, (pZOut zCount bits i).toNat) =
      edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_eq_sum_fin G C.P (externalTargets G C) L.p, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hz : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
  rw [hp, hz] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hzLe : zCount ≤ 6) :
    (externalMissing zCount (graphBits G L)).toNat =
      7 * zCount - edgeCount G C.P (externalTargets G C) := by
  rw [externalMissing, BitVec.toNat_sub,
    totalPToZ_toNat G C L hG hHCard hzLe]
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hz : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
  rw [hp, hz] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.P (externalTargets G C) + 7 * zCount) % 256) = _
  omega

theorem totalHToP_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 4) :
    (totalHToP (graphBits G L)).toNat = edgeCount G C.H C.P := by
  let bits := graphBits G L
  rw [totalHToP, toNat_sumCount]
  have hEach : ∀ i : Fin 4, (hPOut bits i).toNat =
      Shared.directCount G C.P (L.a ⟨i + 1, by omega⟩).1 := by
    intro i
    exact hPOut_toNat G C L i i.isLt
  have hSum : (∑ i ∈ Finset.range 4, (hPOut bits i).toNat) =
      edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hLabelEquiv G C L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ by simpa using hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hp] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem pRowKey_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 4)
    (hzLe : zCount ≤ 6) (p : Nat) (hp : p < 7) :
    (pRowKey zCount (graphBits G L) p).toNat =
      Labels.pKey G C (L.p ⟨p, hp⟩).1 := by
  let bits := graphBits G L
  have hBlocks := pBlockCounts G C L hG hHCard hzLe p hp
  have hDirect := directCount_graphBits_toNat G C L hG hPB hzLe
    (8 + p) (by omega)
  have hD : (XTwoNoRoot.Core.directCount zCount bits (8 + p)).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 15 by omega] using hDirect
  unfold pRowKey Labels.pKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((XTwoNoRoot.Core.directCount zCount bits (8 + p)).toNat * 4096 +
      (pZOut zCount bits p).toNat * 256 + (pHOut bits p).toNat * 16 +
      (pOut bits p).toNat) % 65536 = _
  have hPLe : (pOut bits p).toNat ≤ 7 := by
    rw [hBlocks.1]
    have hc : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
  have hHLe : (pHOut bits p).toNat ≤ 4 := by
    rw [hBlocks.2.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hZLe : (pZOut zCount bits p).toNat ≤ zCount := by
    rw [hBlocks.2.2]
    have hc : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
  have hDLe : G.outdegree (L.p ⟨p, hp⟩).1 ≤ 21 := by
    rw [← hD, XTwoNoRoot.Core.directCount, toNat_count_eq_fin_sum _ _ (by omega)]
    calc
      ∑ i : Fin (15 + zCount), (if coreArc zCount bits (8 + p) i then 1 else 0) ≤
          ∑ _i : Fin (15 + zCount), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> omega
      _ = 15 + zCount := by simp
      _ ≤ 21 := by omega
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2, hD]
  (congr 1; omega)

theorem orderedP_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hHCard : C.H.card = 4)
    (hzLe : zCount ≤ 6)
    (hOrder : ∀ q : Fin 6,
      Labels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pKey G C (L.p ⟨q.val, by omega⟩).1) :
    orderedP zCount (graphBits G L) = true := by
  rw [orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pRowKey_toNat G C L hG hPB hHCard hzLe (p + 1) (by omega),
    pRowKey_toNat G C L hG hPB hHCard hzLe p (by omega)]
  exact hOrder ⟨p, hp⟩

theorem zColumnCode_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 6)
    (z : Nat) (hz : z < zCount) :
    (zColumnCode (graphBits G L) z).toNat =
      Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨z, hz⟩).1 := by
  rw [zColumnCode, toNat_count_eq_fin_sum 7 _ (by omega), Labels.zKey]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pToZ_coreBits G.Adj _ _ _ p z p.isLt (by omega) hz]
  simp

theorem orderedZ_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 6)
    (hOrder : ∀ q : Fin (zCount - 1),
      Labels.zKey G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val + 1, by omega⟩).1 ≤
        Labels.zKey G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val, by omega⟩).1) :
    orderedZ zCount (graphBits G L) = true := by
  rw [orderedZ, all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zColumnCode_toNat G C L hzLe (z + 1) (by omega),
    zColumnCode_toNat G C L hzLe z (by omega)]
  exact hOrder ⟨z, hz⟩

theorem orderedStructuralClasses_true {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hAOne : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hX : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨4 + q.val, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨3 + q.val, by omega⟩).1)
    (hR : ∀ q : Fin 2,
      Labels.structuralKey G C (L.a ⟨q.val + 6, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 5, by omega⟩).1) :
    orderedStructuralClasses (graphBits G L) = true := by
  have hAP (a : Nat) (ha : a < 8) :
      (aPOut (graphBits G L) a).toNat =
        Labels.structuralKey G C (L.a ⟨a, ha⟩).1 := by
    exact aPOut_toNat G C L a ha
  simp only [orderedStructuralClasses, Bool.and_eq_true,
    BitVec.ule_eq_decide, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hAP 2 (by omega), hAP 1 (by omega)]
    exact hAOne 0
  · rw [hAP 4 (by omega), hAP 3 (by omega)]
    exact hX 0
  · rw [all_eq_true_iff]
    intro r hr
    simp only [decide_eq_true_eq]
    rw [hAP (6 + r) (by omega), hAP (5 + r) (by omega)]
    simpa [Nat.add_comm] using hR ⟨r, hr⟩

theorem directZEffectiveStrict_subset_second (C : G.LocalConfiguration)
    (p : V) (hpP : p ∈ C.P) :
    directZEffectiveUnion G C p \ G.outNeighborFinset p ⊆
      G.secondOutNeighborFinset p :=
  RSeven.XFourNoRoot.BroadFourBridge.directZEffectiveStrict_subset_second
    G C p hpP

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
      G.secondOutdegree p + Shared.directCount G C.H p :=
  by
    let U := directZEffectiveUnion G C p
    let N := G.outNeighborFinset p
    let PS := C.P.filter fun v => v ∈ G.secondOutNeighborFinset p
    let Strict := U \ N
    let Direct := U ∩ N
    have hStrict : Strict ⊆ G.secondOutNeighborFinset p := by
      simpa [Strict, U, N] using directZEffectiveStrict_subset_second G C p hpP
    have hPS : PS ⊆ G.secondOutNeighborFinset p :=
      fun _ hv => (Finset.mem_filter.mp hv).2
    have hDisjoint : Disjoint PS Strict := by
      rw [Finset.disjoint_left]
      intro v hvPS hvStrict
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvStrict).1).2
        (Finset.mem_union_left _ (Finset.mem_filter.mp hvPS).1)
    have hSecondCard : PS.card + Strict.card ≤ G.secondOutdegree p := by
      change PS.card + Strict.card ≤ (G.secondOutNeighborFinset p).card
      rw [← Finset.card_union_of_disjoint hDisjoint]
      exact Finset.card_le_card (Finset.union_subset hPS hStrict)
    have hDirect : Direct ⊆ C.H.filter (G.Adj p) := by
      simpa [Direct, U, N] using
        directZEffective_direct_subset_H G C hG hPB p hpP hps
    have hDirectCard : Direct.card ≤ Shared.directCount G C.H p :=
      Finset.card_le_card hDirect
    have hSplit := Finset.card_sdiff_add_card_inter U N
    change Strict.card + Direct.card = U.card at hSplit
    change PS.card + U.card ≤ G.secondOutdegree p + Shared.directCount G C.H p
    omega

theorem pSecondPCount_le_graphPSecond {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 6) (p : Nat) (hp : p < 7) :
    (pSecondPCount zCount (graphBits G L) p).toNat ≤
      (C.P.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply count_le_filterCard C.P L.p
    (fun q ↦ strictSecondLocal zCount (graphBits G L) (8 + p) (8 + q))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro j hj
  have hmem := strictSecondLocal_true_mem G C L hG hzLe
    (8 + p) (8 + j) (by omega) (by omega) hj
  simpa [labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
    show 8 + j.val < 15 by omega] using hmem

theorem pSecondPCount_le_qCount {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hzLe : zCount ≤ 6) (p : Nat) (hp : p < 7) :
    (pSecondPCount zCount (graphBits G L) p).toNat ≤
      TerminalAlphaBeta.qCount G C.P C.H (L.p ⟨p, hp⟩).1 := by
  unfold pSecondPCount TerminalAlphaBeta.qCount
  unfold TerminalAlphaBeta.secondNeighborsThrough
  apply count_le_filterCard C.P L.p
    (fun q => strictSecondLocal zCount (graphBits G L) (8 + p) (8 + q))
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
    have hTrue : coreArc zCount (graphBits G L) (8 + p) (8 + j.val) = true := by
      rw [coreArc_graphBits G C L hG (8 + p) (8 + j.val)
        (by omega) (by omega) hzLe]
      exact decide_eq_true (by
        simpa [labelledVertex, show ¬8 + p < 8 by omega,
          show 8 + p < 15 by omega, show ¬8 + j.val < 8 by omega,
          show 8 + j.val < 15 by omega] using hAdj)
    simp [hTrue] at hNotDirect
  have hFirstGraph : G.Adj (L.p ⟨p, hp⟩).1 (labelledVertex G L middle) := by
    have hFirst' := hFirst
    rw [coreArc_graphBits G C L hG (8 + p) middle
      (by omega) (by omega) hzLe] at hFirst'
    simpa [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 15 by omega] using hFirst'
  have hSecondGraph : G.Adj (labelledVertex G L middle) (L.p j).1 := by
    have hSecond' := hSecond
    rw [coreArc_graphBits G C L hG middle (8 + j.val)
      (by omega) (by omega) hzLe] at hSecond'
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
      by_cases hmH : middle < 5
      · apply Finset.mem_union_right
        simp only [labelledVertex, dif_pos hmA]
        by_cases hmSmall : middle < 3
        · have hi : middle - 1 < 2 := by omega
          have hIdx : (⟨middle, hmA⟩ : Fin 8) =
              ⟨(middle - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [hIdx]
          exact Finset.mem_union_left C.X (L.a_aOne ⟨middle - 1, hi⟩)
        · have hi : middle - 3 < 2 := by omega
          have hIdx : (⟨middle, hmA⟩ : Fin 8) =
              ⟨(middle - 3) + 3, by omega⟩ := Fin.ext (by simp; omega)
          rw [hIdx]
          exact Finset.mem_union_right C.A1 (L.a_x ⟨middle - 3, hi⟩)
      · have hmCase : middle = 5 ∨ middle = 6 ∨ middle = 7 := by omega
        rcases hmCase with rfl | rfl | rfl
        · exact (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
            G C _ _ (L.p ⟨p, hp⟩).2 (L.a_r 0) (by
              simpa [labelledVertex] using hFirstGraph)).elim
        · exact (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
            G C _ _ (L.p ⟨p, hp⟩).2 (L.a_r 1) (by
              simpa [labelledVertex] using hFirstGraph)).elim
        · exact (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
            G C _ _ (L.p ⟨p, hp⟩).2 (L.a_r 2) (by
              simpa [labelledVertex] using hFirstGraph)).elim
    · apply Finset.mem_union_left
      simp [labelledVertex, hmA, show middle < 15 by omega]
  exact ⟨hNotAdj, hTargetNe,
    labelledVertex G L middle, hMiddle, hFirstGraph, hSecondGraph⟩

theorem external_row_missing_le_total {zCount : Nat}
    (C : G.LocalConfiguration) (hPCard : C.P.card = 7)
    (hECard : (externalTargets G C).card = zCount)
    (p : V) (hpP : p ∈ C.P) :
    zCount - directCount G (externalTargets G C) p ≤
      7 * zCount - edgeCount G C.P (externalTargets G C) := by
  have hOther : ∑ q ∈ C.P.erase p, directCount G (externalTargets G C) q ≤
      6 * zCount := by
    calc
      _ ≤ ∑ _q ∈ C.P.erase p, zCount := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
      _ = 6 * zCount := by simp [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit := Finset.sum_erase_add C.P
    (fun q => directCount G (externalTargets G C) q) hpP
  have hBound : edgeCount G C.P (externalTargets G C) ≤
      6 * zCount + directCount G (externalTargets G C) p := by
    unfold edgeCount
    omega
  have hTotal := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, hECard] at hTotal
  omega

theorem directZ_to_P_capacity_external {zCount : Nat}
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPCard : C.P.card = 7)
    (hECard : (externalTargets G C).card = zCount)
    (p : V) (hpP : p ∈ C.P) (hps : ¬G.Adj p C.s) :
    edgeCount G (FiveZUnionEightCapacity.directZNeighbors G C p) C.P ≤
      (7 * zCount - edgeCount G C.P (externalTargets G C)) -
        (zCount - (FiveZUnionEightCapacity.directZNeighbors G C p).card) := by
  let S := FiveZUnionEightCapacity.directZNeighbors G C p
  let E := externalTargets G C
  let T := E \ S
  have hS : S ⊆ E := by
    intro z hz
    exact Finset.mem_union_left _
      (FiveZUnionEightCapacity.directZNeighbors_subset_Z G C p hz)
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = E := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = zCount - S.card := by
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
    · exact (Finset.mem_sdiff.mp hzT).2
        (Finset.mem_filter.mpr ⟨hzZ, hpz⟩)
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
        · subst q
          simp [hpT]
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
  have hSCard : S.card + T.card = zCount := by
    rw [hTCard]
    have := (Finset.card_le_card hS).trans_eq hECard
    omega
  have hPEUpper := edgeCount_le_card_mul_card G C.P E
  rw [hPCard, hECard] at hPEUpper
  change edgeCount G S C.P ≤
    (7 * zCount - edgeCount G C.P E) - (zCount - S.card)
  omega

set_option maxHeartbeats 5000000 in
-- The finite table proof expands all `(zCount,m,s)` arithmetic leaves.
theorem individualEffectiveLower_graph {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 4)
    (hZCases : zCount = 4 ∨ zCount = 5 ∨ zCount = 6)
    (hmBound : 7 * zCount - edgeCount G C.P (externalTargets G C) ≤ 7 * zCount - 26)
    (p : Nat) (hp : p < 7) (hps : ¬G.Adj (L.p ⟨p, hp⟩).1 C.s) :
    (individualEffectiveLower zCount (graphBits G L) p).toNat ≤
      (directZEffectiveUnion G C (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G L
  let v := (L.p ⟨p, hp⟩).1
  let S := FiveZUnionEightCapacity.directZNeighbors G C v
  let U := directZEffectiveUnion G C v
  let m := 7 * zCount - edgeCount G C.P (externalTargets G C)
  let s := S.card
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hZSubE : C.Z ⊆ externalTargets G C := Finset.subset_union_left
  have hs : s ≤ zCount :=
    (Finset.card_le_card ((FiveZUnionEightCapacity.directZNeighbors_subset_Z
      G C v).trans hZSubE)).trans_eq hZCard
  have hLower := directZ_effective_capacity_lower G C hMin v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hRow := external_row_missing_le_total G C hPCard hZCard v hvP
  have hToP := directZ_to_P_capacity_external G C hG hPCard hZCard
    v hvP (by simpa [v] using hps)
  have hM : (externalMissing zCount bits).toNat = m := by
    exact externalMissing_toNat G C L hG hHCard
      (by rcases hZCases with rfl | rfl | rfl <;> omega)
  have hS : (pZOut zCount bits p).toNat = s := by
    rw [(pBlockCounts G C L hG hHCard
      (by rcases hZCases with rfl | rfl | rfl <;> omega) p hp).2.2,
      SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets G C v hvP]
    have hps' : ¬G.Adj v C.s := by simpa [v] using hps
    rw [show epsilonAt G v C.s = 0 by simp [epsilonAt, hps'], Nat.add_zero]
    change Shared.directCount G C.Z v = S.card
    exact (FiveZUnionEightCapacity.card_directZNeighbors G C v).symm
  have hES : Shared.directCount G (externalTargets G C) v = s := by
    rw [← (pBlockCounts G C L hG hHCard
      (by rcases hZCases with rfl | rfl | rfl <;> omega) p hp).2.2, hS]
  change zCount - Shared.directCount G (externalTargets G C) v ≤ m at hRow
  rw [hES] at hRow
  have hMBV : externalMissing zCount bits = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rcases hZCases with rfl | rfl | rfl <;> omega
  have hSBV : pZOut zCount bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rcases hZCases with rfl | rfl | rfl <;> omega
  have hm : m ≤ 7 * zCount - 26 := by simpa [m] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (zCount - s) at hToP
  change (individualEffectiveLower zCount bits p).toNat ≤ U.card
  rcases hZCases with rfl | rfl | rfl
  all_goals
    simp only [individualEffectiveLower, individualEffectiveLowerFour,
      individualEffectiveLowerFive, individualEffectiveLowerSix]
    rw [hMBV, hSBV]
    interval_cases m <;> interval_cases s <;>
      simp only [Nat.choose, add_zero, nonpos_iff_eq_zero, tsub_zero, zero_tsub,
        zero_mul, zero_le, BitVec.ofNat_eq_ofNat, BEq.rfl, ↓reduceIte,
        effectiveAtRowSize, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
        Nat.add_one_sub_one, one_mul, tsub_le_iff_right, BitVec.reduceBEq,
        Bool.false_eq_true, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, tsub_self,
        Nat.one_le_ofNat, Nat.sub_eq_zero_of_le, Nat.reduceLeDiff, Finset.one_le_card,
        Nat.one_mod, Nat.not_ofNat_le_one, Nat.reduceEqDiff, Nat.succ_ne_self,
        OfNat.ofNat_ne_zero, Std.le_refl, one_ne_zero]
        at hInternal hToP hRow hLower ⊢ <;>
      first | omega | exact Finset.card_pos.mp (by omega)

theorem pEffectiveCondition_true {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hHCard : C.H.card = 4)
    (hZCases : zCount = 4 ∨ zCount = 5 ∨ zCount = 6)
    (hmBound : 7 * zCount - edgeCount G C.P (externalTargets G C) ≤ 7 * zCount - 26) :
    all 7 (pEffectiveCondition zCount (graphBits G L)) = true := by
  let bits := graphBits G L
  have hzLe : zCount ≤ 6 := by
    rcases hZCases with rfl | rfl | rfl <;> omega
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hBlocks := pBlockCounts G C L hG hHCard hzLe p hp
  have hNatural : (pSecondPCount zCount bits p).toNat +
      (individualEffectiveLower zCount bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut zCount bits p).toNat := by
    change (pSecondPCount zCount (graphBits G L) p).toNat +
        (individualEffectiveLower zCount (graphBits G L) p).toNat + 1 ≤
      (pOut (graphBits G L) p).toNat +
        2 * (pHOut (graphBits G L) p).toNat +
        (pZOut zCount (graphBits G L) p).toNat
    by_cases hps : G.Adj v C.s
    · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
        G C hG hPB hNoSeymour hRootDegree v hvP hps
      have hSecond := pSecondPCount_le_qCount G C L hG hzLe p hp
      let m := 7 * zCount - edgeCount G C.P (externalTargets G C)
      let s := Shared.directCount G (externalTargets G C) v
      have hm : m ≤ 7 * zCount - 26 := by simpa [m] using hmBound
      have hs : s ≤ zCount :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      have hRow := external_row_missing_le_total G C hPCard hZCard v hvP
      have hMNat : (externalMissing zCount bits).toNat = m := by
        simpa [bits] using externalMissing_toNat G C L hG hHCard hzLe
      have hSNat : (pZOut zCount bits p).toNat = s := by
        simpa [bits, s] using hBlocks.2.2
      have hMBV : externalMissing zCount bits = BitVec.ofNat 8 m := by
        apply BitVec.eq_of_toNat_eq
        rw [hMNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        rcases hZCases with rfl | rfl | rfl <;> omega
      have hSBV : pZOut zCount bits p = BitVec.ofNat 8 s := by
        apply BitVec.eq_of_toNat_eq
        rw [hSNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        rcases hZCases with rfl | rfl | rfl <;> omega
      have hTable : (individualEffectiveLower zCount bits p).toNat ≤ 8 := by
        change zCount - s ≤ m at hRow
        rcases hZCases with rfl | rfl | rfl
        · change (individualEffectiveLowerFour bits p).toNat ≤ 8
          unfold individualEffectiveLowerFour
          rw [hMBV, hSBV]
          interval_cases m <;> interval_cases s <;>
            simp [effectiveAtRowSize] at hRow ⊢
        · change (individualEffectiveLowerFive bits p).toNat ≤ 8
          unfold individualEffectiveLowerFive
          rw [hMBV, hSBV]
          interval_cases m <;> interval_cases s <;>
            simp [effectiveAtRowSize] at hRow ⊢
        · change (individualEffectiveLowerSix bits p).toNat ≤ 8
          unfold individualEffectiveLowerSix
          rw [hMBV, hSBV]
          interval_cases m <;> interval_cases s <;>
            simp [effectiveAtRowSize] at hRow ⊢
      change (individualEffectiveLower zCount (graphBits G L) p).toNat ≤ 8 at hTable
      have hEpsilon : epsilonAt G v C.s = 1 := by simp [epsilonAt, hps]
      rw [hEpsilon] at hEquation
      dsimp [v] at hSecond hEquation hTable hps
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      rw [SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets G C
        (L.p ⟨p, hp⟩).1 hvP]
      simp [epsilonAt, hps]
      omega
    · have hTable := individualEffectiveLower_graph G C L hG hMin hHCard
        hZCases hmBound p hp (by simpa [v] using hps)
      have hPS := pSecondPCount_le_graphPSecond G C L hG hzLe p hp
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
  change ((pSecondPCount zCount bits p).toNat +
      (individualEffectiveLower zCount bits p).toNat + 1) % 256 ≤
    ((pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pZOut zCount bits p).toNat) % 256
  have hRightSmall : (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pZOut zCount bits p).toNat < 256 := by
    have hpLe : (pOut bits p).toNat ≤ 7 := by
      rw [hBlocks.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hhLe : (pHOut bits p).toNat ≤ 4 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hzLe' : (pZOut zCount bits p).toNat ≤ zCount := by
      rw [hBlocks.2.2]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
    omega
  rw [Nat.mod_eq_of_lt hRightSmall,
    Nat.mod_eq_of_lt (hNatural.trans_lt hRightSmall)]
  exact hNatural

theorem nineteen_le_H_to_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hr : C.r = 7) (hk : C.k = 2) (hx : C.x = 2)
    (hPB : C.P = C.B) :
    19 ≤ edgeCount G C.H C.P := by
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  have hR := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  rw [hx] at hHCard hR
  have hRCard : C.R.card = 3 := by omega
  have hA1Card : C.A1.card = 2 := hk
  have hXCard : C.X.card = 2 := hx
  have hPCard : C.P.card = 7 := hr
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro a haA haP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) haA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C haP)
  have hDegreePoint (u : V) (hu : u ∈ C.H) :
      G.outdegree u = Shared.directCount G C.A u + Shared.directCount G C.P u := by
    have h := outdegree_eq_directCount_of_captured G (C.A ∪ C.P) u
      (Shared.H_outgoingCaptured G C hG hPB u hu)
    rw [directCount_union_of_disjoint G C.A C.P u hAP] at h
    exact h
  have hDegreeEq (S : Finset V) (hS : S ⊆ C.H) :
      ∑ u ∈ S, G.outdegree u = edgeCount G S C.A + edgeCount G S C.P := by
    unfold edgeCount
    calc
      ∑ u ∈ S, G.outdegree u =
          ∑ u ∈ S, (Shared.directCount G C.A u + Shared.directCount G C.P u) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hDegreePoint u (hS hu)
      _ = _ := by rw [Finset.sum_add_distrib]
  have hA1Degree : 16 ≤ edgeCount G C.A1 C.A + edgeCount G C.A1 C.P := by
    rw [← hDegreeEq C.A1 (Finset.subset_union_left)]
    calc
      16 = ∑ _u ∈ C.A1, 8 := by simp [hA1Card]
      _ ≤ ∑ u ∈ C.A1, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hXDegree : 16 ≤ edgeCount G C.X C.A + edgeCount G C.X C.P := by
    rw [← hDegreeEq C.X (Finset.subset_union_right)]
    calc
      16 = ∑ _u ∈ C.X, 8 := by simp [hXCard]
      _ ≤ ∑ u ∈ C.X, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hA1ToH : edgeCount G C.A1 C.A ≤ edgeCount G C.A1 C.H := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_le_sum
    intro u hu
    exact Finset.card_le_card (BSixKThree.A1_A_neighbors_subset_H G C hG u hu)
  have hA1HSplit : edgeCount G C.A1 C.H =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X := by
    exact edgeCount_union_of_disjoint G C.A1 C.A1 C.X
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hA1Internal := internal_edgeCount_le_choose_two G C.A1 hG
  have hA1X := edgeCount_le_card_mul_card G C.A1 C.X
  rw [hA1Card] at hA1Internal
  rw [hA1Card, hXCard] at hA1X
  norm_num [Nat.choose] at hA1Internal
  have hA1AUpper : edgeCount G C.A1 C.A ≤ 5 := by omega
  have hTied : ∃ u ∈ C.A1, Shared.directCount G C.A u = 2 := by
    by_contra hn
    push Not at hn
    have hSix : 6 ≤ edgeCount G C.A1 C.A := by
      unfold edgeCount
      calc
        6 = ∑ _u ∈ C.A1, 3 := by simp [hA1Card]
        _ ≤ ∑ u ∈ C.A1, Shared.directCount G C.A u := by
          apply Finset.sum_le_sum
          intro u hu
          have hTwo : 2 ≤ Shared.directCount G C.A u := by
            simpa [Shared.directCount, CertificateBridge.internalFirstNeighbors, hk]
              using (hPivot u
                (Digraph.LocalConfiguration.A1_subset_A (G := G) C hu)).1
          have hNe := hn u hu
          omega
    omega
  obtain ⟨u, huA1, huA⟩ := hTied
  have huP : 7 ≤ Shared.directCount G C.P u := by
    have hTie := (hPivot u
      (Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1)).2
    have hEq : (C.A.filter (G.Adj u)).card = C.k := by
      simpa [Shared.directCount, CertificateBridge.internalFirstNeighbors, hk]
        using huA
    have := hTie hEq
    simpa [Shared.directCount, CertificateBridge.internalFirstNeighbors, hPB, hr]
      using this
  have hOtherLower : 8 ≤ ∑ v ∈ C.A1.erase u,
      (Shared.directCount G C.A v + Shared.directCount G C.P v) := by
    calc
      8 = ∑ _v ∈ C.A1.erase u, 8 := by
        simp [Finset.card_erase_of_mem huA1, hA1Card]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← hDegreePoint v
          (Finset.mem_union_left C.X (Finset.mem_of_mem_erase hv))]
        exact hMin v
  have hA1Strong : 17 ≤ edgeCount G C.A1 C.A + edgeCount G C.A1 C.P := by
    unfold edgeCount
    rw [← Finset.sum_add_distrib, ← Finset.sum_erase_add C.A1
      (fun v ↦ Shared.directCount G C.A v + Shared.directCount G C.P v) huA1]
    omega
  have hATo := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  rw [hHCard, hx, hRCard] at hATo
  norm_num [Nat.choose] at hATo
  have hHASplit : edgeCount G C.H C.A =
      edgeCount G C.A1 C.A + edgeCount G C.X C.A := by
    exact BSixKThree.edgeCount_source_union G C.A1 C.X C.A
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hHPSplit : edgeCount G C.H C.P =
      edgeCount G C.A1 C.P + edgeCount G C.X C.P := by
    exact BSixKThree.edgeCount_source_union G C.A1 C.X C.P
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  omega

theorem H_to_P_add_externalMissing_le_capacity {zCount : Nat}
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (hPCard : C.P.card = 7)
    (hZCard : (externalTargets G C).card = zCount) (hHCard : C.H.card = 4)
    (hzLe : zCount ≤ 6) :
    edgeCount G C.H C.P + (7 * zCount - edgeCount G C.P (externalTargets G C)) ≤
      7 * zCount - 7 := by
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
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHPlusPZ : 35 ≤
      edgeCount G C.P C.H + edgeCount G C.P (externalTargets G C) := by omega
  have hHPPlusSeven : edgeCount G C.H C.P + 7 ≤
      edgeCount G C.P (externalTargets G C) := by omega
  omega

theorem retainedAfterAOnePairDeletion_zero_one (vertex : Nat) :
    retainedAfterAOnePairDeletion 0 1 vertex = decide (8 ≤ vertex ∧ vertex < 15) := by
  unfold retainedAfterAOnePairDeletion
  by_cases hSmall : 1 ≤ vertex ∧ vertex < 3
  · rcases (show vertex = 1 ∨ vertex = 2 by omega) with rfl | rfl <;> decide
  · have hSmallBool : (1 ≤ vertex && vertex < 3) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    rw [hSmallBool]
    by_cases hP : 8 ≤ vertex ∧ vertex < 15
    · simp [hP.1, hP.2]
      omega
    · have hPBool : (8 ≤ vertex && vertex < 15) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp [hPBool, hP]

set_option maxHeartbeats 1000000 in
theorem aOnePairDeletionExpands_true {zCount : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hzLe : zCount ≤ 6) :
    aOnePairDeletionExpands zCount (graphBits G L) = true := by
  let E := G.outNeighborFinsetOf C.P \ (C.P ∪ {C.a1})
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hPOut : (C.P : Set V) ⊆ G.outNeighborSet C.a1 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hExpansion : 7 ≤ E.card := by
    simpa [E, hPCard] using Digraph.oneVertexReduction G hBound hG hNoSeymour
      hPOut (by omega)
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro target htE
    rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
    obtain ⟨middle, hmP, hmt⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
    exact P_outgoingCaptured_retained G C hG hPB middle hmP
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hmt)
  let goodTarget : Nat → Bool :=
    aOnePairDeletionReached zCount (graphBits G L) 0 1
  have hCount : E.card ≤ (count (15 + zCount) goodTarget).toNat := by
    have hFilter := filterCard_le_count (V := V) (retainedVertexSet G C)
      (retainedLabelEquiv G C L hG) goodTarget (fun v ↦ v ∈ E) (by omega) (by
        intro target htE
        rw [retainedLabelEquiv_val G C L hG] at htE
        rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
        have htAOne : labelledVertex G L target.val ≠ C.a1 := by
          intro heq
          apply htOutside
          exact Finset.mem_union_right C.P (Finset.mem_singleton.mpr heq)
        have htZero : target.val ≠ 0 := by
          intro hzero
          apply htAOne
          have htarget : target = ⟨0, by omega⟩ := Fin.ext hzero
          rw [htarget]
          simpa [labelledVertex] using L.a_zero
        have htNotPIndex : ¬(8 ≤ target.val ∧ target.val < 15) := by
          rintro ⟨ht8, ht15⟩
          apply htOutside
          apply Finset.mem_union_left
          have htP : labelledVertex G L target.val ∈ C.P := by
            simp only [labelledVertex, dif_pos ht15]
            rw [dif_neg (not_lt_of_ge ht8)]
            exact (L.p ⟨target.val - 8, by omega⟩).2
          exact htP
        obtain ⟨middle, hmP, hmt⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
        obtain ⟨i, hi⟩ := L.p.surjective ⟨middle, hmP⟩
        let mi := 8 + i.val
        have hmi : mi < 15 := by omega
        have hmLabel : labelledVertex G L mi = middle := by
          simp [mi, labelledVertex, show ¬8 + i.val < 8 by omega,
            show 8 + i.val < 15 by omega, congrArg Subtype.val hi]
        dsimp only [goodTarget, aOnePairDeletionReached]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨htZero, ?_⟩, ?_⟩
        · rw [retainedAfterAOnePairDeletion_zero_one]
          simp [htNotPIndex]
        · rw [any_eq_true_iff]
          refine ⟨mi, hmi, ?_⟩
          rw [Bool.and_eq_true, retainedAfterAOnePairDeletion_zero_one,
            coreArc_graphBits G C L hG mi target.val hmi target.isLt hzLe]
          constructor
          · exact decide_eq_true (by simp [mi]; omega)
          · rw [hmLabel]
            exact decide_eq_true hmt)
    have hFilterEq : ((retainedVertexSet G C).filter fun v ↦ v ∈ E).card =
        E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv ↦ hv.2, fun hv ↦ ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    exact hFilter
  unfold aOnePairDeletionExpands
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  exact hExpansion.trans hCount

theorem commonCore_true {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hPB : C.P = C.B) (hk : C.k = 2) (hXCard : C.X.card = 2)
    (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (hHCard : C.H.card = 4) (hzLe : zCount ≤ 6)
    (hPOrder : ∀ q : Fin 6,
      Labels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pKey G C (L.p ⟨q.val, by omega⟩).1)
    (hZOrder : ∀ q : Fin (zCount - 1),
      Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
        Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val, by omega⟩).1)
    (hAOneOrder : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨4 + q.val, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨3 + q.val, by omega⟩).1)
    (hROrder : ∀ q : Fin 2,
      Labels.structuralKey G C (L.a ⟨q.val + 6, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 5, by omega⟩).1) :
    commonCore zCount (graphBits G L) = true := by
  have hOrA := orientedA_true G C L hG
  have hOrP := orientedP_true G C L hG
  have hOrPH := orientedPH_true G C L hG
  have hFixed := fixedA_true G C L hG
  have hXReach := everyXReached_true G C L hk
  have hZReach := allZReached_true G C L hzLe
  have hInactive := inactiveZZero_true G C L hzLe
  have hThree := three_le_aOneToXCount G C L hG hPivot hk hXCard
  have hThreeBool : (3 : BitVec 8).ule (count 4 fun q ↦
      aArc (graphBits G L) (1 + q / 2) (3 + q % 2)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hThree
  have hAMin := aMinimumAndDegree_true G C L hG hPB hPivot hMin hk
  have hANon := aNonSeymour_all_true G C L hG hPB hNoSeymour hzLe
  have hPMin := pMinimumDegree_true G C L hG hPB hHCard hMin hzLe
  have hPNon := pNonSeymour_all_true G C L hG hPB hNoSeymour hzLe
  have hDelete := aOnePairDeletionExpands_true G hBound C L hG hPB
    hNoSeymour hzLe
  have hSharp := XTwoNoRoot.Core.sharpKing_of_orientedP zCount (graphBits G L) hOrP
  have hOP := orderedP_true G C L hG hPB hHCard hzLe hPOrder
  have hOZ := orderedZ_true G C L hzLe hZOrder
  have hOS := orderedStructuralClasses_true G C L hAOneOrder hXOrder hROrder
  simp only [commonCore, hOrA, hOrP, hOrPH, hFixed, hXReach, hZReach,
    hInactive, hThreeBool, hAMin, hANon, hPMin, hPNon, hDelete, hSharp, hOP, hOZ,
    hOS, Bool.and_self]

theorem smallCore_true_of_components {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hHCard : C.H.card = 4) (hzLe : zCount ≤ 6)
    (hCommon : commonCore zCount (graphBits G L) = true)
    (hEffective : all 7 (pEffectiveCondition zCount (graphBits G L)) = true)
    (hHP : 19 ≤ edgeCount G C.H C.P)
    (hCapacity : edgeCount G C.H C.P +
      (7 * zCount - edgeCount G C.P (externalTargets G C)) ≤ 7 * zCount - 7) :
    smallCore zCount (graphBits G L) = true := by
  have hHPNat := totalHToP_toNat G C L hHCard
  have hMissingNat := externalMissing_toNat G C L hG hHCard hzLe
  have hzSmall : 7 * zCount < 256 := by omega
  have hLower : (19 : BitVec 8).ule
      (totalHToP (graphBits G L)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hHPNat]
    exact hHP
  have hUpper : (totalHToP (graphBits G L) +
      externalMissing zCount (graphBits G L)).ule
        (BitVec.ofNat 8 ((7 * zCount - 7 : Nat))) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
      hHPNat, hMissingNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (hCapacity.trans_lt (by omega)),
      Nat.mod_eq_of_lt (by omega)]
    exact hCapacity
  simp only [smallCore, hCommon, hEffective, hLower, hUpper, Bool.and_self]

end SeymourEight.BSevenKTwo.RSeven.XTwoRoot.Assembly
