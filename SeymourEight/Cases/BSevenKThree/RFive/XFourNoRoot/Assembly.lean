import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.GraphFacts
import SeymourEight.Cases.BSevenKThree.Counting
import SeymourEight.Shared.InnerDegreeThree

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Assembly

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem orientedA_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    orientedA (graphArc G L) = true := by
  rw [orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true]
  constructor
  · rw [aArc_graph G L i i hi hi]
    simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [aArc_graph G L i j hi hj, aArc_graph G L j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    by_cases h : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
    · simp [hij, h, hG.2 h]
    · simp [hij, h]

theorem orientedP_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    orientedP (graphArc G L) = true := by
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true]
  constructor
  · rw [pArc_graph G L i i hi hi]
    simpa using hG.1 (L.p ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [pArc_graph G L i j hi hj, pArc_graph G L j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    by_cases h : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
    · simp [hij, h, hG.2 h]
    · simp [hij, h]

theorem orientedPH_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    orientedPH (graphArc G L) = true := by
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  rw [pToA_graph G L p (1 + h) hp (by omega),
    aToP_graph G L (1 + h) p (by omega) hp]
  by_cases ha : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨1 + h, by omega⟩).1
  · simp [ha, hG.2 ha]
  · simp [ha]

theorem fixedAOne_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    fixedAOne (graphArc G L) = true := by
  rw [fixedAOne, all_eq_true_iff]
  intro j hj
  by_cases hjA : j < 8
  · simp only [graphArc, dif_pos (by omega : 0 < 8), dif_pos hjA]
    have hzero : (L.a ⟨0, by omega⟩).1 = C.a1 := by simpa using L.a_zero
    rw [hzero]
    by_cases hA1 : 1 ≤ j ∧ j ≤ 3
    · have hjMem : (L.a ⟨j, hjA⟩).1 ∈ C.A1 := by
        have heq : (⟨j, hjA⟩ : Fin 8) = ⟨(j - 1) + 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [heq]
        exact L.a_aOne ⟨j - 1, by omega⟩
      simp [hA1, (Finset.mem_filter.mp hjMem).2]
    · have hn : ¬G.Adj C.a1 (L.a ⟨j, hjA⟩).1 := by
        intro ha
        have hm : (L.a ⟨j, hjA⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        have hj0 : j ≠ 0 := by
          intro hj0
          subst j
          exact hG.1 C.a1 (by simpa [L.a_zero] using ha)
        have hjX : (L.a ⟨j, hjA⟩).1 ∈ C.X := by
          have heq : (⟨j, hjA⟩ : Fin 8) = ⟨(j - 4) + 4, by omega⟩ :=
            Fin.ext (by simp; omega)
          rw [heq]
          exact L.a_x ⟨j - 4, by omega⟩
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hm hjX
      simp [hA1, hn] ; omega
  · by_cases hjP : j < 13
    · have hadj : G.Adj C.a1 (L.p ⟨j - 8, by omega⟩).1 :=
        (Finset.mem_filter.mp (L.p ⟨j - 8, by omega⟩).2).2
      simp [graphArc, L.a_zero, hjA, hjP, hadj, show 8 ≤ j by omega]
    · have hjQ : j < 15 := by omega
      have hn : ¬G.Adj C.a1 (L.q ⟨j - 13, by omega⟩).1 := by
        intro ha
        exact (Finset.mem_sdiff.mp (L.q ⟨j - 13, by omega⟩).2).2
          (Finset.mem_filter.mpr ⟨
            Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q _).2, ha⟩)
      simp [graphArc, L.a_zero, hjA, hjP, hjQ, hn] ; omega

theorem noPToAOne_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    noPToAOne (graphArc G L) = true := by
  rw [noPToAOne, all_eq_true_iff]
  intro p hp
  rw [pToA_graph G L p 0 hp (by omega)]
  have hzero : (L.a ⟨0, by omega⟩).1 = C.a1 := by simpa using L.a_zero
  rw [hzero]
  have ha : G.Adj C.a1 (L.p ⟨p, hp⟩).1 :=
    (Finset.mem_filter.mp (L.p ⟨p, hp⟩).2).2
  simp [hG.2 ha]

theorem qInB_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : qInB (graphArc G L) = true := by
  rw [qInB, all_eq_true_iff]
  intro q hq
  rw [any_eq_true_iff]
  have hqB := Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q ⟨q, hq⟩).2
  rw [Digraph.LocalConfiguration.B, Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet] at hqB
  rcases hqB.1 with ⟨a, hsa, haq⟩
  have haA : a ∈ C.A := (Digraph.mem_outNeighborFinset (G := G)).mpr hsa
  obtain ⟨i, hi⟩ := L.a.surjective ⟨a, haA⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [aToQ_graph G L i q i.isLt hq]
  simpa [congrArg Subtype.val hi] using haq

theorem qReached_iff_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) (q : Fin 2) :
    qReached (graphArc G L) q = true ↔ (L.q q).1 ∈ BSevenKThree.reachedQ G C := by
  rw [qReached, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · obtain ⟨i, hi, hadj⟩ := (any_eq_true_iff 3 _).mp h
      rw [aToQ_graph G L (1 + i) q (by omega) q.isLt] at hadj
      have hsrc : (L.a ⟨1 + i, by omega⟩).1 =
          (aOneLabelEquiv G C L hA1Card ⟨i, hi⟩).1 := by
        simp [Nat.add_comm]
      exact Finset.mem_inter.mpr ⟨(L.q q).2,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨_, Finset.mem_union_left C.P (aOneLabelEquiv G C L hA1Card ⟨i, hi⟩).2,
            by simpa [hsrc] using of_decide_eq_true hadj⟩⟩
    · obtain ⟨i, hi, hadj⟩ := (any_eq_true_iff 5 _).mp h
      rw [pToQ_graph G L i q hi q.isLt] at hadj
      exact Finset.mem_inter.mpr ⟨(L.q q).2,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨_, Finset.mem_union_right C.A1 (L.p ⟨i, hi⟩).2,
            of_decide_eq_true hadj⟩⟩
  · intro hmem
    rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_inter.mp hmem).2 with ⟨u, hu, huq⟩
    rcases Finset.mem_union.mp hu with huA | huP
    · left
      rw [any_eq_true_iff]
      obtain ⟨i, hi⟩ := (aOneLabelEquiv G C L hA1Card).surjective ⟨u, huA⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [aToQ_graph G L (1 + i) q (by omega) q.isLt]
      have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := by
        simpa [aOneLabelEquiv] using congrArg Subtype.val hi
      have hSource : (⟨1 + i.val, by omega⟩ : Fin 8) =
          ⟨i.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hSource, hiVal]
      exact decide_eq_true huq
    · right
      rw [any_eq_true_iff]
      obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [pToQ_graph G L i q i.isLt q.isLt]
      simpa [congrArg Subtype.val hi] using huq

theorem qReachStatus_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3)
    (yValue : Nat) (hy : BSevenKThree.y G C = yValue) :
    qReachStatus yValue (graphArc G L) = true := by
  have hCount : (count 2 (qReached (graphArc G L))).toNat =
      (BSevenKThree.reachedQ G C).card := by
    rw [toNat_count_eq_fin_sum 2 _ (by omega)]
    calc
      (∑ q : Fin 2, if qReached (graphArc G L) q = true then 1 else 0) =
          ∑ q : Fin 2, if (L.q q).1 ∈ BSevenKThree.reachedQ G C then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases h : qReached (graphArc G L) q = true
        · have hm := (qReached_iff_mem G C L hA1Card q).mp h
          simp [h, hm]
        · have hn : (L.q q).1 ∉ BSevenKThree.reachedQ G C := by
            intro hm
            exact h ((qReached_iff_mem G C L hA1Card q).mpr hm)
          simp [Bool.eq_false_of_not_eq_true h, hn]
      _ = (C.Q.filter fun v ↦ v ∈ BSevenKThree.reachedQ G C).card := by
        symm
        exact filterCard_eq_sum_fin C.Q L.q _
      _ = (BSevenKThree.reachedQ G C).card := by
        congr 1
        ext v
        simp only [Finset.mem_filter]
        constructor
        · exact fun h ↦ h.2
        · intro h
          exact ⟨Finset.inter_subset_left h, h⟩
  rw [qReachStatus]
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [hCount, BitVec.toNat_ofNat]
  have hyLe : yValue ≤ 2 := by
    rw [← hy, BSevenKThree.y]
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (by simpa using (Fintype.card_congr L.q).symm)
  rw [Nat.mod_eq_of_lt (by omega)]
  simpa [BSevenKThree.y] using hy

theorem everyXReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) :
    everyXReached (graphArc G L) = true := by
  rw [everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]; left; rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := (aOneLabelEquiv G C L hA1Card).surjective ⟨u, huA1⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [aArc_graph G L (1 + i) (4 + x) (by omega) (by omega)]
    have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := by
      simpa [aOneLabelEquiv] using congrArg Subtype.val hi
    have hSource : (⟨1 + i.val, by omega⟩ : Fin 8) =
        ⟨i.val + 1, by omega⟩ := Fin.ext (by simp; omega)
    have hTarget : (⟨4 + x, by omega⟩ : Fin 8) =
        ⟨x + 4, by omega⟩ := Fin.ext (by simp; omega)
    rw [hSource, hiVal, hTarget]
    exact decide_eq_true hux
  · rw [Bool.or_eq_true]; right; rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [pToA_graph G L i (4 + x) i.isLt (by omega)]
    simpa [Nat.add_comm, congrArg Subtype.val hi] using hux

theorem everyZReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : everyZReached zCount (graphPToZ G L) = true := by
  rw [everyZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  obtain ⟨p, hp, hpz⟩ : ∃ p ∈ C.P, G.Adj p (L.z ⟨z, hz⟩).1 := by
    rcases Finset.mem_union.mp (L.z ⟨z, hz⟩).2 with hvZ | hvRoot
    · exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp (Finset.mem_sdiff.mp hvZ).1
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : (L.z ⟨z, hz⟩).1 = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        simpa [hvs] using hReach
      · simp [rootSecondFinset, hReach] at hvRoot
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pToZ_graph G L i z i.isLt hz]
  simpa [congrArg Subtype.val hi] using hpz

theorem inactiveZZero_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) :
    inactiveZZero zCount (graphPToZ G L) = true := by
  rw [inactiveZZero, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro j hj
  simp [graphPToZ, hp]

theorem A_outdegree_eq_blocks {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (a : Nat) (ha : a < 8) :
    G.outdegree (L.a ⟨a, ha⟩).1 =
      directCount G C.A (L.a ⟨a, ha⟩).1 +
        directCount G C.B (L.a ⟨a, ha⟩).1 := by
  have hDis : Disjoint C.A C.B :=
    Digraph.LocalConfiguration.disjoint_A_B (G := G) C
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG (L.a ⟨a, ha⟩).1 (L.a _).2
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.B)
    (L.a ⟨a, ha⟩).1 hCap
  rw [directCount_union_of_disjoint G C.A C.B _ hDis] at hEq
  exact hEq

theorem aDegree_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (a : Nat) (ha : a < 8) :
    (aDegree (graphArc G L) a).toNat = G.outdegree (L.a ⟨a, ha⟩).1 := by
  rw [aDegree, BitVec.toNat_add, aOut_toNat G C L a ha,
    aBOut_toNat G C L a ha, Nat.mod_eq_of_lt, A_outdegree_eq_blocks G C L hG a ha]
  have hA := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.a ⟨a, ha⟩).1) C.A)
  have hB := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.a ⟨a, ha⟩).1) C.B)
  change directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card at hA
  change directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card at hB
  have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hBCard : C.B.card = 7 := by
    rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
    change C.P.card + C.Q.card = 7
    omega
  omega

theorem aConditions_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hr : C.r = 5) : aConditions (graphArc G L) = true := by
  rw [aConditions, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L a ha
  have hBO := aBOut_toNat G C L a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 3 ≤ (aOut (graphArc G L) a).toNat := by
    rw [hAO]
    simpa [hk, directCount, CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut (graphArc G L) a).toNat = 3 →
      5 ≤ (aBOut (graphArc G L) a).toNat := by
    intro heq
    rw [hBO]
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change directCount G C.A (L.a ⟨a, ha⟩).1 = 3
      rw [← hAO]
      exact heq
    simpa [hr, directCount, CertificateBridge.internalFirstNeighbors] using
      hPivotA.2 hCardEq
  have hTotal : 8 ≤ (aOut (graphArc G L) a).toNat +
      (aBOut (graphArc G L) a).toNat := by
    rw [hAO, hBO, ← A_outdegree_eq_blocks G C L hG a ha]
    exact hMin _
  simp only [Bool.and_eq_true, BitVec.ule_eq_decide,
    decide_eq_true_eq]
  refine ⟨⟨hAmin, ?_⟩, ?_⟩
  · by_cases heq : aOut (graphArc G L) a = 3
    · have ht := hTie (congrArg BitVec.toNat heq)
      simp [heq, ht]
    · rw [Bool.or_eq_true]
      left
      simpa [heq]
  · rw [aDegree, BitVec.toNat_add, Nat.mod_eq_of_lt]
    · exact hTotal
    · have hALe : (aOut (graphArc G L) a).toNat ≤ 8 := by
        rw [hAO]
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (by simpa using (Fintype.card_congr L.a).symm)
      have hBLe : (aBOut (graphArc G L) a).toNat ≤ 7 := by
        rw [hBO]
        apply (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C, hr]
        have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
        omega
      omega

theorem P_outdegree_eq_blocks {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (p : Nat) (hp : p < 5) :
    G.outdegree (L.p ⟨p, hp⟩).1 =
      directCount G C.P (L.p ⟨p, hp⟩).1 +
      directCount G C.H (L.p ⟨p, hp⟩).1 +
      directCount G C.Q (L.p ⟨p, hp⟩).1 +
      directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
  let v := (L.p ⟨p, hp⟩).1
  let W := externalTargets G C
  have hHP : Disjoint C.H C.P := Digraph.LocalConfiguration.disjoint_H_P (G := G) C
  have hHQ : Disjoint C.H C.Q := by
    apply Finset.disjoint_of_subset_left (Digraph.LocalConfiguration.H_subset_A (G := G) C)
    exact Finset.disjoint_of_subset_right (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)
  have hHPQ : Disjoint (C.H ∪ C.P) C.Q := by
    rw [Finset.disjoint_left]
    intro w hw hwQ
    rcases Finset.mem_union.mp hw with hwH | hwP
    · exact (Finset.disjoint_left.mp hHQ) hwH hwQ
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hwQ
  have hAllW : Disjoint (C.H ∪ C.P ∪ C.Q) W := by
    rw [Finset.disjoint_left]
    intro w hw hwW
    rcases Finset.mem_union.mp hw with hwHP | hwQ
    · rcases Finset.mem_union.mp hwHP with hwH | hwP
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_H_externalTargets G C hG)) hwH hwW
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hwP) hwW
    · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hwQ) hwW
  have hCap := BSixKThree.P_outgoingCaptured_general G C hG v (L.p ⟨p, hp⟩).2
  rw [outdegree_eq_directCount_of_captured G (C.H ∪ C.P ∪ C.Q ∪ W) v hCap,
    directCount_union_of_disjoint G (C.H ∪ C.P ∪ C.Q) W v hAllW,
    directCount_union_of_disjoint G (C.H ∪ C.P) C.Q v hHPQ,
    directCount_union_of_disjoint G C.H C.P v hHP]
  dsimp [v, W]
  omega

theorem pDegree_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hzLe : zCount ≤ 2)
    (p : Nat) (hp : p < 5) :
    (pDegree zCount (graphArc G L) (graphPToZ G L) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have h := pBlockCounts G C L hHCard (by omega) p hp
  rw [pDegree, pAuxOut, BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_add, h.1, h.2.1, h.2.2.1, h.2.2.2]
  have hP : directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 5 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.p).symm)
  have hH : directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hQ : directCount G C.Q (L.p ⟨p, hp⟩).1 ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.q).symm)
  have hZ : directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ zCount :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.z).symm)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  rw [P_outdegree_eq_blocks G C L hG p hp]
  omega

theorem pConditions_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hzLe : zCount ≤ 2)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    pConditions zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [pConditions, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pDegree_toNat G C L hG hHCard hzLe p hp]
  exact hMin _

theorem degreeThreeConsequences_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hOriented : orientedA (graphArc G L) = true)
    (hMinimum : ∀ a < 8, (3 : BitVec 8).ule (aOut (graphArc G L) a) = true) :
    degreeThreeClassification (graphArc G L) = true ∧
      threeInnerWitnesses (graphArc G L) = true := by
  let arc := aArc (graphArc G L)
  have hOr : InnerDegreeThree.oriented arc = true := by
    simpa [arc, InnerDegreeThree.oriented, orientedA] using hOriented
  have hMin : InnerDegreeThree.minimumThree arc = true := by
    rw [InnerDegreeThree.minimumThree, all_eq_true_iff]
    intro a ha
    simpa [arc, InnerDegreeThree.outCount, aOut] using hMinimum a ha
  exact ⟨InnerDegreeThree.classification_of arc hOr hMin,
    InnerDegreeThree.threeWitnesses_of arc hOr hMin⟩

theorem projectedNonSeymour_unaugmented {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzLe : zCount ≤ 2)
    (source : Nat) (hs : source < 13) :
    (projectedSecondCount zCount (graphArc G L) (graphPToZ G L) source).toNat <
      G.outdegree (labelledVertex G L source) := by
  exact (projectedSecondCount_le_graph_retained G C L hG (by omega) source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨_, h⟩))

theorem projectedSecondCount_toNat_lt_256 {zCount : Nat} (hzLe : zCount ≤ 2)
    (arc pToZ : Nat → Nat → Bool) (source : Nat) :
    (projectedSecondCount zCount arc pToZ source).toNat < 256 := by
  unfold projectedSecondCount
  rw [toNat_count _ _ (by omega)]
  calc
    _ ≤ ∑ _i ∈ Finset.range (15 + zCount), 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases projectedSecond zCount arc pToZ source i <;> decide
    _ = 15 + zCount := by simp
    _ < 256 := by omega

theorem aNonSeymour_unaugmented_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzLe : zCount ≤ 2) :
    aNonSeymour 1 zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [aNonSeymour, all_eq_true_iff]
  intro a ha
  simp only [qAnonymousLower, BitVec.ult_eq_decide, decide_eq_true_eq]
  norm_num
  have hz : (0 : BitVec 8).toNat = 0 := by decide
  rw [hz, Nat.add_zero, Nat.mod_eq_of_lt
    (projectedSecondCount_toNat_lt_256 hzLe _ _ _),
    aDegree_toNat G C L hG a ha]
  have h := projectedNonSeymour_unaugmented G C L hG hNoSeymour hzLe a (by omega)
  simpa [labelledVertex, ha] using h

theorem pNonSeymour_unaugmented_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hzLe : zCount ≤ 2) :
    pNonSeymour 1 zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [pNonSeymour, all_eq_true_iff]
  intro p hp
  simp only [qAnonymousLower, BitVec.ult_eq_decide, decide_eq_true_eq]
  norm_num
  have hz : (0 : BitVec 8).toNat = 0 := by decide
  rw [hz, Nat.add_zero, Nat.mod_eq_of_lt
    (projectedSecondCount_toNat_lt_256 hzLe _ _ _),
    pDegree_toNat G C L hG hHCard hzLe p hp]
  have h := projectedNonSeymour_unaugmented G C L hG hNoSeymour hzLe
    (8 + p) (by omega)
  simpa [labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 13 by omega] using h

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Assembly
