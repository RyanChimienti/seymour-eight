import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.GraphFacts
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Derived
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.GraphBridge
import SeymourEight.Cases.BSevenKThree.Counting
import SeymourEight.Shared.InnerDegreeThree

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Assembly

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
    have hzero : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      have hfin : (⟨0, by omega⟩ : Fin 8) = 0 := Fin.ext (by simp)
      rw [hfin]
      exact L.a_zero
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
  · by_cases hjP : j < 14
    · have hjp : j - 8 < 6 := by omega
      have hadj : G.Adj C.a1 (L.p ⟨j - 8, hjp⟩).1 :=
        (Finset.mem_filter.mp (L.p ⟨j - 8, hjp⟩).2).2
      simp [graphArc, L.a_zero, hjA, hjP, hadj,
        show 8 ≤ j by omega]
    · have hjQ : j = 14 := by omega
      have hn : ¬G.Adj C.a1 (L.q 0).1 := by
        intro ha
        exact (Finset.mem_sdiff.mp (L.q 0).2).2
          (Finset.mem_filter.mpr ⟨
            Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2, ha⟩)
      simp [graphArc, L.a_zero, hjQ, hn]

theorem noPToAOne_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    noPToAOne (graphArc G L) = true := by
  rw [noPToAOne, all_eq_true_iff]
  intro p hp
  rw [pToA_graph G L p 0 hp (by omega)]
  have hzero : (L.a ⟨0, by omega⟩).1 = C.a1 := by
    have hfin : (⟨0, by omega⟩ : Fin 8) = 0 := Fin.ext (by simp)
    rw [hfin]
    exact L.a_zero
  rw [hzero]
  have ha : G.Adj C.a1 (L.p ⟨p, hp⟩).1 :=
    (Finset.mem_filter.mp (L.p ⟨p, hp⟩).2).2
  simp [hG.2 ha]

theorem qInB_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : qInB (graphArc G L) = true := by
  rw [qInB, any_eq_true_iff]
  have hqB := Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2
  rw [Digraph.LocalConfiguration.B, Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet] at hqB
  rcases hqB.1 with ⟨a, hsa, haq⟩
  have haA : a ∈ C.A := (Digraph.mem_outNeighborFinset (G := G)).mpr hsa
  obtain ⟨i, hi⟩ := L.a.surjective ⟨a, haA⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [aToQ_graph G L i i.isLt]
  simpa [congrArg Subtype.val hi] using haq

theorem everyXReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) :
    everyXReached (graphArc G L) = true := by
  rw [everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := (aOneLabelEquiv G C L hA1Card).surjective ⟨u, huA1⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [aArc_graph G L (1 + i) (4 + x) (by omega) (by omega)]
    have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := by
      simpa [aOneLabelEquiv] using congrArg Subtype.val hi
    have hSource : (⟨1 + i.val, by omega⟩ : Fin 8) = ⟨i.val + 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    have hTarget : (⟨4 + x, by omega⟩ : Fin 8) = ⟨x + 4, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [hSource, hiVal, hTarget]
    exact decide_eq_true hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [pToA_graph G L i (4 + x) i.isLt (by omega)]
    have hiVal : (L.p i).1 = u := congrArg Subtype.val hi
    have hTarget : (⟨4 + x, by omega⟩ : Fin 8) = ⟨x + 4, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [hiVal, hTarget]
    exact decide_eq_true hux

theorem everyZReached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : everyZReached zCount (graphPToZ G L) = true := by
  rw [everyZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  obtain ⟨p, hp, hpz⟩ : ∃ p ∈ C.P, G.Adj p (L.z ⟨z, hz⟩).1 := by
    rcases Finset.mem_union.mp (L.z ⟨z, hz⟩).2 with hvZ | hvRoot
    · have hReach := (Finset.mem_sdiff.mp hvZ).1
      exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReach
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
    (L : Labels G zCount C) (_hzLe : zCount ≤ 4) :
    inactiveZZero zCount (graphPToZ G L) = true := by
  rw [inactiveZZero, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro j hj
  simp [graphPToZ, hp]

theorem qReachStatus_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3)
    (yValue : Nat) (hy : BSevenKThree.y G C = yValue)
    (hyCases : yValue = 0 ∨ yValue = 1) :
    qReachStatus yValue (graphArc G L) = true := by
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro q hq
    obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hq⟩
    have hi0 : i = 0 := Subsingleton.elim _ _
    simpa [hi0] using congrArg Subtype.val hi.symm
  rcases hyCases with rfl | rfl
  · have hEmpty : reachedQ G C = ∅ := Finset.card_eq_zero.mp hy
    have hnA (i : Fin 3) : ¬G.Adj (L.a ⟨i.val + 1, by omega⟩).1 (L.q 0).1 := by
      intro ha
      have : (L.q 0).1 ∈ reachedQ G C := Finset.mem_inter.mpr ⟨(L.q 0).2,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨_, Finset.mem_union_left C.P (L.a_aOne i), ha⟩⟩
      simp [hEmpty] at this
    have hnP (i : Fin 6) : ¬G.Adj (L.p i).1 (L.q 0).1 := by
      intro ha
      have : (L.q 0).1 ∈ reachedQ G C := Finset.mem_inter.mpr ⟨(L.q 0).2,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨_, Finset.mem_union_right C.A1 (L.p i).2, ha⟩⟩
      simp [hEmpty] at this
    have hAnyA : any 3 (fun a ↦ aToQ (graphArc G L) (1 + a)) = false := by
      cases h : any 3 (fun a ↦ aToQ (graphArc G L) (1 + a)) with
      | false => rfl
      | true =>
          obtain ⟨i, hi, hAdj⟩ := (any_eq_true_iff 3 _).mp h
          rw [aToQ_graph G L (1 + i) (by omega)] at hAdj
          have hSource : (⟨1 + i, by omega⟩ : Fin 8) =
              ⟨(⟨i, hi⟩ : Fin 3).val + 1, by omega⟩ := Fin.ext (by simp; omega)
          exact False.elim ((hnA ⟨i, hi⟩)
            (by simpa [hSource] using of_decide_eq_true hAdj))
    have hAnyP : any 6 (pToQ (graphArc G L)) = false := by
      cases h : any 6 (pToQ (graphArc G L)) with
      | false => rfl
      | true =>
          obtain ⟨i, hi, hAdj⟩ := (any_eq_true_iff 6 _).mp h
          rw [pToQ_graph G L i hi] at hAdj
          exact (hnP ⟨i, hi⟩) (of_decide_eq_true hAdj) |> False.elim
    simp [qReachStatus, hAnyA, hAnyP]
  · have hMem : (L.q 0).1 ∈ reachedQ G C := by
      have hSub : reachedQ G C ⊆ C.Q := Finset.inter_subset_left
      have hReachedCard : (reachedQ G C).card = 1 := by
        simpa [BSevenKThree.y] using hy
      have hQCard : C.Q.card = 1 := by
        simpa using (Fintype.card_congr L.q).symm
      have hEq : reachedQ G C = C.Q :=
        Finset.eq_of_subset_of_card_le hSub (by omega)
      rw [hEq]
      exact (L.q 0).2
    rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_inter.mp hMem).2 with ⟨u, hu, huq⟩
    rcases Finset.mem_union.mp hu with huA | huP
    · obtain ⟨i, hi⟩ := (aOneLabelEquiv G C L hA1Card).surjective ⟨u, huA⟩
      have hAny : any 3 (fun a ↦ aToQ (graphArc G L) (1 + a)) = true := by
        rw [any_eq_true_iff]
        refine ⟨i, i.isLt, ?_⟩
        rw [aToQ_graph G L (1 + i) (by omega)]
        have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := by
          simpa [aOneLabelEquiv] using congrArg Subtype.val hi
        have hSource : (⟨1 + i.val, by omega⟩ : Fin 8) =
            ⟨i.val + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hSource, hiVal]
        exact decide_eq_true huq
      simp [qReachStatus, hAny]
    · obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
      have hAny : any 6 (pToQ (graphArc G L)) = true := by
        rw [any_eq_true_iff]
        refine ⟨i, i.isLt, ?_⟩
        rw [pToQ_graph G L i i.isLt]
        simpa [congrArg Subtype.val hi] using huq
      simp [qReachStatus, hAny]

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

theorem aConditions_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hr : C.r = 6) : aConditions (graphArc G L) = true := by
  rw [aConditions, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L a ha
  have hBO := aBOut_toNat G C L a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 3 ≤ (aOut (graphArc G L) a).toNat := by
    rw [hAO]
    simpa [hk, directCount, CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut (graphArc G L) a).toNat = 3 →
      6 ≤ (aBOut (graphArc G L) a).toNat := by
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
      have hBLe : (aBOut (graphArc G L) a).toNat ≤ 8 := by
        rw [hBO]
        have hCard : C.B.card = 7 := by
          rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C, hr]
          have : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
          omega
        have hLe := Finset.card_le_card
          (Finset.filter_subset (G.Adj (L.a ⟨a, ha⟩).1) C.B)
        have hSeven :
            (C.B.filter (G.Adj (L.a ⟨a, ha⟩).1)).card ≤ 7 := hLe.trans hCard.le
        change (C.B.filter (G.Adj (L.a ⟨a, ha⟩).1)).card ≤ 8
        omega
      omega

theorem qSingleton {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : C.Q = {(L.q 0).1} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(L.q 0).2, ?_⟩
  intro q hq
  obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hq⟩
  have hi0 : i = 0 := Subsingleton.elim _ _
  simpa [hi0] using congrArg Subtype.val hi.symm

theorem pAuxOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (yValue : Nat)
    (hy : BSevenKThree.y G C = yValue) (hyCases : yValue = 0 ∨ yValue = 1)
    (hzLe : zCount ≤ 4) (p : Nat) (hp : p < 6) :
    (pAuxOut yValue zCount (graphArc G L) (graphPToZ G L) p).toNat =
      directCount G ({(L.q 0).1} ∪ (externalTargets G C)) (L.p ⟨p, hp⟩).1 := by
  have hZ := (pBlockCounts G C L hG hHCard (by omega) p hp).2.2
  have hDis : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
  have hQCount : (bitCount (pToQ (graphArc G L) p)).toNat =
      directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 := by
    rw [pToQ_graph G L p hp]
    by_cases h : G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 <;>
      simp [bitCount, directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, h]
  rw [pAuxOut, BitVec.toNat_add, hZ]
  rcases hyCases with rfl | rfl
  · have hEmpty : reachedQ G C = ∅ := Finset.card_eq_zero.mp hy
    have hn : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 := by
      intro ha
      have hm : (L.q 0).1 ∈ reachedQ G C := Finset.mem_inter.mpr ⟨(L.q 0).2,
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨_, Finset.mem_union_right C.A1 (L.p _).2, ha⟩⟩
      simp [hEmpty] at hm
    have hZero : directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 = 0 := by
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hn]
    rw [if_pos rfl]
    have hZSmall : directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 < 256 := by
      have hLe := Finset.card_le_card
        (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
      change directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card at hLe
      have hzCard : (externalTargets G C).card = zCount := by
        simpa using (Fintype.card_congr L.z).symm
      omega
    change (directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 + 0) % 256 =
      directCount G ({(L.q 0).1} ∪ (externalTargets G C)) (L.p ⟨p, hp⟩).1
    rw [Nat.add_zero, Nat.mod_eq_of_lt hZSmall]
    rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hDis, hZero,
      Nat.zero_add]
  · rw [if_neg (by omega), hQCount]
    have hSmall : directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 +
        directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 < 256 := by
      have hz := Finset.card_le_card
        (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) (externalTargets G C))
      have hq := Finset.card_le_card
        (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1)
          ({(L.q 0).1} : Finset V))
      change directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card at hz
      change directCount G {(L.q 0).1} (L.p ⟨p, hp⟩).1 ≤
        ({(L.q 0).1} : Finset V).card at hq
      have hzCard : (externalTargets G C).card = zCount := by
        simpa using (Fintype.card_congr L.z).symm
      simp only [Finset.card_singleton] at hq
      omega
    rw [Nat.mod_eq_of_lt hSmall, Nat.add_comm,
      directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hDis]

theorem pConditions_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (yValue : Nat) (hy : BSevenKThree.y G C = yValue)
    (hyCases : yValue = 0 ∨ yValue = 1) (hzLe : zCount ≤ 4) :
    pConditions yValue zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [pConditions, all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C L hG hHCard (by omega) p hp
  have hAux := pAuxOut_toNat G C L hG hHCard yValue hy hyCases (by omega) p hp
  have hQ := qSingleton G C L
  have hDegree :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG (L.p ⟨p, hp⟩).1 (L.p _).2
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pDegree, BitVec.toNat_add, BitVec.toNat_add, hBlocks.1, hBlocks.2.1, hAux]
  have hSmall : directCount G C.P (L.p ⟨p, hp⟩).1 +
      directCount G C.H (L.p ⟨p, hp⟩).1 +
        directCount G ({(L.q 0).1} ∪ (externalTargets G C)) (L.p ⟨p, hp⟩).1 < 256 := by
    have hP : directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 6 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simpa using (Fintype.card_congr L.p).symm)
    have hH : directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hE : directCount G ({(L.q 0).1} ∪ (externalTargets G C)) (L.p ⟨p, hp⟩).1 ≤
        1 + zCount := by
      apply (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      have hqz : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
        rw [Finset.disjoint_left]
        intro v hvQ hvZ
        have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
        subst v
        exact (Finset.disjoint_left.mp
          (BSixKThree.disjoint_B_externalTargets G C))
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
      rw [Finset.card_union_of_disjoint hqz]
      have hzCard : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
      simp [hzCard]
    omega
  have hPH : directCount G C.P (L.p ⟨p, hp⟩).1 +
      directCount G C.H (L.p ⟨p, hp⟩).1 < 256 := by
    omega
  rw [Nat.mod_eq_of_lt hPH, Nat.mod_eq_of_lt hSmall]
  rw [← hDegree]
  exact hMin _

theorem aNonSeymour_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzSmall : 15 + zCount < 256) :
    aNonSeymour zCount (graphArc G L) (graphPToZ G L) = true := by
  rw [aNonSeymour, all_eq_true_iff]
  intro a ha
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSecond := projectedSecondCount_le_graph G C L hG hzSmall a ha
  have hDegree := A_outdegree_eq_blocks G C L hG a ha
  have hAO := aOut_toNat G C L a ha
  have hBO := aBOut_toNat G C L a ha
  have hDirect : (aDegree (graphArc G L) a).toNat =
      G.outdegree (L.a ⟨a, ha⟩).1 := by
    rw [aDegree, BitVec.toNat_add, hAO, hBO, hDegree]
    have hSmall : directCount G C.A (L.a ⟨a, ha⟩).1 +
        directCount G C.B (L.a ⟨a, ha⟩).1 < 256 := by
      have hA : directCount G C.A (L.a ⟨a, ha⟩).1 ≤ 8 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (by simpa using (Fintype.card_congr L.a).symm)
      have hB : directCount G C.B (L.a ⟨a, ha⟩).1 ≤ 7 := by
        apply (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
        have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
        have hq : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
        have hr : C.r = 6 := by simpa [Digraph.LocalConfiguration.r] using hp
        omega
      omega
    rw [Nat.mod_eq_of_lt hSmall]
  rw [hDirect]
  exact hSecond.trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨_, h⟩))

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

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Assembly
