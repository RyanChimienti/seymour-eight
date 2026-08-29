import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.Encoding
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.GraphFacts

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.GraphFacts

open Shared Shared.FiniteCore Labels Encoding Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def hLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7) :
    Fin 7 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 7 → {v : V // v ∈ C.H} := fun i ↦
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, by
      by_cases hi : i.val < 3
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi⟩)
      · apply Finset.mem_union_right C.A1
        have heq : (⟨i.val + 1, by omega⟩ : Fin 8) =
            ⟨(i.val - 3) + 4, by omega⟩ := Fin.ext (by simp; omega)
        rw [heq]
        exact L.a_x ⟨i.val - 3, by omega⟩⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := Fin.ext_iff.mp ha
    simp only at hval
    omega
  · simpa using hHCard.symm

@[simp] theorem hLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7) (i : Fin 7) :
    (hLabelEquiv G C L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := by
  simp [hLabelEquiv]

noncomputable def aOneLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) :
    Fin 3 ≃ {v : V // v ∈ C.A1} := by
  let f : Fin 3 → {v : V // v ∈ C.A1} := fun i ↦
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, L.a_aOne i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := Fin.ext_iff.mp ha
    simp only at hval
    omega
  · simpa using hA1Card.symm

@[simp] theorem aOneLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) (i : Fin 3) :
    (aOneLabelEquiv G C L hA1Card i).1 =
      (L.a ⟨i.val + 1, by omega⟩).1 := by
  simp [aOneLabelEquiv]

noncomputable def xLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 4) :
    Fin 4 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 4 → {v : V // v ∈ C.X} := fun i ↦
    ⟨(L.a ⟨i.val + 4, by omega⟩).1, L.a_x i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 4, by omega⟩ : Fin 8) =
        ⟨j.val + 4, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := Fin.ext_iff.mp ha
    simp only at hval
    omega
  · simpa using hXCard.symm

@[simp] theorem xLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 4) (i : Fin 4) :
    (xLabelEquiv G C L hXCard i).1 =
      (L.a ⟨i.val + 4, by omega⟩).1 := by
  simp [xLabelEquiv]

theorem aOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 8) :
    (aOut (graphArc G L) source).toNat =
      directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  rw [aArc_graph G L source j hs j.isLt]
  simp

theorem aPOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 8) :
    (aPOut (graphArc G L) source).toNat =
      directCount G C.P (L.a ⟨source, hs⟩).1 := by
  rw [aPOut, toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [aToP_graph G L source j hs j.isLt]
  simp

theorem aQOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 8) :
    (aQOut (graphArc G L) source).toNat =
      directCount G C.Q (L.a ⟨source, hs⟩).1 := by
  rw [aQOut, toNat_count_eq_fin_sum 2 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.Q L.q _
  intro j
  rw [aToQ_graph G L source j hs j.isLt]
  simp

theorem aBOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 8) :
    (aBOut (graphArc G L) source).toNat =
      directCount G C.B (L.a ⟨source, hs⟩).1 := by
  rw [aBOut, BitVec.toNat_add, aPOut_toNat G C L source hs,
    aQOut_toNat G C L source hs]
  have hDis := Digraph.LocalConfiguration.disjoint_P_Q (G := G) C
  have hP : directCount G C.P (L.a ⟨source, hs⟩).1 ≤ 5 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.p).symm)
  have hQ : directCount G C.Q (L.a ⟨source, hs⟩).1 ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.q).symm)
  rw [Nat.mod_eq_of_lt (by omega),
    ← directCount_union_of_disjoint G C.P C.Q _ hDis,
    Digraph.LocalConfiguration.P_union_Q]

theorem pBlockCounts {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7)
    (hzSmall : zCount < 256) (p : Nat) (hp : p < 5) :
    (pOut (graphArc G L) p).toNat = directCount G C.P (L.p ⟨p, hp⟩).1 ∧
    (pHOut (graphArc G L) p).toNat = directCount G C.H (L.p ⟨p, hp⟩).1 ∧
    (pQOut (graphArc G L) p).toNat = directCount G C.Q (L.p ⟨p, hp⟩).1 ∧
    (pZOut zCount (graphPToZ G L) p).toNat =
      directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
  constructor
  · rw [pOut, toNat_count_eq_fin_sum 5 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P L.p _
    intro j
    rw [pArc_graph G L p j hp j.isLt]
    simp
  constructor
  · rw [pHOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H (hLabelEquiv G C L hHCard) _
    intro j
    rw [hLabelEquiv_val, pToA_graph G L p (1 + j) hp (by omega)]
    simp [Nat.add_comm]
  constructor
  · rw [pQOut, toNat_count_eq_fin_sum 2 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Q L.q _
    intro j
    rw [pToQ_graph G L p j hp j.isLt]
    simp
  · rw [pZOut, toNat_count_eq_fin_sum zCount _ hzSmall]
    symm
    apply directCount_eq_sum_bool G (externalTargets G C) L.z _
    intro j
    rw [pToZ_graph G L p j hp j.isLt]
    simp

theorem hPOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (h : Nat) (hh : h < 7) :
    (hPOut (graphArc G L) h).toNat =
      directCount G C.P (L.a ⟨h + 1, by omega⟩).1 := by
  rw [hPOut, toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [aToP_graph G L (1 + h) j (by omega) j.isLt]
  simp [Nat.add_comm]

def labelledVertex {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 13 then (L.p ⟨n - 8, by omega⟩).1
  else if hnQ : n < 15 then (L.q ⟨n - 13, by omega⟩).1
  else if hnZ : n < 15 + zCount then (L.z ⟨n - 15, by omega⟩).1
  else C.s

def retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  C.A ∪ C.P ∪ C.Q ∪ externalTargets G C

noncomputable def retainedLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    Fin (15 + zCount) ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin (15 + zCount) → {v : V // v ∈ retainedVertexSet G C} := fun i ↦
    if hiA : i.val < 8 then ⟨(L.a ⟨i, hiA⟩).1, by simp [retainedVertexSet, (L.a _).2]⟩
    else if hiP : i.val < 13 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1, by simp [retainedVertexSet, (L.p _).2]⟩
    else if hiQ : i.val < 15 then
      ⟨(L.q ⟨i.val - 13, by omega⟩).1, by simp [retainedVertexSet, (L.q _).2]⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1, by simp [retainedVertexSet, (L.z _).2]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    simp only [retainedVertexSet, Finset.mem_union] at hv
    rcases hv with ((hvA | hvP) | hvQ) | hvZ
    · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
      refine ⟨⟨i, by omega⟩, Subtype.ext ?_⟩
      simpa [f, i.isLt] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
      refine ⟨⟨i.val + 8, by omega⟩, Subtype.ext ?_⟩
      simpa [f, show ¬i.val + 8 < 8 by omega, show i.val + 8 < 13 by omega]
        using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hvQ⟩
      refine ⟨⟨i.val + 13, by omega⟩, Subtype.ext ?_⟩
      simpa [f, show ¬i.val + 13 < 8 by omega,
        show ¬i.val + 13 < 13 by omega, show i.val + 13 < 15 by omega]
        using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, Subtype.ext ?_⟩
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 13 by omega, show ¬i.val + 15 < 15 by omega]
        using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := Finset.disjoint_of_subset_right
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)
    have hAPQ : Disjoint (C.A ∪ C.P) C.Q := by
      rw [Finset.disjoint_left]
      intro v hv hvQ
      rcases Finset.mem_union.mp hv with hvA | hvP
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hvQ
    have hAPQZ : Disjoint (C.A ∪ C.P ∪ C.Q) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hv hvZ
      rcases Finset.mem_union.mp hv with hvAP | hvQ
      · rcases Finset.mem_union.mp hvAP with hvA | hvP
        · exact SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.external_not_mem_A
            G C hG v hvZ hvA
        · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvZ
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvZ
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp, retainedVertexSet,
      Finset.card_union_of_disjoint hAPQZ, Finset.card_union_of_disjoint hAPQ,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
    have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
    have hz : (externalTargets G C).card = zCount := by
      simpa using (Fintype.card_congr L.z).symm
    simp [ha, hp, hq, hz]

@[simp] theorem retainedLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (i : Fin (15 + zCount)) :
    (retainedLabelEquiv G C L hG i).1 = labelledVertex G L i := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 13
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  by_cases hiQ : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, hiQ]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, hiQ, i.isLt]

theorem coreArc_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 13) (ht : target < 15 + zCount) :
    coreArc zCount (graphArc G L) (graphPToZ G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  by_cases hsA : source < 8
  · by_cases htA : target < 8
    · simp [coreArc, graphArc, labelledVertex, hsA, htA, show target < 15 by omega]
    by_cases htP : target < 13
    · simp [coreArc, graphArc, labelledVertex, hsA, htA, htP,
        show target < 15 by omega]
    by_cases htQ : target < 15
    · simp [coreArc, graphArc, labelledVertex, hsA, htA, htP, htQ]
    · have hn := SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.A_not_adj_external
          G C hG (L.a ⟨source, hsA⟩).1 (L.z ⟨target - 15, by omega⟩).1
          (L.a _).2 (L.z _).2
      simp [coreArc, labelledVertex, hsA, htA, htP, htQ, ht, hn]
  · have hsP : source < 13 := hs
    by_cases htA : target < 8
    · simp [coreArc, graphArc, labelledVertex, hsA, hsP, htA,
        show target < 15 by omega]
    by_cases htP : target < 13
    · simp [coreArc, graphArc, labelledVertex, hsA, hsP, htA, htP,
        show target < 15 by omega]
    by_cases htQ : target < 15
    · simp [coreArc, graphArc, labelledVertex, hsA, hsP, htA, htP, htQ]
    · simp [coreArc, graphPToZ, labelledVertex, hsA, hsP, htA,
        htP, htQ, ht, show source - 8 < 5 by omega,
        show target - 15 < zCount by omega]

theorem projectedSecondCount_le_retained_second_card {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C) (hG : G.IsOriented)
    (hzSmall : 15 + zCount < 256) (source : Nat) (hs : source < 13) :
    (projectedSecondCount zCount (graphArc G L) (graphPToZ G L) source).toNat ≤
      ((retainedVertexSet G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (labelledVertex G L source)).card := by
  have hGood : ∀ j : Fin (15 + zCount),
      projectedSecond zCount (graphArc G L) (graphPToZ G L) source j = true →
        (retainedLabelEquiv G C L hG j).1 ∈
          G.secondOutNeighborFinset (labelledVertex G L source) := by
    intro j hj
    simp only [projectedSecond, Bool.and_eq_true, decide_eq_true_eq] at hj
    rcases hj with ⟨⟨hne, hNot⟩, hReach⟩
    obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
    rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
    have hmSource : middle < 13 := by
      by_contra hn
      have hFalse : coreArc zCount (graphArc G L) (graphPToZ G L)
          middle j = false := by
        simp [coreArc, show ¬middle < 8 by omega, hn]
      rw [hFalse] at hLast
      simp at hLast
    rw [coreArc_graph G C L hG source middle hs (by omega)] at hFirst
    rw [coreArc_graph G C L hG middle j hmSource j.isLt] at hLast
    rw [coreArc_graph G C L hG source j hs j.isLt] at hNot
    have hneV : labelledVertex G L j ≠ labelledVertex G L source := by
      intro heq
      have hFin : j = ⟨source, by omega⟩ := by
        apply (retainedLabelEquiv G C L hG).injective
        apply Subtype.ext
        simpa using heq
      exact hne (Fin.ext_iff.mp hFin)
    rw [retainedLabelEquiv_val, Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
      by simpa using hNot, hneV⟩
  have hFiltered :=
    SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.count_le_filterCard
      (V := V) (retainedVertexSet G C) (retainedLabelEquiv G C L hG)
      (projectedSecond zCount (graphArc G L) (graphPToZ G L) source)
      (fun v ↦ v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
      hzSmall hGood
  exact hFiltered

theorem projectedSecondCount_le_graph_retained {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C) (hG : G.IsOriented)
    (hzSmall : 15 + zCount < 256) (source : Nat) (hs : source < 13) :
    (projectedSecondCount zCount (graphArc G L) (graphPToZ G L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  have hFiltered := projectedSecondCount_le_retained_second_card G C L hG
    hzSmall source hs
  unfold Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (fun _ hv ↦ (Finset.mem_filter.mp hv).2))

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.GraphFacts
