import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.Encoding
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.BooleanBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts

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
            ⟨(i.val - 3) + 4, by omega⟩ := by
          apply Fin.ext
          simp
          omega
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
    have hval : i.val + 1 = j.val + 1 := Fin.ext_iff.mp ha
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
    have hval := congrArg Fin.val ha
    simp at hval
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
  rw [aPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [aToP_graph G L source j hs j.isLt]
  simp

theorem aBOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 8) :
    (aBOut (graphArc G L) source).toNat =
      directCount G C.B (L.a ⟨source, hs⟩).1 := by
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro q hq
    obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hq⟩
    have : i = 0 := Subsingleton.elim _ _
    simpa [this] using congrArg Subtype.val hi.symm
  rw [aBOut, BitVec.toNat_add, aPOut_toNat G C L source hs]
  have hBit : (bitCount (aToQ (graphArc G L) source)).toNat =
      directCount G {(L.q 0).1} (L.a ⟨source, hs⟩).1 := by
    rw [aToQ_graph G L source hs]
    by_cases h : G.Adj (L.a ⟨source, hs⟩).1 (L.q 0).1 <;>
      simp [bitCount, directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, h]
  rw [hBit]
  have hDis : Disjoint C.P {(L.q 0).1} := by
    rw [Finset.disjoint_left]
    intro v hvP hvQ
    have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
    subst v
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP (L.q 0).2
  have hSmall : directCount G C.P (L.a ⟨source, hs⟩).1 +
      directCount G {(L.q 0).1} (L.a ⟨source, hs⟩).1 < 256 := by
    have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have h1 : directCount G C.P (L.a ⟨source, hs⟩).1 ≤ 6 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hp
    have h2 : directCount G {(L.q 0).1} (L.a ⟨source, hs⟩).1 ≤
        1 := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
    omega
  rw [Nat.mod_eq_of_lt hSmall,
    ← directCount_union_of_disjoint G C.P {(L.q 0).1} _ hDis,
    ← hQ, Digraph.LocalConfiguration.P_union_Q]

theorem pBlockCounts {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (_hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hzSmall : zCount < 256) (p : Nat) (hp : p < 6) :
    (pOut (graphArc G L) p).toNat = directCount G C.P (L.p ⟨p, hp⟩).1 ∧
    (pHOut (graphArc G L) p).toNat = directCount G C.H (L.p ⟨p, hp⟩).1 ∧
    (pZOut zCount (graphPToZ G L) p).toNat =
      directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
  constructor
  · rw [pOut, toNat_count_eq_fin_sum 6 _ (by omega)]
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
  · rw [pZOut, toNat_count_eq_fin_sum zCount _ hzSmall]
    symm
    apply directCount_eq_sum_bool G (externalTargets G C) L.z _
    intro j
    rw [pToZ_graph G L p j hp j.isLt]
    simp only [decide_eq_true_eq]

theorem hPOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (h : Nat) (hh : h < 7) :
    (hPOut (graphArc G L) h).toNat =
      directCount G C.P (L.a ⟨h + 1, by omega⟩).1 := by
  rw [hPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [aToP_graph G L (1 + h) j (by omega) j.isLt]
  simp [Nat.add_comm]

def labelledVertex {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 14 then (L.p ⟨n - 8, by omega⟩).1
  else if hnQ : n = 14 then (L.q 0).1
  else if hnZ : n < 15 + zCount then (L.z ⟨n - 15, by omega⟩).1
  else C.s

def retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  C.A ∪ C.P ∪ C.Q ∪ (externalTargets G C)

theorem A_not_adj_external (C : G.LocalConfiguration) (hG : G.IsOriented)
    (u v : V) (hu : u ∈ C.A) (hv : v ∈ externalTargets G C) : ¬G.Adj u v := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · exact
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
        G C hG u v hu hvZ
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by
        simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      intro hus
      have hsu : G.Adj C.s u :=
        (Digraph.mem_outNeighborFinset (G := G)).mp hu
      exact hG.2 hsu hus
    · simp [rootSecondFinset, hReach] at hvRoot

theorem external_not_mem_A (C : G.LocalConfiguration) (hG : G.IsOriented)
    (v : V) (hv : v ∈ externalTargets G C) : v ∉ C.A := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · intro hvA
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
        (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by
        simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
    · simp [rootSecondFinset, hReach] at hvRoot

noncomputable def retainedLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    Fin (15 + zCount) ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin (15 + zCount) → {v : V // v ∈ retainedVertexSet G C} := fun i ↦
    if hiA : i.val < 8 then ⟨(L.a ⟨i, hiA⟩).1, by simp [retainedVertexSet, (L.a _).2]⟩
    else if hiP : i.val < 14 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1, by simp [retainedVertexSet, (L.p _).2]⟩
    else if hiQ : i.val = 14 then
      ⟨(L.q 0).1, by simp [retainedVertexSet, (L.q 0).2]⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1, by simp [retainedVertexSet, (L.z _).2]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    simp only [retainedVertexSet, Finset.mem_union] at hv
    rcases hv with ((hvA | hvP) | hvQ) | hvZ
    · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
      refine ⟨⟨i, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, i.isLt] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
      refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 8 < 8 by omega,
        show i.val + 8 < 14 by omega] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hvQ⟩
      refine ⟨⟨14, by omega⟩, ?_⟩
      apply Subtype.ext
      have hi0 : i = 0 := Subsingleton.elim _ _
      simpa [f, hi0] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 14 by omega,
        show i.val + 15 ≠ 14 by omega] using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := by
      exact Finset.disjoint_of_subset_right
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
        · exact external_not_mem_A G C hG v hvZ hvA
        · exact (Finset.disjoint_left.mp
            (BSixKThree.disjoint_B_externalTargets G C))
              (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvZ
      · exact (Finset.disjoint_left.mp
          (BSixKThree.disjoint_B_externalTargets G C))
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvZ
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp, retainedVertexSet,
      Finset.card_union_of_disjoint hAPQZ,
      Finset.card_union_of_disjoint hAPQ,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have hq : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
    have hz : (externalTargets G C).card = zCount := by simpa using (Fintype.card_congr L.z).symm
    simp [ha, hp, hq, hz]

@[simp] theorem retainedLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (i : Fin (15 + zCount)) :
    (retainedLabelEquiv G C L hG i).1 = labelledVertex G L i := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 14
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  by_cases hiQ : i.val = 14
  · simp [retainedLabelEquiv, labelledVertex, hiQ]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, hiQ, i.isLt]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (count n b).toNat ≤ (S.filter Q).card := by
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · simp [hb, hGood j hb]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

theorem coreArc_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 14) (ht : target < 15 + zCount) :
    coreArc zCount (graphArc G L) (graphPToZ G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  by_cases hsA : source < 8
  · by_cases htA : target < 8
    · have ht15 : target < 15 := by omega
      simp [coreArc, graphArc, labelledVertex, hsA, htA, ht15]
    by_cases htP : target < 14
    · have ht15 : target < 15 := by omega
      simp [coreArc, graphArc, labelledVertex, hsA, htA, htP, ht15]
    by_cases htQ : target = 14
    · have ht15 : target < 15 := by omega
      simp [coreArc, graphArc, labelledVertex, hsA, htQ]
    · have htZ : 15 ≤ target := by omega
      have hn : ¬G.Adj (L.a ⟨source, hsA⟩).1
          (L.z ⟨target - 15, by omega⟩).1 :=
        A_not_adj_external G C hG _ _ (L.a _).2 (L.z _).2
      simp [coreArc, graphArc, labelledVertex, hsA, htA, htP, htQ, ht, hn]
  · have hsP : source < 14 := hs
    by_cases htA : target < 8
    · have ht15 : target < 15 := by omega
      simp [coreArc, graphArc, labelledVertex, hsA, hsP, htA, ht15]
    by_cases htP : target < 14
    · have ht15 : target < 15 := by omega
      simp [coreArc, graphArc, labelledVertex, hsA, hsP, htA, htP, ht15]
    by_cases htQ : target = 14
    · have ht15 : target < 15 := by omega
      simp [coreArc, graphArc, labelledVertex, hsA, hsP, htQ]
    · have htZ : 15 ≤ target := by omega
      have hpIndex : source - 8 < 6 := by omega
      have hzIndex : target - 15 < zCount := by omega
      simp [coreArc, graphPToZ, labelledVertex, hsA, hsP,
        htA, htP, htQ, ht, show ¬target < 15 by omega,
        hpIndex, hzIndex]

theorem projectedSecond_true_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 14) (ht : target < 15 + zCount)
    (hSecond : projectedSecond zCount (graphArc G L) (graphPToZ G L)
      source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  simp only [projectedSecond, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_graph G C L hG source middle (by omega) (by omega)] at hFirst
  by_cases hmQ : middle = 14
  · subst middle
    simp [coreArc] at hLast
  have hm' : middle < 14 := by omega
  rw [coreArc_graph G C L hG middle target hm' ht] at hLast
  rw [coreArc_graph G C L hG source target (by omega) ht] at hNotArc
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin (15 + zCount)) = ⟨source, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa using heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

theorem projectedSecondCount_le_graph_retained {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C) (hG : G.IsOriented)
    (hzSmall : 15 + zCount < 256) (source : Nat) (hs : source < 14) :
    (projectedSecondCount zCount (graphArc G L) (graphPToZ G L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  have hFiltered := count_le_filterCard (V := V) (retainedVertexSet G C)
    (retainedLabelEquiv G C L hG)
    (projectedSecond zCount (graphArc G L) (graphPToZ G L) source)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    hzSmall (by
      intro j hj
      rw [retainedLabelEquiv_val]
      exact projectedSecond_true_mem G C L hG source j hs j.isLt hj)
  unfold projectedSecondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

theorem projectedSecondCount_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzSmall : 15 + zCount < 256)
    (source : Nat) (hs : source < 8) :
    (projectedSecondCount zCount (graphArc G L) (graphPToZ G L) source).toNat ≤
      G.secondOutdegree (L.a ⟨source, hs⟩).1 := by
  have h := projectedSecondCount_le_graph_retained G C L hG hzSmall source
    (by omega)
  simpa [labelledVertex, hs] using h

theorem pStrictSecond_true_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (p r : Nat)
    (hp : p < 6) (hr : r < 6)
    (hSecond : strictSecondLocal (graphArc G L) (8 + p) (8 + r) = true) :
    (L.p ⟨r, hr⟩).1 ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1 := by
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 14 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  have hpA : ¬8 + p < 8 := by omega
  have hpP : 8 + p < 14 := by omega
  have hrA : ¬8 + r < 8 := by omega
  have hrP : 8 + r < 14 := by omega
  have hr15 : 8 + r < 15 := by omega
  have hm15 : middle < 15 := by omega
  have hFirst' : decide (G.Adj (labelledVertex G L (8 + p))
      (labelledVertex G L middle)) = true := by
    rw [← coreArc_graph G C L hG (8 + p) middle (by omega) (by omega)]
    simpa [coreArc, hpA, hpP, hm15] using hFirst
  have hLast' : decide (G.Adj (labelledVertex G L middle)
      (labelledVertex G L (8 + r))) = true := by
    rw [← coreArc_graph G C L hG middle (8 + r) (by omega) (by omega)]
    by_cases hmA : middle < 8
    · simpa [coreArc, hmA, hr15] using hLast
    · have hmP : middle < 14 := by omega
      simpa [coreArc, hmA, hmP, hr15] using hLast
  have hNot' : ¬G.Adj (labelledVertex G L (8 + p))
      (labelledVertex G L (8 + r)) := by
    apply decide_eq_false_iff_not.mp
    rw [← coreArc_graph G C L hG (8 + p) (8 + r) (by omega) (by omega)]
    simpa [coreArc, hpA, hpP, hr15] using hNot
  have hneV : (L.p ⟨r, hr⟩).1 ≠ (L.p ⟨p, hp⟩).1 := by
    intro heq
    apply hne
    have : (⟨r, hr⟩ : Fin 6) = ⟨p, hp⟩ := by
      apply L.p.injective
      exact Subtype.ext heq
    exact congrArg (fun n : Nat ↦ 8 + n) (Fin.ext_iff.mp this)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨labelledVertex G L middle, ?_, ?_⟩, ?_, hneV⟩
  · simpa [labelledVertex, hpA, hpP] using of_decide_eq_true hFirst'
  · simpa [labelledVertex, hrA, hrP] using of_decide_eq_true hLast'
  · simpa [labelledVertex, hpA, hpP, hrA, hrP] using hNot'

theorem pSecondPCount_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (p : Nat) (hp : p < 6) :
    (pSecondPCount (graphArc G L) p).toNat ≤
      (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply count_le_filterCard C.P L.p
    (fun r ↦ strictSecondLocal (graphArc G L) (8 + p) (8 + r))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro r hr'
  exact pStrictSecond_true_mem G C L hG p r hp r.isLt hr'

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts
