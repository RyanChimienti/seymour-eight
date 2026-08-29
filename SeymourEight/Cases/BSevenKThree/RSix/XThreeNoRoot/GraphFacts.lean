import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.Encoding
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.BooleanBridge
import Mathlib.Data.Bool.Basic

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.GraphFacts

open Shared Shared.FiniteCore Labels Encoding Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

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
    have ha : (⟨i.val + 1, by omega⟩ : Fin 8) = ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := congrArg Fin.val ha
    change i.val + 1 = j.val + 1 at hval
    omega
  · simpa using hA1Card.symm

@[simp] theorem aOneLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) (i : Fin 3) :
    (aOneLabelEquiv G C L hA1Card i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := by
  rfl

noncomputable def xLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 3) :
    Fin 3 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 3 → {v : V // v ∈ C.X} := fun i ↦
    ⟨(L.a ⟨i.val + 4, by omega⟩).1, L.a_x i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 4, by omega⟩ : Fin 8) = ⟨j.val + 4, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := congrArg Fin.val ha
    change i.val + 4 = j.val + 4 at hval
    omega
  · simpa using hXCard.symm

@[simp] theorem xLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hXCard : C.X.card = 3) (i : Fin 3) :
    (xLabelEquiv G C L hXCard i).1 = (L.a ⟨i.val + 4, by omega⟩).1 := by
  rfl

abbrev graphBits {zCount : Nat} (L : Labels G zCount C) : Core.Encoding :=
  Encoding.graphBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (L.q 0).1 (fun i ↦ (L.z i).1)

def labelledVertex {zCount : Nat} (L : Labels G zCount C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 14 then (L.p ⟨n - 8, by omega⟩).1
  else if hnQ : n = 14 then (L.q 0).1
  else if hnZ : n < 15 + zCount then (L.z ⟨n - 15, by omega⟩).1
  else C.s

@[simp] theorem labelledVertex_a {zCount : Nat} (L : Labels G zCount C)
    (i : Nat) (hi : i < 8) :
    labelledVertex G L i = (L.a ⟨i, hi⟩).1 := by simp [labelledVertex, hi]

@[simp] theorem labelledVertex_p {zCount : Nat} (L : Labels G zCount C)
    (i : Nat) (hi : i < 6) :
    labelledVertex G L (8 + i) = (L.p ⟨i, hi⟩).1 := by
  simp [labelledVertex, show 8+i<14 by omega]

@[simp] theorem labelledVertex_q {zCount : Nat} (L : Labels G zCount C) :
    labelledVertex G L 14 = (L.q 0).1 := by simp [labelledVertex]

@[simp] theorem labelledVertex_z {zCount : Nat} (L : Labels G zCount C)
    (i : Nat) (hi : i < zCount) :
    labelledVertex G L (15 + i) = (L.z ⟨i, hi⟩).1 := by
  simp [labelledVertex, show ¬15+i<8 by omega, show ¬15+i<14 by omega,
    show 15+i≠14 by omega, hi]

def retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  C.A ∪ C.B ∪ externalTargets G C

noncomputable def retainedLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    Fin (15 + zCount) ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin (15 + zCount) → {v : V // v ∈ retainedVertexSet G C} := fun i ↦
    if hiA : i.val < 8 then
      ⟨(L.a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left _ (Finset.mem_union_left _ (L.a _).2)⟩
    else if hiP : i.val < 14 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left _ (Finset.mem_union_right _
          (Digraph.LocalConfiguration.P_subset_B (G := G) C (L.p _).2))⟩
    else if hiQ : i.val = 14 then
      ⟨(L.q 0).1, Finset.mem_union_left _ (Finset.mem_union_right _
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2))⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1,
      Finset.mem_union_right _ (L.z _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAB | hvZ
    · rcases Finset.mem_union.mp hvAB with hvA | hvB
      · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hvB
        rcases Finset.mem_union.mp hvB with hvP | hvQ
        · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
          refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show ¬i.val + 8 < 8 by omega,
            show i.val + 8 < 14 by omega] using congrArg Subtype.val hi
        · obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hvQ⟩
          have hi0 : i = 0 := Subsingleton.elim _ _
          refine ⟨⟨14, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, hi0] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 14 by omega,
        show i.val + 15 ≠ 14 by omega] using congrArg Subtype.val hi
  · have hAB : Disjoint C.A C.B :=
      Digraph.LocalConfiguration.disjoint_A_B (G := G) C
    have hABZ : Disjoint (C.A ∪ C.B) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvAB hvZ
      rcases Finset.mem_union.mp hvAB with hvA | hvB
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
          · simp [rootSecondFinset, hReach] at hvRoot
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_right _ hvB)
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_B (G := G) C hvB
          · simp [rootSecondFinset, hReach] at hvRoot
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp,
      retainedVertexSet, Finset.card_union_of_disjoint hABZ,
      Finset.card_union_of_disjoint hAB]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hb : C.B.card = 7 := by
      rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
        Finset.card_union_of_disjoint
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
      have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
      have hq : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
      omega
    have hz : (externalTargets G C).card = zCount := by
      simpa using (Fintype.card_congr L.z).symm
    simp [ha, hb, hz]

@[simp] theorem retainedLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (i : Fin (15 + zCount)) :
    (retainedLabelEquiv G C L hG i).1 = labelledVertex G L i.val := by
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

theorem A_not_adj_external (C : G.LocalConfiguration) (hG : G.IsOriented)
    (u v : V) (hu : u ∈ C.A) (hv : v ∈ externalTargets G C) : ¬G.Adj u v := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · exact
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
        G C hG u v hu hvZ
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      intro hus
      exact hG.2 ((Digraph.mem_outNeighborFinset (G := G)).mp hu) hus
    · simp [rootSecondFinset, hReach] at hvRoot

set_option linter.flexible false in
theorem encodedArc_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source target : Nat) (hs : source < 14) (ht : target < 15 + zCount) :
    encodedArc (graphBits G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  have hA0P : ∀ i : Fin 6, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 6, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i ↦ hG.2 (hA0P i)
  by_cases hsA : source < 8
  · by_cases htA : target < 8
    · by_cases hs0 : source = 0
      · subst source
        rcases (show target = 0 ∨ (1 ≤ target ∧ target ≤ 3) ∨
            (4 ≤ target ∧ target ≤ 7) by omega) with rfl | htA1 | htXR
        · simpa [encodedArc, labelledVertex] using decide_eq_false (hG.1 (L.a 0).1)
        · have hm : (L.a ⟨target, htA⟩).1 ∈ C.A1 := by
            have heq : (⟨target, htA⟩ : Fin 8) =
                ⟨(target - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
            rw [heq]
            exact L.a_aOne ⟨target - 1, by omega⟩
          have ha : G.Adj (L.a 0).1 (L.a ⟨target, htA⟩).1 := by
            rw [L.a_zero]
            exact (Finset.mem_filter.mp hm).2
          simp [encodedArc, labelledVertex, htA, htA1, ha]
        · by_cases htR : target = 7
          · subst target
            have hn : ¬G.Adj (L.a 0).1 (L.a 7).1 := by
              intro ha
              have hm : (L.a 7).1 ∈ C.A1 := by
                apply Finset.mem_filter.mpr
                rw [← L.a_zero]
                exact ⟨(L.a 7).2, ha⟩
              exact (Finset.disjoint_left.mp
                (Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C))
                  (Finset.mem_union_left _ (Finset.mem_union_left _ hm)) L.a_r
            simp [encodedArc, labelledVertex, hn]
          · have hm : (L.a ⟨target, htA⟩).1 ∈ C.X := by
              have heq : (⟨target, htA⟩ : Fin 8) =
                  ⟨(target - 4) + 4, by omega⟩ := Fin.ext (by simp; omega)
              rw [heq]
              exact L.a_x ⟨target - 4, by omega⟩
            have hn : ¬G.Adj (L.a 0).1 (L.a ⟨target, htA⟩).1 := by
              intro ha
              have hm1 : (L.a ⟨target, htA⟩).1 ∈ C.A1 := by
                apply Finset.mem_filter.mpr
                rw [← L.a_zero]
                exact ⟨(L.a _).2, ha⟩
              exact (Finset.disjoint_left.mp
                (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hm1 hm
            simp [encodedArc, labelledVertex, htA, hn]
            omega
      · by_cases ht0 : target = 0
        · subst target
          by_cases hsA1 : source ≤ 3
          · have hm : (L.a ⟨source, hsA⟩).1 ∈ C.A1 := by
              have heq : (⟨source, hsA⟩ : Fin 8) =
                  ⟨(source - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
              rw [heq]
              exact L.a_aOne ⟨source - 1, by omega⟩
            have ha : G.Adj (L.a 0).1 (L.a ⟨source, hsA⟩).1 := by
              rw [L.a_zero]
              exact (Finset.mem_filter.mp hm).2
            simp [encodedArc, labelledVertex, hsA, hsA1, hG.2 ha]
          · have hi : source - 4 < 4 := by omega
            have heq : (⟨4 + (source - 4), by omega⟩ : Fin 8) =
                ⟨source, hsA⟩ := Fin.ext (by simp; omega)
            rw [show source = 4 + (source - 4) by omega,
              Encoding.aToZero_graphBits G.Adj _ _ _ _ (source - 4) hi, heq]
            simp [labelledVertex, show 4 + (source - 4) = source by omega, hsA]
        · have hi : source - 1 < 7 := by omega
          have hj : target - 1 < 7 := by omega
          rw [show source = (source - 1) + 1 by omega,
            show target = (target - 1) + 1 by omega,
            Encoding.hArc_graphBits G.Adj _ _ _ _ _ _ hi hj]
          have hsFin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          have htFin : (⟨target - 1 + 1, by omega⟩ : Fin 8) =
              ⟨target, htA⟩ := Fin.ext (by simp; omega)
          rw [hsFin, htFin]
          have hne : G.Adj (L.a ⟨source, hsA⟩).1
              (L.a ⟨target, htA⟩).1 → source - 1 ≠ target - 1 := by
            intro ha heq
            have : source = target := by omega
            subst target
            exact hG.1 _ ha
          simp [labelledVertex, show source - 1 + 1 = source by omega,
            show target - 1 + 1 = target by omega, hsA, htA]
          exact hne
    · by_cases htP : target < 14
      · by_cases hs0 : source = 0
        · subst source
          simp [encodedArc, labelledVertex, htA, htP, hA0P]
        · rw [show source = (source - 1) + 1 by omega,
            show target = 8 + (target - 8) by omega,
            Encoding.hToP_graphBits G.Adj _ _ _ _ _ _ (by omega) (by omega)]
          have hsFin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          rw [hsFin]
          simp [labelledVertex, show source - 1 + 1 = source by omega,
            show 8 + (target - 8) = target by omega, hsA, htA, htP]
      · by_cases htQ : target = 14
        · subst target
          by_cases hs0 : source = 0
          · subst source
            have hn : ¬G.Adj (L.a 0).1 (L.q 0).1 := by
              rw [L.a_zero]
              intro ha
              exact (Finset.mem_sdiff.mp (L.q 0).2).2
                (Finset.mem_filter.mpr ⟨
                  Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2, ha⟩)
            simp [encodedArc, labelledVertex, hn]
          · rw [show source = (source - 1) + 1 by omega,
              Encoding.aToQ_graphBits G.Adj _ _ _ _ _ (by omega)]
            have hsFin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
                ⟨source, hsA⟩ := Fin.ext (by simp; omega)
            rw [hsFin]
            simp [labelledVertex, show source - 1 + 1 = source by omega, hsA]
        · have hn := A_not_adj_external G C hG (L.a ⟨source, hsA⟩).1
              (L.z ⟨target - 15, by omega⟩).1 (L.a _).2 (L.z _).2
          simp [encodedArc, labelledVertex, hsA, htA, htP, htQ, ht, hn]
  · have hsP : source < 14 := hs
    by_cases htA : target < 8
    · by_cases ht0 : target = 0
      · subst target
        simp [encodedArc, labelledVertex, hsA, hsP, hP0]
      · by_cases htH : target ≤ 6
        · rw [show source = 8 + (source - 8) by omega,
            show target = (target - 1) + 1 by omega,
            Encoding.pToH_graphBits G.Adj _ _ _ _ _ _ (by omega) (by omega)]
          have htFin : (⟨target - 1 + 1, by omega⟩ : Fin 8) =
              ⟨target, htA⟩ := Fin.ext (by simp; omega)
          rw [htFin]
          simp [labelledVertex, show 8 + (source - 8) = source by omega,
            show target - 1 + 1 = target by omega, hsA, hsP, htA]
        · have hn := BSixKThreeCoreGraphBridge.P_not_adj_R G C
              (L.p ⟨source - 8, by omega⟩).1 (L.a 7).1 (L.p _).2 L.a_r
          have ht7 : target = 7 := by omega
          subst target
          simp [encodedArc, labelledVertex, hsA, hsP, hn]
    · by_cases htP : target < 14
      · rw [show source = 8 + (source - 8) by omega,
          show target = 8 + (target - 8) by omega,
          Encoding.pArc_graphBits G.Adj _ _ _ _ _ _ (by omega) (by omega)]
        have hne : G.Adj (L.p ⟨source - 8, by omega⟩).1
            (L.p ⟨target - 8, by omega⟩).1 → source - 8 ≠ target - 8 := by
          intro ha heq
          have hFin : (⟨source - 8, by omega⟩ : Fin 6) =
              ⟨target - 8, by omega⟩ := Fin.ext heq
          exact hG.1 _ (by simpa [hFin] using ha)
        simp [labelledVertex, show 8 + (source - 8) = source by omega,
          show 8 + (target - 8) = target by omega, hsA, hsP, htA, htP]
        exact hne
      · by_cases htQ : target = 14
        · subst target
          rw [show source = 8 + (source - 8) by omega,
            Encoding.pToQ_graphBits G.Adj _ _ _ _ _ (by omega)]
          simp [labelledVertex, show 8 + (source - 8) = source by omega, hsA, hsP]
        · rw [show source = 8 + (source - 8) by omega,
            show target = 15 + (target - 15) by omega,
            Encoding.pToZ_graphBits G.Adj _ _ _ _ _ _ (by omega) (by omega) (by omega)]
          simp [labelledVertex, show 8 + (source - 8) = source by omega,
            show 15 + (target - 15) = target by omega,
            hsA, hsP, htA, htP, htQ, ht]

theorem aArc_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    encodedArc (graphBits G L) i j =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  simpa [labelledVertex, hi, hj] using
    encodedArc_graphBits G C L hG hzLe i j (by omega) (by omega)

theorem aToP_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (a p : Nat) (ha : a < 8) (hp : p < 6) :
    encodedArc (graphBits G L) a (8+p) =
      decide (G.Adj (L.a ⟨a, ha⟩).1 (L.p ⟨p, hp⟩).1) := by
  simpa [labelledVertex, ha, show 8+p<14 by omega] using
    encodedArc_graphBits G C L hG hzLe a (8+p) (by omega) (by omega)

theorem pToA_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (p a : Nat) (hp : p < 6) (ha : a < 8) :
    encodedArc (graphBits G L) (8+p) a =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨a, ha⟩).1) := by
  simpa [labelledVertex, ha, show 8+p<14 by omega] using
    encodedArc_graphBits G C L hG hzLe (8+p) a (by omega) (by omega)

theorem pArc_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (i j : Nat) (hi : i < 6) (hj : j < 6) :
    encodedArc (graphBits G L) (8+i) (8+j) =
      decide (G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1) := by
  simpa [labelledVertex, show 8+i<14 by omega, show 8+j<14 by omega] using
    encodedArc_graphBits G C L hG hzLe (8+i) (8+j) (by omega) (by omega)

theorem aToQ_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (a : Nat) (ha : a < 8) :
    encodedArc (graphBits G L) a 14 =
      decide (G.Adj (L.a ⟨a, ha⟩).1 (L.q 0).1) := by
  simpa [labelledVertex, ha] using
    encodedArc_graphBits G C L hG hzLe a 14 (by omega) (by omega)

theorem pToQ_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (p : Nat) (hp : p < 6) :
    encodedArc (graphBits G L) (8+p) 14 =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1) := by
  simpa [labelledVertex, show 8+p<14 by omega] using
    encodedArc_graphBits G C L hG hzLe (8+p) 14 (by omega) (by omega)

theorem pToZ_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (p z : Nat) (hp : p < 6) (hz : z < zCount) :
    encodedArc (graphBits G L) (8+p) (15+z) =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  simpa [labelledVertex, show 8+p<14 by omega, show ¬15+z<8 by omega,
    show ¬15+z<14 by omega, show 15+z≠14 by omega, hz] using
    encodedArc_graphBits G C L hG hzLe (8+p) (15+z) (by omega) (by omega)

theorem strictSecond_true_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source target : Nat) (hs : source < 14) (ht : target < 15 + zCount)
    (hSecond : strictSecond (encodedArc (graphBits G L)) source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  simp only [strictSecond, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 14 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [encodedArc_graphBits G C L hG hzLe source middle (by omega) (by omega)] at hFirst
  rw [encodedArc_graphBits G C L hG hzLe middle target hm ht] at hLast
  rw [encodedArc_graphBits G C L hG hzLe source target (by omega) ht] at hNot
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin (15+zCount)) = ⟨source, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa [retainedLabelEquiv_val] using heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨labelledVertex G L middle, of_decide_eq_true hFirst,
      of_decide_eq_true hLast⟩,
    by simpa using hNot, hVertexNe⟩

theorem secondCount_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 8) :
    (secondCount zCount (encodedArc (graphBits G L)) source).toNat ≤
      G.secondOutdegree (L.a ⟨source, hs⟩).1 := by
  have hFiltered := count_le_filterCard (V := V) (retainedVertexSet G C)
    (retainedLabelEquiv G C L hG)
    (strictSecond (encodedArc (graphBits G L)) source)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1)
    (by omega) (by
      intro j hj
      rw [retainedLabelEquiv_val G C L hG]
      have hm := strictSecond_true_mem G C L hG hzLe source j (by omega) j.isLt hj
      rw [labelledVertex_a G L source hs] at hm
      exact hm)
  unfold secondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

noncomputable def hLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 6) :
    Fin 6 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 6 → {v : V // v ∈ C.H} := fun i ↦
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
    have hval : i.val + 1 = j.val + 1 := congrArg Fin.val ha
    exact Nat.add_right_cancel hval
  · simpa using hHCard.symm

@[simp] theorem hLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 6) (i : Fin 6) :
    (hLabelEquiv G C L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

theorem aOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 8) :
    (aOut (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  rw [aArc_graphBits G C L hG hzLe source j hs j.isLt]
  simp

theorem aPOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 8) :
    (aPOut (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G C.P (L.a ⟨source, hs⟩).1 := by
  rw [aPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [aToP_graphBits G C L hG hzLe source j hs j.isLt]
  simp

theorem aBOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 8) :
    (aBOut (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G C.B (L.a ⟨source, hs⟩).1 := by
  have hPQ : C.B = C.P ∪ C.Q :=
    (Digraph.LocalConfiguration.P_union_Q (G := G) C).symm
  rw [hPQ, directCount_union_of_disjoint G C.P C.Q _
    (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
  have hP := aPOut_toNat G C L hG hzLe source hs
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro v hv
    obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hv⟩
    simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
  have hQC : Shared.directCount G C.Q (L.a ⟨source, hs⟩).1 =
      if G.Adj (L.a ⟨source, hs⟩).1 (L.q 0).1 then 1 else 0 := by
    calc
      _ = Shared.directCount G {(L.q 0).1} (L.a ⟨source, hs⟩).1 :=
        congrArg (fun S ↦ Shared.directCount G S (L.a ⟨source, hs⟩).1) hQ
      _ = _ := by simp [Shared.directCount_singleton, Shared.epsilonAt]
  have hPLe : Shared.directCount G C.P (L.a ⟨source, hs⟩).1 ≤ 6 := by
    change (C.P.filter (G.Adj (L.a ⟨source, hs⟩).1)).card ≤ 6
    have h := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.a ⟨source, hs⟩).1) C.P)
    have hc : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    omega
  rw [aBOut, BitVec.toNat_add, hP, hQC]
  have hBit : (bitCount (encodedArc (graphBits G L) source 14)).toNat =
      if G.Adj (L.a ⟨source, hs⟩).1 (L.q 0).1 then 1 else 0 := by
    rw [bitCount, aToQ_graphBits G C L hG hzLe source hs]
    by_cases h : G.Adj (L.a ⟨source, hs⟩).1 (L.q 0).1 <;>
      simp [h, BitVec.toNat_ofNat]
  have hBitLe : (bitCount (encodedArc (graphBits G L) source 14)).toNat ≤ 1 := by
    rw [hBit]
    split <;> omega
  rw [Nat.mod_eq_of_lt (by omega), hBit]

theorem pOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 6) :
    (pOut (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G C.P (L.p ⟨source, hs⟩).1 := by
  rw [pOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [pArc_graphBits G C L hG hzLe source j hs j.isLt]
  simp

theorem pHOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hHCard : C.H.card = 6) (source : Nat) (hs : source < 6) :
    (pHOut (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G C.H (L.p ⟨source, hs⟩).1 := by
  rw [pHOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H (hLabelEquiv G C L hHCard) _
  intro j
  rw [hLabelEquiv_val]
  rw [show 1 + j.val = j.val + 1 by omega]
  rw [pToA_graphBits G C L hG hzLe source (j+1) hs (by omega)]
  simp

theorem hPOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hHCard : C.H.card = 6) (source : Nat) (hs : source < 6) :
    (hPOut (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G C.P (hLabelEquiv G C L hHCard ⟨source, hs⟩).1 := by
  rw [hPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [hLabelEquiv_val]
  rw [show 1 + source = source + 1 by omega]
  rw [aToP_graphBits G C L hG hzLe (source+1) j (by omega) j.isLt]
  simp

theorem totalHToP_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (hHCard : C.H.card = 6) :
    (totalHToP (encodedArc (graphBits G L))).toNat = edgeCount G C.H C.P := by
  have hToNat (n : Nat) (f : Nat → BitVec 8) :
      (sumCount n f).toNat = (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
    induction n with
    | zero => simp [sumCount]
    | succ n ih =>
        rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
        norm_num
  rw [totalHToP, hToNat]
  have hSum : (∑ i ∈ Finset.range 6,
      (hPOut (encodedArc (graphBits G L)) i).toNat) = edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hLabelEquiv G C L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact hPOut_toNat G C L hG hzLe hHCard i i.isLt
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hPCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem pAuxOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 6) :
    (pAuxOut zCount (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G (C.Q ∪ externalTargets G C) (L.p ⟨source, hs⟩).1 := by
  rw [pAuxOut, show 1+zCount=zCount+1 by omega,
    toNat_count_eq_fin_sum (zCount+1) _ (by omega)]
  have hDisjoint : Disjoint C.Q (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvQ hvE
      rcases Finset.mem_union.mp hvE with hvZ | hvRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
            (Finset.mem_union_right _
              (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ))
      · by_cases hr : ∃ p ∈ C.P, G.Adj p C.s
        · have : v = C.s := by simpa [rootSecondFinset, hr] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_B (G := G) C
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
        · simp [rootSecondFinset, hr] at hvRoot
  have hUnion := directCount_union_of_disjoint G C.Q (externalTargets G C)
    (L.p ⟨source, hs⟩).1 hDisjoint
  rw [hUnion]
  have hQCount : Shared.directCount G C.Q (L.p ⟨source, hs⟩).1 =
      if G.Adj (L.p ⟨source, hs⟩).1 (L.q 0).1 then 1 else 0 := by
    have hQ : C.Q = {(L.q 0).1} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨(L.q 0).2, ?_⟩
      intro v hv
      obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hv⟩
      simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
    calc
      Shared.directCount G C.Q (L.p ⟨source, hs⟩).1 =
          Shared.directCount G {(L.q 0).1} (L.p ⟨source, hs⟩).1 :=
        congrArg (fun S ↦ Shared.directCount G S (L.p ⟨source, hs⟩).1) hQ
      _ = _ := by simp [Shared.directCount_singleton, Shared.epsilonAt]
  have hZCount : Shared.directCount G (externalTargets G C)
      (L.p ⟨source, hs⟩).1 =
      ∑ j : Fin zCount, if G.Adj (L.p ⟨source, hs⟩).1 (L.z j).1 then 1 else 0 := by
    rw [directCount_eq_sum_fin G (externalTargets G C) L.z]
    simp
  rw [hQCount, hZCount]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.add_zero]
  congr 1
  · simp only [pToQ_graphBits G C L hG hzLe source hs]
    simp
  · apply Finset.sum_congr rfl
    intro j _
    rw [show 14 + j.succ.val = 15 + j.val by simp; omega]
    simp only [pToZ_graphBits G C L hG hzLe source j hs j.isLt]
    simp

theorem pZOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 6) :
    (pZOut zCount (encodedArc (graphBits G L)) source).toNat =
      Shared.directCount G (externalTargets G C) (L.p ⟨source, hs⟩).1 := by
  rw [pZOut, toNat_count_eq_fin_sum zCount _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (externalTargets G C) L.z _
  intro j
  rw [pToZ_graphBits G C L hG hzLe source j hs j.isLt]
  simp

theorem innerSecond_true_iff {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source target : Nat) (hs : source < 8) (ht : target < 8) :
    innerSecond (encodedArc (graphBits G L)) source target = true ↔
      (L.a ⟨target, ht⟩).1 ∈
        CertificateBridge.internalSecondNeighbors (G := G) C.A
          (L.a ⟨source, hs⟩).1 := by
  unfold innerSecond innerReaches
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    CertificateBridge.internalSecondNeighbors, Finset.mem_filter]
  rw [aArc_graphBits G C L hG hzLe source target hs ht]
  constructor
  · rintro ⟨⟨hne, hNot⟩, hReach⟩
    obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 8 _).mp hReach
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
    rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
    rw [aArc_graphBits G C L hG hzLe source middle hs hm] at hFirst
    rw [aArc_graphBits G C L hG hzLe middle target hm ht] at hLast
    have hNot' : ¬G.Adj (L.a ⟨source, hs⟩).1 (L.a ⟨target, ht⟩).1 := by
      simpa using hNot
    refine ⟨(L.a ⟨target, ht⟩).2, hNot', ?_,
      (L.a ⟨middle, hm⟩).1, (L.a ⟨middle, hm⟩).2,
      of_decide_eq_true hFirst, of_decide_eq_true hLast⟩
    intro heq
    apply hne
    have hfin : (⟨target, ht⟩ : Fin 8) = ⟨source, hs⟩ := by
      apply L.a.injective
      apply Subtype.ext
      exact heq
    exact Fin.ext_iff.mp hfin
  · rintro ⟨_, hNot, hneVertex, middle, hmA, hFirst, hLast⟩
    obtain ⟨mi, hmi⟩ := L.a.surjective ⟨middle, hmA⟩
    have hmVal : (L.a mi).1 = middle := congrArg Subtype.val hmi
    have hms : mi.val ≠ source := by
      intro heq
      have hfin : mi = ⟨source, hs⟩ := Fin.ext heq
      rw [hfin] at hmVal
      rw [← hmVal] at hFirst
      exact hG.1 _ hFirst
    have hmt : mi.val ≠ target := by
      intro heq
      have hfin : mi = ⟨target, ht⟩ := Fin.ext heq
      rw [hfin] at hmVal
      rw [← hmVal] at hLast
      exact hG.1 _ hLast
    have hst : target ≠ source := by
      intro heq
      apply hneVertex
      apply congrArg (fun q : Fin 8 ↦ (L.a q).1)
      exact Fin.ext heq
    have hNotB : (!decide
        (G.Adj (L.a ⟨source, hs⟩).1 (L.a ⟨target, ht⟩).1)) = true := by
      simp [hNot]
    refine ⟨⟨hst, hNotB⟩, (any_eq_true_iff 8 _).mpr
      ⟨mi, mi.isLt, ?_⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hms, hmt⟩, ?_⟩, ?_⟩
    · rw [aArc_graphBits G C L hG hzLe source mi hs mi.isLt]
      exact decide_eq_true (by simpa [hmVal] using hFirst)
    · rw [aArc_graphBits G C L hG hzLe mi target mi.isLt ht]
      exact decide_eq_true (by simpa [hmVal] using hLast)

theorem innerSecondCount_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 8) :
    (innerSecondCount (encodedArc (graphBits G L)) source).toNat =
      (CertificateBridge.internalSecondNeighbors (G := G) C.A
        (L.a ⟨source, hs⟩).1).card := by
  rw [innerSecondCount, toNat_count_eq_fin_sum 8 _ (by omega)]
  let T := CertificateBridge.internalSecondNeighbors (G := G) C.A
    (L.a ⟨source, hs⟩).1
  have hTSub : T ⊆ C.A := fun _ hv ↦ (Finset.mem_filter.mp hv).1
  have hCard : (C.A.filter fun v ↦ v ∈ T).card = T.card := by
    congr 1
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv ↦ ⟨hTSub hv, hv⟩⟩
  rw [← hCard, filterCard_eq_sum_fin C.A L.a]
  apply Finset.sum_congr rfl
  intro j hj
  have hiff := innerSecond_true_iff G C L hG hzLe source j hs j.isLt
  by_cases hb : innerSecond (encodedArc (graphBits G L)) source j = true
  · have hp : (L.a j).1 ∈ T := hiff.mp hb
    simp [hb, hp]
  · have hp : ¬((L.a j).1 ∈ T) := fun h ↦ hb (hiff.mpr h)
    simp [hb, hp]

def hallTargets (C : G.LocalConfiguration) (v : V) : Finset V :=
  (C.Q ∪ externalTargets G C).filter fun e ↦
    ∃ p ∈ C.P, G.Adj v p ∧ G.Adj p e

theorem hallReached_true_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source e : Nat) (hs : source < 8) (he : e < 1 + zCount)
    (hReach : hallReached zCount (encodedArc (graphBits G L)) source e = true) :
    labelledVertex G L (14 + e) ∈ hallTargets G C (L.a ⟨source, hs⟩).1 := by
  unfold hallReached at hReach
  obtain ⟨p, hp, hPath⟩ := (any_eq_true_iff 6 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  have hFirst := hPath.1
  have hLast := hPath.2
  rw [encodedArc_graphBits G C L hG hzLe source (8+p) (by omega) (by omega)] at hFirst
  rw [encodedArc_graphBits G C L hG hzLe (8+p) (14+e) (by omega) (by omega)] at hLast
  have hpAdj : G.Adj (L.a ⟨source, hs⟩).1 (L.p ⟨p, hp⟩).1 := by
    rw [labelledVertex_a G L source hs, labelledVertex_p G L p hp] at hFirst
    exact of_decide_eq_true hFirst
  have heAdj : G.Adj (L.p ⟨p, hp⟩).1 (labelledVertex G L (14+e)) := by
    rw [labelledVertex_p G L p hp] at hLast
    exact of_decide_eq_true hLast
  apply Finset.mem_filter.mpr
  refine ⟨?_, (L.p ⟨p, hp⟩).1, (L.p _).2, hpAdj, heAdj⟩
  by_cases he0 : e = 0
  · subst e
    exact Finset.mem_union_left _ (L.q 0).2
  · apply Finset.mem_union_right _
    have hz : e - 1 < zCount := by omega
    have hv : labelledVertex G L (14+e) = (L.z ⟨e-1, hz⟩).1 := by
      rw [show 14+e=15+(e-1) by omega, labelledVertex_z]
    rw [hv]
    exact (L.z _).2

theorem hallCount_le_card {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (source : Nat) (hs : source < 8) :
    (hallCount zCount (encodedArc (graphBits G L)) source).toNat ≤
      (hallTargets G C (L.a ⟨source, hs⟩).1).card := by
  rw [hallCount, toNat_count_eq_fin_sum (1+zCount) _ (by omega)]
  let f : Fin (1+zCount) → V := fun e ↦ labelledVertex G L (14+e.val)
  have hQE : Disjoint C.Q (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvE
    rcases Finset.mem_union.mp hvE with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
          (Finset.mem_union_right _
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ))
    · by_cases hr : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : v = C.s := by simpa [rootSecondFinset, hr] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_B (G := G) C
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
      · simp [rootSecondFinset, hr] at hvRoot
  have hfInj : Function.Injective f := by
    intro i j hij
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · exact Fin.ext (by omega)
      · have hzj : j.val - 1 < zCount := by omega
        have heq : (L.q 0).1 = (L.z ⟨j.val-1, hzj⟩).1 := by
          have hh := hij
          dsimp [f] at hh
          rw [show 14+i.val=14 by omega, labelledVertex_q,
            show 14+j.val=15+(j.val-1) by omega,
            labelledVertex_z G L (j.val-1) hzj] at hh
          exact hh
        exfalso
        exact (Finset.disjoint_left.mp hQE) (L.q 0).2 (heq ▸ (L.z _).2)
    · by_cases hj0 : j.val = 0
      · have hzi : i.val - 1 < zCount := by omega
        have heq : (L.z ⟨i.val-1, hzi⟩).1 = (L.q 0).1 := by
          have hh := hij
          dsimp [f] at hh
          rw [show 14+i.val=15+(i.val-1) by omega,
            labelledVertex_z G L (i.val-1) hzi,
            show 14+j.val=14 by omega, labelledVertex_q] at hh
          exact hh
        exfalso
        exact (Finset.disjoint_left.mp hQE) (L.q 0).2 (heq ▸ (L.z _).2)
      · have hzi : i.val - 1 < zCount := by omega
        have hzj : j.val - 1 < zCount := by omega
        have heq : (L.z ⟨i.val-1, hzi⟩).1 = (L.z ⟨j.val-1, hzj⟩).1 := by
          have hh := hij
          dsimp [f] at hh
          rw [show 14+i.val=15+(i.val-1) by omega,
            labelledVertex_z G L (i.val-1) hzi,
            show 14+j.val=15+(j.val-1) by omega,
            labelledVertex_z G L (j.val-1) hzj] at hh
          exact hh
        have hfin : (⟨i.val-1, hzi⟩ : Fin zCount) = ⟨j.val-1, hzj⟩ := by
          apply L.z.injective
          exact Subtype.ext heq
        apply Fin.ext
        have hval : i.val - 1 = j.val - 1 := congrArg Fin.val hfin
        change i.val = j.val
        omega
  let T := hallTargets G C (L.a ⟨source, hs⟩).1
  let S : Finset (Fin (1+zCount)) := Finset.univ.filter fun e ↦ f e ∈ T
  have hCountEq : (∑ e : Fin (1+zCount),
      if hallReached zCount (encodedArc (graphBits G L)) source e then 1 else 0) ≤
      S.card := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro e _
    by_cases hb : hallReached zCount (encodedArc (graphBits G L)) source e = true
    · have hm : f e ∈ T := hallReached_true_mem G C L hG hzLe source e hs e.isLt hb
      simp [hb, hm]
    · have hf := Bool.eq_false_of_not_eq_true hb
      simp [hf]
  exact hCountEq.trans (by
    have himage : S.image f ⊆ T := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨e, he, rfl⟩
      exact (Finset.mem_filter.mp he).2
    rw [← Finset.card_image_of_injective S hfInj]
    exact Finset.card_le_card himage)

theorem pSecondP_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 4)
    (p : Nat) (hp : p < 6) :
    (pSecondP (encodedArc (graphBits G L)) p).toNat ≤
      (C.P.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply count_le_filterCard C.P L.p
    (fun q ↦ strictSecond (encodedArc (graphBits G L)) (8+p) (8+q))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro q hq
  have hm := strictSecond_true_mem G C L hG hzLe (8+p) (8+q)
    (by omega) (by omega) hq
  rw [labelledVertex_p G L p hp, labelledVertex_p G L q q.isLt] at hm
  exact hm

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.GraphFacts
