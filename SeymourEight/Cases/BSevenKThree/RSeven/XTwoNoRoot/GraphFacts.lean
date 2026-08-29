import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Labels
import SeymourEight.Certificates.BSevenKThree.RSeven.XTwo.CoreDefs
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.Encoding
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.GraphFacts

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.GraphFacts

open Shared Shared.FiniteCore Labels
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot
open XThreeNoRoot.Core XThreeNoRoot.Encoding

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev graphBits {zCount : Nat} (L : Labels G zCount C) : XThreeNoRoot.Core.Encoding :=
  coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)

def labelledVertex {zCount : Nat} (L : Labels G zCount C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 15 then (L.p ⟨n - 8, by omega⟩).1
  else if hnZ : n < 15 + zCount then (L.z ⟨n - 15, by omega⟩).1
  else C.s

abbrev retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  XThreeNoRoot.GraphFacts.retainedVertexSet G C

noncomputable def retainedLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    Fin (15 + zCount) ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin (15 + zCount) → {v : V // v ∈ retainedVertexSet G C} := fun i ↦
    if hiA : i.val < 8 then
      ⟨(L.a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left (externalTargets G C)
          (Finset.mem_union_left C.P (L.a _).2)⟩
    else if hiP : i.val < 15 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left (externalTargets G C)
          (Finset.mem_union_right C.A (L.p _).2)⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1,
      Finset.mem_union_right (C.A ∪ C.P) (L.z _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAP | hvZ
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega,
          show i.val + 8 < 15 by omega] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 15 by omega] using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hAPZ : Disjoint (C.A ∪ C.P) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvAP hvZ
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by
              simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
          · simp [rootSecondFinset, hReach] at hvRoot
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by
              simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
          · simp [rootSecondFinset, hReach] at hvRoot
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp]
    change Fintype.card (Fin (15 + zCount)) =
      ((C.A ∪ C.P) ∪ externalTargets G C).card
    rw [
      Finset.card_union_of_disjoint hAPZ,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hz : (externalTargets G C).card = zCount := by
      simpa using (Fintype.card_congr L.z).symm
    simp [ha, hp, hz]

@[simp] theorem retainedLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (i : Fin (15 + zCount)) :
    (retainedLabelEquiv G C L hG i).1 = labelledVertex G L i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

noncomputable def hLabelEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 5) :
    Fin 5 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 5 → {v : V // v ∈ C.H} := fun i ↦
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, by
      by_cases hi : i.val < 3
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi⟩)
      · apply Finset.mem_union_right C.A1
        have heq : (⟨i.val + 1, by omega⟩ : Fin 8) =
            ⟨(i.val - 3) + 4, by omega⟩ := by
          apply Fin.ext
          change i.val + 1 = i.val - 3 + 4
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
    have hval := congrArg Fin.val ha
    change i.val + 1 = j.val + 1 at hval
    omega
  · simpa using hHCard.symm

@[simp] theorem hLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 5) (i : Fin 5) :
    (hLabelEquiv G C L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

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
    change i.val + 1 = j.val + 1 at hval
    omega
  · simpa using hA1Card.symm

@[simp] theorem aOneLabelEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hA1Card : C.A1.card = 3) (i : Fin 3) :
    (aOneLabelEquiv G C L hA1Card i).1 =
      (L.a ⟨i.val + 1, by omega⟩).1 := rfl

theorem coreArc_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source target : Nat) (hs : source < 15) (ht : target < 15 + zCount) :
    coreArc zCount (graphBits G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  have hA0P : ∀ i : Fin 7, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i ↦ hG.2 (hA0P i)
  unfold coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA]
      by_cases hs0 : source = 0
      · subst source
        have hCases : target = 0 ∨ (1 ≤ target ∧ target ≤ 3) ∨
            (4 ≤ target ∧ target ≤ 7) := by omega
        rcases hCases with rfl | htA1 | htOther
        · simpa [aArc, labelledVertex] using decide_eq_false (hG.1 (L.a 0).1)
        · have hmem : (L.a ⟨target, htA⟩).1 ∈ C.A1 := by
            have heq : (⟨target, htA⟩ : Fin 8) =
                ⟨(target - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
            rw [heq]
            exact L.a_aOne ⟨target - 1, by omega⟩
          have hadj : G.Adj (L.a 0).1 (L.a ⟨target, htA⟩).1 := by
            rw [L.a_zero]
            exact (Finset.mem_filter.mp hmem).2
          simp [aArc, labelledVertex, htA, htA1, hadj]
        · have hnadj : ¬G.Adj (L.a 0).1 (L.a ⟨target, htA⟩).1 := by
            intro hadj
            have hA1 : (L.a ⟨target, htA⟩).1 ∈ C.A1 := by
              apply Finset.mem_filter.mpr
              rw [← L.a_zero]
              exact ⟨(L.a _).2, hadj⟩
            by_cases htX : target ≤ 5
            · have hX : (L.a ⟨target, htA⟩).1 ∈ C.X := by
                have heq : (⟨target, htA⟩ : Fin 8) =
                    ⟨(target - 4) + 4, by omega⟩ := Fin.ext (by simp; omega)
                rw [heq]
                exact L.a_x ⟨target - 4, by omega⟩
              exact (Finset.disjoint_left.mp
                (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hA1 hX
            · have hR : (L.a ⟨target, htA⟩).1 ∈ C.R := by
                have heq : (⟨target, htA⟩ : Fin 8) =
                    ⟨(target - 6) + 6, by omega⟩ := Fin.ext (by simp; omega)
                rw [heq]
                exact L.a_r ⟨target - 6, by omega⟩
              exact (Finset.disjoint_left.mp
                (Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C))
                  (Finset.mem_union_left _ (Finset.mem_union_left _ hA1)) hR
          simp [aArc, labelledVertex, htA, hnadj]
          omega
      · by_cases ht0 : target = 0
        · subst target
          by_cases hsA1 : source ≤ 3
          · have hmem : (L.a ⟨source, hsA⟩).1 ∈ C.A1 := by
              have heq : (⟨source, hsA⟩ : Fin 8) =
                  ⟨(source - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
              rw [heq]
              exact L.a_aOne ⟨source - 1, by omega⟩
            have hadj : G.Adj (L.a 0).1 (L.a ⟨source, hsA⟩).1 := by
              rw [L.a_zero]
              exact (Finset.mem_filter.mp hmem).2
            simp [aArc, labelledVertex, hsA, hsA1, hG.2 hadj]
          · have hsx : source - 4 < 4 := by omega
            have heqs : source = 4 + (source - 4) := by omega
            conv_lhs => rw [heqs]
            rw [aToZero_coreBits G.Adj _ _ _ (source - 4) hsx]
            have heq : (⟨4 + (source - 4), by omega⟩ : Fin 8) =
                ⟨source, hsA⟩ := Fin.ext (by simp; omega)
            rw [heq]
            simp [labelledVertex, hsA]
        · have heqs : source = (source - 1) + 1 := by omega
          have heqt : target = (target - 1) + 1 := by omega
          conv_lhs => rw [heqs, heqt]
          rw [hArc_coreBits G.Adj _ _ _ (source - 1) (target - 1)
            (by omega) (by omega)]
          have hImp : G.Adj (L.a ⟨source, hsA⟩).1 (L.a ⟨target, htA⟩).1 →
              source - 1 ≠ target - 1 := by
            intro hadj heq
            have hst : source = target := by omega
            subst target
            exact hG.1 _ hadj
          have hsi : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := by
            apply Fin.ext
            change source - 1 + 1 = source
            omega
          have hti : (⟨target - 1 + 1, by omega⟩ : Fin 8) =
              ⟨target, htA⟩ := by
            apply Fin.ext
            change target - 1 + 1 = target
            omega
          rw [hsi, hti]
          rw [show decide (source - 1 ≠ target - 1 ∧
              G.Adj (L.a ⟨source, hsA⟩).1 (L.a ⟨target, htA⟩).1) =
              decide (G.Adj (L.a ⟨source, hsA⟩).1
                (L.a ⟨target, htA⟩).1) by
            exact Bool.decide_congr ⟨And.right, fun h ↦ ⟨hImp h, h⟩⟩]
          simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP]
        unfold aToP
        by_cases hs0 : source = 0
        · subst source
          simp [hA0P, labelledVertex, htA, htP]
        · rw [if_neg hs0, hToP_coreBits G.Adj _ _ _ (source - 1) (target - 8)
              (by omega) (by omega)]
          have haeq : (L.a ⟨source - 1 + 1, by omega⟩).1 =
              (L.a ⟨source, hsA⟩).1 := by
            congr 2
            apply Fin.ext
            simp
            omega
          rw [haeq]
          simp [labelledVertex, hsA, htA, htP]
      · have hn := XThreeNoRoot.GraphFacts.A_not_adj_external G C hG
            (L.a ⟨source, hsA⟩).1 (L.z ⟨target - 15, by omega⟩).1
            (L.a _).2 (L.z _).2
        simp [htP, ht, labelledVertex, hsA, htA, hn]
  · rw [if_neg hsA, if_pos hs]
    by_cases htA : target < 8
    · rw [if_pos htA]
      unfold pToA
      by_cases ht0 : target = 0
      · subst target
        simp [hP0, labelledVertex, hsA, hs]
      · rw [if_neg ht0, pToH_coreBits G.Adj _ _ _ (source - 8) (target - 1)
            (by omega) (by omega)]
        have haeq : (L.a ⟨target - 1 + 1, by omega⟩).1 =
            (L.a ⟨target, htA⟩).1 := by
          congr 2
          apply Fin.ext
          simp
          omega
        rw [haeq]
        simp [labelledVertex, hsA, hs, htA]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP, pArc_coreBits G.Adj _ _ _ (source - 8) (target - 8)
            (by omega) (by omega)]
        have hImp : G.Adj (L.p ⟨source - 8, by omega⟩).1
            (L.p ⟨target - 8, by omega⟩).1 → source - 8 ≠ target - 8 := by
          intro hadj hij
          apply hG.1 (L.p ⟨source - 8, by omega⟩).1
          have heq : (⟨source - 8, by omega⟩ : Fin 7) =
              ⟨target - 8, by omega⟩ := Fin.ext hij
          simpa [heq] using hadj
        rw [show decide (source - 8 ≠ target - 8 ∧
            G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) =
            decide (G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) by
          exact Bool.decide_congr ⟨And.right, fun h ↦ ⟨hImp h, h⟩⟩]
        simp [labelledVertex, hsA, hs, htA, htP]
      · rw [if_neg htP, if_pos ht,
          pToZ_coreBits G.Adj _ _ _ (source - 8) (target - 15)
            (by omega) (by omega) (by omega)]
        simp [labelledVertex, hsA, hs, htA, htP, ht]

theorem aArc_graphBits {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (graphBits G L) i j =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  have h := coreArc_graphBits G C L hG hzLe i j (by omega) (by omega)
  simpa [XThreeNoRoot.Core.coreArc, hi, hj, labelledVertex] using h

theorem innerSecond_true_iff {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source target : Nat) (hs : source < 8) (ht : target < 8) :
    innerSecond (graphBits G L) source target = true ↔
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
      apply Fin.ext
      exact heq
    have hNotB : (!decide
        (G.Adj (L.a ⟨source, hs⟩).1 (L.a ⟨target, ht⟩).1)) = true := by
      simp [hNot]
    refine ⟨⟨hst, hNotB⟩, (any_eq_true_iff 8 _).mpr ⟨mi, mi.isLt, ?_⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hms, hmt⟩, ?_⟩, ?_⟩
    · rw [aArc_graphBits G C L hG hzLe source mi hs mi.isLt]
      exact decide_eq_true (by simpa [hmVal] using hFirst)
    · rw [aArc_graphBits G C L hG hzLe mi target mi.isLt ht]
      exact decide_eq_true (by simpa [hmVal] using hLast)

theorem innerSecondCount_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source : Nat) (hs : source < 8) :
    (innerSecondCount (graphBits G L) source).toNat =
      (CertificateBridge.internalSecondNeighbors (G := G) C.A
        (L.a ⟨source, hs⟩).1).card := by
  rw [innerSecondCount, toNat_count_eq_fin_sum 8 _ (by omega)]
  let T := CertificateBridge.internalSecondNeighbors (G := G) C.A
    (L.a ⟨source, hs⟩).1
  have hTSub : T ⊆ C.A := by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have hCard : (C.A.filter fun v ↦ v ∈ T).card = T.card := by
    congr 1
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv ↦ ⟨hTSub hv, hv⟩⟩
  rw [← hCard, filterCard_eq_sum_fin C.A L.a]
  apply Finset.sum_congr rfl
  intro j hj
  have hiff := innerSecond_true_iff G C L hG hzLe source j hs j.isLt
  by_cases hb : innerSecond (graphBits G L) source j = true
  · have hp : (L.a j).1 ∈ T := hiff.mp hb
    simp [hb, hp]
  · have hp : ¬((L.a j).1 ∈ T) := fun h ↦ hb (hiff.mpr h)
    simp [hb, hp]

theorem directCount_graphBits_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (hPB : C.P = C.B) (source : Nat) (hs : source < 15) :
    (XThreeNoRoot.Core.directCount zCount (graphBits G L) source).toNat =
      G.outdegree (labelledVertex G L source) := by
  rw [XThreeNoRoot.Core.directCount,
    toNat_count_eq_fin_sum (15 + zCount) _ (by omega)]
  have hCount : (∑ j : Fin (15 + zCount),
      if coreArc zCount (graphBits G L) source j then 1 else 0) =
      Shared.directCount G (retainedVertexSet G C)
        (labelledVertex G L source) := by
    symm
    apply directCount_eq_sum_bool G (retainedVertexSet G C)
      (retainedLabelEquiv G C L hG) _
    intro j
    rw [retainedLabelEquiv_val G C L hG,
      coreArc_graphBits G C L hG hzLe source j hs j.isLt]
    simp
  rw [hCount]
  apply (outdegree_eq_directCount_of_captured G _ _ ?_).symm
  by_cases hsA : source < 8
  · simpa [labelledVertex, hsA] using
      XThreeNoRoot.GraphFacts.A_outgoingCaptured_retained G C hG hPB
        (L.a ⟨source, hsA⟩).1 (L.a _).2
  · simpa [labelledVertex, hsA, hs] using
      XThreeNoRoot.GraphFacts.P_outgoingCaptured_retained G C hG hPB
        (L.p ⟨source - 8, by omega⟩).1 (L.p _).2

theorem strictSecondLocal_true_mem {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source target : Nat) (hs : source < 15) (ht : target < 15 + zCount)
    (hSecond : strictSecondLocal zCount (graphBits G L) source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_graphBits G C L hG hzLe source middle hs (by omega)] at hFirst
  rw [coreArc_graphBits G C L hG hzLe middle target hm ht] at hLast
  rw [coreArc_graphBits G C L hG hzLe source target hs ht] at hNotArc
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin (15 + zCount)) = ⟨source, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa [retainedLabelEquiv_val G C L hG] using heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

theorem localSecondCount_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source : Nat) (hs : source < 15) :
    (localSecondCount zCount (graphBits G L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  have hFiltered := XThreeNoRoot.GraphFacts.count_le_filterCard (V := V)
    (retainedVertexSet G C) (retainedLabelEquiv G C L hG)
    (strictSecondLocal zCount (graphBits G L) source)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    (by omega) (by
      intro j hj
      rw [retainedLabelEquiv_val G C L hG]
      exact strictSecondLocal_true_mem G C L hG hzLe source j hs j.isLt hj)
  unfold localSecondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

theorem nonSeymour_graphBits_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (hPB : C.P = C.B) (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 15) :
    (localSecondCount zCount (graphBits G L) source).ult
      (XThreeNoRoot.Core.directCount zCount (graphBits G L) source) = true := by
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [directCount_graphBits_toNat G C L hG hzLe hPB source hs]
  exact (localSecondCount_le_graph G C L hG hzLe source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨labelledVertex G L source, h⟩))

theorem A_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = Shared.directCount G C.A u + Shared.directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG u hu
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.P) u (by
    intro v hv
    simpa [hPB] using hCap hv)
  rw [directCount_union_of_disjoint G C.A C.P u hAP] at hEq
  exact hEq

theorem aOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source : Nat) (hs : source < 8) :
    (aOut (graphBits G L) source).toNat =
      Shared.directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  rw [aArc_graphBits G C L hG hzLe source j hs j.isLt]
  simp

theorem aPOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 6)
    (source : Nat) (hs : source < 8) :
    (aPOut (graphBits G L) source).toNat =
      Shared.directCount G C.P (L.a ⟨source, hs⟩).1 := by
  rw [aPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  have h := coreArc_graphBits G C L hG hzLe source (8 + j.val)
    (by omega) (by omega)
  have h' : aToP (graphBits G L) source j =
      decide (G.Adj (L.a ⟨source, hs⟩).1 (L.p j).1) := by
    simpa [XThreeNoRoot.Core.coreArc, hs, show ¬8 + j.val < 8 by omega,
      show 8 + j.val < 15 by omega, labelledVertex] using h
  rw [h']
  simp

theorem pOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (source : Nat) (hs : source < 7) :
    (pOut (graphBits G L) source).toNat =
      Shared.directCount G C.P (L.p ⟨source, hs⟩).1 := by
  rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [pArc_coreBits G.Adj _ _ _ source j hs j.isLt]
  simp only [decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hadj
    refine ⟨?_, hadj⟩
    intro heq
    have hpEq : (⟨source, hs⟩ : Fin 7) = j := Fin.ext heq
    rw [hpEq] at hadj
    exact hG.1 (L.p j).1 hadj

theorem pHOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (_hG : G.IsOriented) (hHCard : C.H.card = 5)
    (source : Nat) (hs : source < 7) :
    (XTwoNoRoot.Core.pHOut (graphBits G L) source).toNat =
      Shared.directCount G C.H (L.p ⟨source, hs⟩).1 := by
  rw [XTwoNoRoot.Core.pHOut,
    toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H (hLabelEquiv G C L hHCard) _
  intro j
  rw [hLabelEquiv_val]
  rw [pToH_coreBits G.Adj _ _ _ source j hs (by omega)]
  simp

theorem pZOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hzLe : zCount ≤ 6)
    (source : Nat) (hs : source < 7) :
    (pZOut zCount (graphBits G L) source).toNat =
      Shared.directCount G (externalTargets G C) (L.p ⟨source, hs⟩).1 := by
  rw [pZOut, toNat_count_eq_fin_sum zCount _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (externalTargets G C) L.z _
  intro j
  rw [pToZ_coreBits G.Adj _ _ _ source j hs (by omega) j.isLt]
  simp

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.GraphFacts
