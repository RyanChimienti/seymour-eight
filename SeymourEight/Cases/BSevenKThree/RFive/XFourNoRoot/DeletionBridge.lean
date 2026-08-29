import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.AugmentedBridge
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.DeletionBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def middleVertex {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i : Nat) : V :=
  labelledVertex G L (aOnePIndex i)

def targetVertex {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i : Nat) : V :=
  labelledVertex G L (aOneSecondTargetIndex i)

theorem aOnePIndex_lt (i : Nat) (hi : i < 8) : aOnePIndex i < 13 := by
  simp [aOnePIndex]
  split <;> omega

theorem targetIndex_lt {zCount : Nat} (i : Nat) (hi : i < 6 + zCount)
    (_hzLe : zCount ≤ 2) : aOneSecondTargetIndex i < 15 + zCount := by
  unfold aOneSecondTargetIndex
  split
  · omega
  · split <;> omega

theorem middleVertex_injective {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    Function.Injective (fun i : Fin 8 ↦ middleVertex G L i) := by
  intro i j hij
  have hfin : (⟨aOnePIndex i, (aOnePIndex_lt i i.isLt).trans (by omega)⟩ :
      Fin (15 + zCount)) =
      ⟨aOnePIndex j, (aOnePIndex_lt j j.isLt).trans (by omega)⟩ := by
    apply (retainedLabelEquiv G C L hG).injective
    apply Subtype.ext
    simpa [middleVertex, retainedLabelEquiv_val] using hij
  apply Fin.ext
  have hn := Fin.ext_iff.mp hfin
  simp only [aOnePIndex] at hn
  split at hn <;> split at hn <;> omega

theorem targetVertex_injective {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 2) :
    Function.Injective (fun i : Fin (6 + zCount) ↦ targetVertex G L i) := by
  intro i j hij
  have hfin :
      (⟨aOneSecondTargetIndex i, targetIndex_lt i i.isLt hzLe⟩ : Fin (15 + zCount)) =
      ⟨aOneSecondTargetIndex j, targetIndex_lt j j.isLt hzLe⟩ := by
    apply (retainedLabelEquiv G C L hG).injective
    apply Subtype.ext
    simpa [targetVertex, retainedLabelEquiv_val] using hij
  apply Fin.ext
  have hn := Fin.ext_iff.mp hfin
  by_cases hi4 : i.val < 4 <;> by_cases hi6 : i.val < 6 <;>
    by_cases hj4 : j.val < 4 <;> by_cases hj6 : j.val < 6 <;>
    simp [aOneSecondTargetIndex, hi4, hi6, hj4, hj6] at hn <;> omega

theorem middle_mem_out {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hFixed : fixedAOne (graphArc G L) = true) (i : Nat) (hi : i < 8) :
    middleVertex G L i ∈ G.outNeighborFinset C.a1 := by
  rw [Digraph.mem_outNeighborFinset]
  rw [fixedAOne, all_eq_true_iff] at hFixed
  have h := hFixed (aOnePIndex i) (by
    exact (aOnePIndex_lt i hi).trans (by omega))
  have hArc : graphArc G L 0 (aOnePIndex i) = true := by
    have hp : (decide (1 ≤ aOnePIndex i) && decide (aOnePIndex i ≤ 3) ||
        decide (8 ≤ aOnePIndex i) && decide (aOnePIndex i < 13)) = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      unfold aOnePIndex
      split <;> omega
    simpa [hp] using h
  have ht15 : aOnePIndex i < 15 :=
    (aOnePIndex_lt i hi).trans (by omega)
  have hCore : coreArc zCount (graphArc G L) (graphPToZ G L) 0
      (aOnePIndex i) = true := by
    simpa [coreArc, ht15] using hArc
  have hg := coreArc_graph G C L hG 0 (aOnePIndex i)
    (by omega) (by exact (aOnePIndex_lt i hi).trans (by omega))
  rw [hCore] at hg
  simpa [middleVertex, labelledVertex, L.a_zero] using hg

theorem middle_surjective {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hA1Card : C.A1.card = 3)
    (w : V) (hw : w ∈ G.outNeighborFinset C.a1) :
    ∃ i : Fin 8, middleVertex G L i = w := by
  have hOut := Shared.outNeighborFinset_a1_eq_A1_union_P G C hG
  rw [hOut] at hw
  rcases Finset.mem_union.mp hw with hwA | hwP
  · obtain ⟨i, hi⟩ := (aOneLabelEquiv G C L hA1Card).surjective ⟨w, hwA⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    have hi3 : i.val < 3 := by omega
    have hi8 : 1 + i.val < 8 := by omega
    unfold middleVertex
    rw [show aOnePIndex i.val = 1 + i.val by simp [aOnePIndex, hi3]]
    have hia : (L.a ⟨1 + i.val, hi8⟩).1 = w := by
      simpa [Nat.add_comm] using congrArg Subtype.val hi
    simpa only [labelledVertex, dif_pos hi8] using hia
  · obtain ⟨i, hi⟩ := L.p.surjective ⟨w, hwP⟩
    refine ⟨⟨3 + i.val, by omega⟩, ?_⟩
    have h3 : ¬3 + i.val < 3 := by omega
    have h8 : ¬8 + i.val < 8 := by omega
    have h13 : 8 + i.val < 13 := by omega
    unfold middleVertex
    rw [show aOnePIndex (3 + i.val) = 8 + i.val by
      simp [aOnePIndex, h3]]
    simpa [labelledVertex, h8, h13] using congrArg Subtype.val hi

theorem target_not_direct {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hFixed : fixedAOne (graphArc G L) = true) (hzLe : zCount ≤ 2)
    (t : Nat) (ht : t < 6 + zCount) :
    ¬G.Adj C.a1 (targetVertex G L t) := by
  have htIdx := targetIndex_lt t ht hzLe
  have hCore : coreArc zCount (graphArc G L) (graphPToZ G L) 0
      (aOneSecondTargetIndex t) = false := by
    by_cases h15 : aOneSecondTargetIndex t < 15
    · rw [fixedAOne, all_eq_true_iff] at hFixed
      have h := hFixed (aOneSecondTargetIndex t) h15
      have hFalse : graphArc G L 0 (aOneSecondTargetIndex t) = false := by
        have hp : (decide (1 ≤ aOneSecondTargetIndex t) &&
            decide (aOneSecondTargetIndex t ≤ 3) ||
            decide (8 ≤ aOneSecondTargetIndex t) &&
            decide (aOneSecondTargetIndex t < 13)) = false := by
          unfold aOneSecondTargetIndex
          split
          · simp; omega
          · split <;> simp <;> omega
        simpa [hp] using h
      simpa [coreArc, h15] using hFalse
    · simp [coreArc, h15]
  intro hAdj
  have hg := coreArc_graph G C L hG 0 (aOneSecondTargetIndex t)
    (by omega) htIdx
  rw [hCore] at hg
  have : decide (G.Adj (labelledVertex G L 0)
      (labelledVertex G L (aOneSecondTargetIndex t))) = false := hg.symm
  have hn := decide_eq_false_iff_not.mp this
  exact hn (by simpa [targetVertex, labelledVertex, L.a_zero] using hAdj)

theorem target_ne_aOne {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 2)
    (t : Nat) (ht : t < 6 + zCount) : targetVertex G L t ≠ C.a1 := by
  intro heq
  have hfin :
      (⟨aOneSecondTargetIndex t, targetIndex_lt t ht hzLe⟩ : Fin (15 + zCount)) =
        ⟨0, by omega⟩ := by
    apply (retainedLabelEquiv G C L hG).injective
    apply Subtype.ext
    simpa [targetVertex, retainedLabelEquiv_val, labelledVertex, L.a_zero] using heq
  have hn := Fin.ext_iff.mp hfin
  have hpos : 0 < aOneSecondTargetIndex t := by
    unfold aOneSecondTargetIndex
    split
    · omega
    · split <;> omega
  exact (Nat.ne_of_gt hpos) hn

theorem private_target_second {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hFixed : fixedAOne (graphArc G L) = true) (hzLe : zCount ≤ 2)
    (deleted target : Nat) (hd : deleted < 8) (ht : target < 6 + zCount)
    (hPrivate : aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
      deleted target = true) :
    targetVertex G L target ∈ G.secondOutNeighborFinset C.a1 := by
  simp only [aOnePrivateTarget, Bool.and_eq_true] at hPrivate
  have hArc := hPrivate.1
  rw [coreArc_graph G C L hG (aOnePIndex deleted)
    (aOneSecondTargetIndex target) (aOnePIndex_lt deleted hd)
    (targetIndex_lt target ht hzLe)] at hArc
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨middleVertex G L deleted,
    (Digraph.mem_outNeighborFinset (G := G)).mp
      (middle_mem_out G C L hG hFixed deleted hd),
    (by simpa [middleVertex, targetVertex] using hArc)⟩,
    target_not_direct G C L hG hFixed hzLe target ht,
    target_ne_aOne G C L hG hzLe target ht⟩

theorem private_count_toNat (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (deleted : Nat) (hzSmall : 6 + zCount < 256) :
    (count (6 + zCount) fun target ↦
      aOnePrivateTarget zCount arc pToZ deleted target).toNat =
      (Finset.univ.filter fun target : Fin (6 + zCount) ↦
        aOnePrivateTarget zCount arc pToZ deleted target = true).card := by
  rw [toNat_count_eq_fin_sum _ _ hzSmall]
  symm
  rw [Finset.card_filter]

set_option linter.flexible false in
theorem aOneDeletionConditions_true {zCount : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hA1Card : C.A1.card = 3)
    (hk : C.k = 3) (hr : C.r = 5) (hzLe : zCount ≤ 2)
    (hFixed : fixedAOne (graphArc G L) = true) :
    aOneDeletionConditions zCount (graphArc G L) (graphPToZ G L) = true := by
  let T := G.secondOutNeighborFinset C.a1
  have hDegree : G.outdegree C.a1 = 8 := by
    rw [Shared.outdegree_a1_eq_k_add_r G C hG, hk, hr]
  have hTCard : T.card ≤ 7 := by
    have hlt := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hs ↦ hNoSeymour ⟨C.a1, hs⟩)
    unfold Digraph.secondOutdegree at hlt
    rw [hDegree] at hlt
    exact Nat.le_of_lt_succ (by simpa [T] using hlt)
  rw [aOneDeletionConditions, all_eq_true_iff]
  intro deleted hd
  let d : Fin 8 := ⟨deleted, hd⟩
  let u := middleVertex G L deleted
  let S := (G.outNeighborFinset C.a1).erase u
  let E := G.outNeighborFinsetOf S \ (S ∪ {C.a1})
  have huOut : u ∈ G.outNeighborFinset C.a1 :=
    middle_mem_out G C L hG hFixed deleted hd
  have hau : G.Adj C.a1 u := (Digraph.mem_outNeighborFinset (G := G)).mp huOut
  have hExpansion : 7 ≤ E.card := by
    simpa [S, E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hau
  have hMiss : (T \ E).card ≤ 1 := by
    simpa [T, S, E] using Digraph.oneArcDeletion_misses_at_most_one G hBound hG
      hNoSeymour hDegree hau
  have hPrivateNotE (target : Fin (6 + zCount))
      (hPrivate : aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
        deleted target = true) : targetVertex G L target ∉ E := by
    intro htE
    rcases Finset.mem_sdiff.mp htE with ⟨htReach, _⟩
    obtain ⟨middle, hmS, hmt⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
    have hmOut : middle ∈ G.outNeighborFinset C.a1 := Finset.mem_of_mem_erase hmS
    obtain ⟨other, hother⟩ := middle_surjective G C L hG hA1Card middle hmOut
    have hne : other.val ≠ deleted := by
      intro heq
      have : middle = u := by simp [u, ← hother, heq]
      exact (Finset.mem_erase.mp hmS).1 this
    simp only [aOnePrivateTarget, Bool.and_eq_true] at hPrivate
    have hAllRaw := hPrivate.2
    rw [all_eq_true_iff] at hAllRaw
    have hAll := hAllRaw other.val other.isLt
    simp [hne] at hAll
    have hArcTrue : coreArc zCount (graphArc G L) (graphPToZ G L)
        (aOnePIndex other.val) (aOneSecondTargetIndex target.val) = true := by
      rw [coreArc_graph G C L hG _ _ (aOnePIndex_lt other.val other.isLt)
        (targetIndex_lt target.val target.isLt hzLe)]
      apply decide_eq_true
      simpa [middleVertex, targetVertex, ← hother] using hmt
    rw [hArcTrue] at hAll
    simp at hAll
  let I := Finset.univ.filter fun target : Fin (6 + zCount) ↦
    aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L) deleted target = true
  have hImageSubset : I.image (fun target : Fin (6 + zCount) ↦
      targetVertex G L target.val) ⊆ T \ E := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨target, htI, rfl⟩
    have ht := (Finset.mem_filter.mp htI).2
    exact Finset.mem_sdiff.mpr ⟨
      private_target_second G C L hG hFixed hzLe deleted target hd target.isLt ht,
      hPrivateNotE target ht⟩
  have hCountOne : (count (6 + zCount) fun target ↦
      aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
        deleted target).toNat ≤ 1 := by
    rw [private_count_toNat zCount _ _ deleted (by omega)]
    change I.card ≤ 1
    rw [← Finset.card_image_of_injective I
      (targetVertex_injective G C L hG hzLe)]
    exact (Finset.card_le_card hImageSubset).trans hMiss
  by_cases hReached : aOneDeletedReached (graphArc G L) deleted = true
  · simp only [aOneDeletionCondition, BitVec.ule_eq_decide, decide_eq_true_eq]
    change (count (6 + zCount) fun target ↦
      aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
        deleted target).toNat ≤ (bitCount (aOneDeletedReached
          (graphArc G L) deleted)).toNat
    rw [hReached]
    simpa [bitCount] using hCountOne
  · have hReachedFalse := Bool.eq_false_of_not_eq_true hReached
    have huNotE : u ∉ E := by
      intro huE
      rcases Finset.mem_sdiff.mp huE with ⟨huReach, _⟩
      obtain ⟨middle, hmS, hmu⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp huReach
      have hmOut : middle ∈ G.outNeighborFinset C.a1 := Finset.mem_of_mem_erase hmS
      obtain ⟨other, hother⟩ := middle_surjective G C L hG hA1Card middle hmOut
      have hne : other.val ≠ deleted := by
        intro heq
        have : middle = u := by simp [u, ← hother, heq]
        exact (Finset.mem_erase.mp hmS).1 this
      have hArcTrue : graphArc G L (aOnePIndex other.val)
          (aOnePIndex deleted) = true := by
        have hCoreTrue : coreArc zCount (graphArc G L) (graphPToZ G L)
            (aOnePIndex other.val) (aOnePIndex deleted) = true := by
          rw [coreArc_graph G C L hG _ _ (aOnePIndex_lt other.val other.isLt)
            (by exact (aOnePIndex_lt deleted hd).trans (by omega))]
          apply decide_eq_true
          simpa [middleVertex, ← hother, u] using hmu
        have hs13 := aOnePIndex_lt other.val other.isLt
        have ht15 : aOnePIndex deleted < 15 :=
          (aOnePIndex_lt deleted hd).trans (by omega)
        by_cases hs8 : aOnePIndex other.val < 8
        · simpa [coreArc, hs8, ht15] using hCoreTrue
        · simpa [coreArc, hs8, hs13, ht15] using hCoreTrue
      have : aOneDeletedReached (graphArc G L) deleted = true := by
        rw [aOneDeletedReached, any_eq_true_iff]
        exact ⟨other.val, other.isLt, by simp [hne, hArcTrue]⟩
      exact hReached this
    have hESubset : E ⊆ T := by
      intro w hwE
      rcases Finset.mem_sdiff.mp hwE with ⟨hwReach, hwOutside⟩
      obtain ⟨middle, hmS, hmw⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
      have hwmid : G.Adj C.a1 middle :=
        (Digraph.mem_outNeighborFinset (G := G)).mp (Finset.mem_of_mem_erase hmS)
      have hwNeU : w ≠ u := fun hwu ↦ huNotE (hwu ▸ hwE)
      have hwNotS : w ∉ S := fun hwS ↦ hwOutside (Finset.mem_union_left _ hwS)
      have hwNotDirect : ¬G.Adj C.a1 w := by
        intro haw
        exact hwNotS (Finset.mem_erase.mpr ⟨hwNeU,
          (Digraph.mem_outNeighborFinset (G := G)).mpr haw⟩)
      have hwNeA : w ≠ C.a1 := by
        intro hw
        subst w
        exact hwOutside (Finset.mem_union_right _ (Finset.mem_singleton_self C.a1))
      rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨middle, hwmid, hmw⟩, hwNotDirect, hwNeA⟩
    have hNoPrivate : ∀ target : Fin (6 + zCount),
        aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
          deleted target = false := by
      intro target
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have htNotE := hPrivateNotE target ht
      have hUnion : E ∪ {targetVertex G L target} ⊆ T :=
        Finset.union_subset hESubset (by
          intro v hv
          rw [Finset.mem_singleton] at hv
          subst v
          exact private_target_second G C L hG hFixed hzLe deleted
            target hd target.isLt ht)
      have hCard := Finset.card_le_card hUnion
      have hUnionCard : (E ∪ {targetVertex G L target}).card = E.card + 1 := by
        rw [Finset.card_union_of_disjoint]
        · simp
        · rw [Finset.disjoint_left]
          intro v hvE hvt
          exact htNotE (Finset.mem_singleton.mp hvt ▸ hvE)
      rw [hUnionCard] at hCard
      omega
    have hCountZero : (count (6 + zCount) fun target ↦
        aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
          deleted target).toNat = 0 := by
      rw [toNat_count_eq_fin_sum _ _ (by omega)]
      apply Finset.sum_eq_zero
      intro target _
      simp [hNoPrivate target]
    simp only [aOneDeletionCondition, BitVec.ule_eq_decide, decide_eq_true_eq]
    change (count (6 + zCount) fun target ↦
      aOnePrivateTarget zCount (graphArc G L) (graphPToZ G L)
        deleted target).toNat ≤ (bitCount (aOneDeletedReached
          (graphArc G L) deleted)).toNat
    rw [hReachedFalse, hCountZero]
    simp [bitCount]

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.DeletionBridge
