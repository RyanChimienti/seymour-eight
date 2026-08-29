import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.AugmentedBridge
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.SharpDefs

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.SharpAugmentedBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  AugmentedBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem qAnonymousSharpLower_le_card (C : G.LocalConfiguration)
    (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    (qAnonymousSharpLower (graphArc G L)).toNat ≤
      (qAnonymousSet G C).card := by
  have hSixteen := sixteen_le_q_retained_add_twice_anonymous G C L hMin
  have hUpper := q_retained_upper G C L hG hHCard hFixed
  have hHQ := totalHToQ_toNat G C L hHCard
  have hPQ := totalPToQ_toNat G C L hHCard
  have hQCard : C.Q.card = 2 := by
    simpa using (Fintype.card_congr L.q).symm
  have hHCap := edgeCount_le_card_mul_card G C.H C.Q
  have hPCap := edgeCount_le_card_mul_card G C.P C.Q
  have hPCard : C.P.card = 5 := by
    simpa using (Fintype.card_congr L.p).symm
  have h14 : (14 : BitVec 8).toNat = 14 := by decide
  have h10 : (10 : BitVec 8).toNat = 10 := by decide
  rw [hHCard, hQCard] at hHCap
  rw [hPCard, hQCard] at hPCap
  have hHLe : totalHToQ (graphArc G L) ≤ (14 : BitVec 8) := by
    rw [BitVec.le_def, hHQ, h14]
    omega
  have hPLe : totalPToQ (graphArc G L) ≤ (10 : BitVec 8) := by
    rw [BitVec.le_def, hPQ, h10]
    omega
  have hDefBound : (hQDefect 2 (graphArc G L)).toNat ≤ 14 := by
    change ((14 : BitVec 8) - totalHToQ (graphArc G L)).toNat ≤ 14
    rw [BitVec.toNat_sub_of_le hHLe, h14]
    omega
  have hMissBound : (qMissing (graphArc G L)).toNat ≤ 10 := by
    rw [qMissing, BitVec.toNat_sub_of_le hPLe, h10]
    omega
  have hAddSmall : (hQDefect 2 (graphArc G L)).toNat +
      (qMissing (graphArc G L)).toNat < 256 := by omega
  let d := hQDefect 2 (graphArc G L) + qMissing (graphArc G L)
  have hdNat : d.toNat = (hQDefect 2 (graphArc G L)).toNat +
      (qMissing (graphArc G L)).toNat := by
    dsimp [d]
    simpa using Nat.mod_eq_of_lt hAddSmall
  rw [← hdNat] at hUpper
  have hn0 : (0 : BitVec 8).toNat = 0 := by decide
  have hn1 : (1 : BitVec 8).toNat = 1 := by decide
  have hn2 : (2 : BitVec 8).toNat = 2 := by decide
  have hn3 : (3 : BitVec 8).toNat = 3 := by decide
  have hn4 : (4 : BitVec 8).toNat = 4 := by decide
  have hn5 : (5 : BitVec 8).toNat = 5 := by decide
  have hn6 : (6 : BitVec 8).toNat = 6 := by decide
  have hn8 : (8 : BitVec 8).toNat = 8 := by decide
  have hn10 : (10 : BitVec 8).toNat = 10 := by decide
  change (if d == 0 then (6 : BitVec 8) else if d.ule 2 then 5
    else if d.ule 4 then 4 else if d.ule 6 then 3
    else if d.ule 8 then 2 else if d.ule 10 then 1 else 0).toNat ≤ _
  split <;> rename_i h0
  · simp only [beq_iff_eq] at h0
    have hd := congrArg BitVec.toNat h0
    rw [hn0] at hd
    rw [hn6]
    omega
  split <;> rename_i h2
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h2
    rw [hn2] at h2
    rw [hn5]
    omega
  split <;> rename_i h4
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h4
    rw [hn4] at h4
    rw [hn4]
    omega
  split <;> rename_i h6
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h6
    rw [hn6] at h6
    rw [hn3]
    omega
  split <;> rename_i h8
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h8
    rw [hn8] at h8
    rw [hn2]
    omega
  split <;> rename_i h10'
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h10'
    rw [hn10] at h10'
    rw [hn1]
    omega
  · simp

theorem augmented_projected_sharp_le_second (C : G.LocalConfiguration)
    (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true)
    (source : Nat) (hs : source < 13)
    (hBoth : (if source < 8 then reachesBothQFromA (graphArc G L) source
      else reachesBothQFromP (graphArc G L) (source - 8)) = true) :
    (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) source).toNat +
        (qAnonymousSharpLower (graphArc G L)).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  let R := (retainedVertexSet G C).filter fun v ↦
    v ∈ G.secondOutNeighborFinset (labelledVertex G L source)
  let U := qAnonymousSet G C
  have hProjected := projectedSecondCount_le_retained_second_card G C L hG
    (by omega) source hs
  have hLower := qAnonymousSharpLower_le_card G C L hG hMin hHCard hFixed
  have hDis : Disjoint R U := by
    rw [Finset.disjoint_left]
    intro v hvR hvU
    exact (Finset.mem_sdiff.mp hvU).2 (Finset.mem_filter.mp hvR).1
  have hUnion : R ∪ U ⊆
      G.secondOutNeighborFinset (labelledVertex G L source) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvR | hvU
    · exact (Finset.mem_filter.mp hvR).2
    · exact qAnonymous_mem_second G C L hG source hs hBoth hvU
  dsimp [R, U] at hProjected hLower hDis hUnion ⊢
  unfold Digraph.secondOutdegree
  calc
    _ ≤ ((retainedVertexSet G C).filter fun v ↦
          v ∈ G.secondOutNeighborFinset (labelledVertex G L source)).card +
        (qAnonymousSet G C).card := add_le_add hProjected hLower
    _ = (((retainedVertexSet G C).filter fun v ↦
          v ∈ G.secondOutNeighborFinset (labelledVertex G L source)) ∪
        qAnonymousSet G C).card := (Finset.card_union_of_disjoint hDis).symm
    _ ≤ _ := Finset.card_le_card hUnion

theorem qAnonymousSharpLower_toNat_le_six (arc : Nat → Nat → Bool) :
    (qAnonymousSharpLower arc).toNat ≤ 6 := by
  simp only [qAnonymousSharpLower]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]

theorem projected_add_qSharp_toNat (arc pToZ : Nat → Nat → Bool)
    (source : Nat) :
    (projectedSecondCount 1 arc pToZ source + qAnonymousSharpLower arc).toNat =
      (projectedSecondCount 1 arc pToZ source).toNat +
        (qAnonymousSharpLower arc).toNat := by
  change (count 16 (projectedSecond 1 arc pToZ source) +
    qAnonymousSharpLower arc).toNat =
      (count 16 (projectedSecond 1 arc pToZ source)).toNat +
        (qAnonymousSharpLower arc).toNat
  have hp := count_toNat_le 16 (projectedSecond 1 arc pToZ source) (by omega)
  have hq := qAnonymousSharpLower_toNat_le_six arc
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem aNonSeymourSharp_true (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    aNonSeymourSharp (graphArc G L) (graphPToZ G L) = true := by
  rw [aNonSeymourSharp, all_eq_true_iff]
  intro a ha
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hDegree := A_outdegree_eq_blocks G C L hG a ha
  have hAO := aOut_toNat G C L a ha
  have hBO := aBOut_toNat G C L a ha
  have hDegreeNat : (aDegree (graphArc G L) a).toNat =
      G.outdegree (L.a ⟨a, ha⟩).1 := by
    rw [aDegree, BitVec.toNat_add, hAO, hBO,
      Nat.mod_eq_of_lt (by
        have hA := Finset.card_le_card (Finset.filter_subset
          (G.Adj (L.a ⟨a, ha⟩).1) C.A)
        have hB := Finset.card_le_card (Finset.filter_subset
          (G.Adj (L.a ⟨a, ha⟩).1) C.B)
        have hACard : C.A.card = 8 := by
          simpa using (Fintype.card_congr L.a).symm
        have hBCard : C.B.card = 7 := by
          rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
          have hp : C.P.card = 5 := by
            simpa using (Fintype.card_congr L.p).symm
          have hq : C.Q.card = 2 := by
            simpa using (Fintype.card_congr L.q).symm
          change C.P.card + C.Q.card = 7
          omega
        change directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card at hA
        change directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card at hB
        omega), hDegree]
  by_cases hBoth : reachesBothQFromA (graphArc G L) a = true
  · have hAug := augmented_projected_sharp_le_second G C L hG hMin
      hHCard hFixed a (by omega) (by simpa [ha] using hBoth)
    have hAug' :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat +
            (qAnonymousSharpLower (graphArc G L)).toNat ≤
          G.secondOutdegree (L.a ⟨a, ha⟩).1 := by
      simpa [labelledVertex, ha] using hAug
    rw [if_pos hBoth, projected_add_qSharp_toNat, hDegreeNat]
    exact hAug'.trans_lt (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨_, h⟩))
  · rw [if_neg hBoth]
    have hZero :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a +
          (0 : BitVec 8)).toNat =
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat := by
      exact congrArg BitVec.toNat (bitvec_add_zero _)
    rw [hZero, hDegreeNat]
    have hProj := projectedSecondCount_le_graph_retained G C L hG (by omega) a
      (by omega)
    have hProj' :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat ≤
          G.secondOutdegree (L.a ⟨a, ha⟩).1 := by
      simpa [labelledVertex, ha] using hProj
    exact hProj'.trans_lt
      (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun h ↦ hNoSeymour ⟨_, h⟩))

theorem pNonSeymourSharp_true (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    pNonSeymourSharp (graphArc G L) (graphPToZ G L) = true := by
  rw [pNonSeymourSharp, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hDegree := pDegree_toNat G C L hG hHCard (by omega) p hp
  by_cases hBoth : reachesBothQFromP (graphArc G L) p = true
  · have hAug := augmented_projected_sharp_le_second G C L hG hMin
      hHCard hFixed (8 + p) (by omega) (by simpa using hBoth)
    have hAug' :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) (8 + p)).toNat +
            (qAnonymousSharpLower (graphArc G L)).toNat ≤
          G.secondOutdegree (L.p ⟨p, hp⟩).1 := by
      simpa [labelledVertex, show ¬8 + p < 8 by omega,
        show 8 + p < 13 by omega] using hAug
    rw [if_pos hBoth, projected_add_qSharp_toNat, hDegree]
    exact hAug'.trans_lt (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨_, h⟩))
  · rw [if_neg hBoth]
    have hZero :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) (8 + p) +
          (0 : BitVec 8)).toNat =
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) (8 + p)).toNat := by
      exact congrArg BitVec.toNat (bitvec_add_zero _)
    rw [hZero, hDegree]
    have hProj := projectedSecondCount_le_graph_retained G C L hG (by omega)
      (8 + p) (by omega)
    have hProj' :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) (8 + p)).toNat ≤
          G.secondOutdegree (L.p ⟨p, hp⟩).1 := by
      simpa [labelledVertex, show ¬8 + p < 8 by omega,
        show 8 + p < 13 by omega] using hProj
    exact hProj'.trans_lt
      (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun h ↦ hNoSeymour ⟨_, h⟩))

theorem sharpResidualCore_true (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true)
    (hCommon : commonCore 2 1 (graphArc G L) (graphPToZ G L) = true) :
    sharpResidualCore (graphArc G L) (graphPToZ G L) = true := by
  simp [sharpResidualCore, hCommon,
    aNonSeymourSharp_true G C L hG hMin hNoSeymour hHCard hFixed,
    pNonSeymourSharp_true G C L hG hMin hNoSeymour hHCard hFixed]

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.SharpAugmentedBridge
