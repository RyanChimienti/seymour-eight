import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.AugmentedBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat = (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      norm_num

set_option maxHeartbeats 2000000 in
/-- Targets reached from `Q` but omitted from the retained finite model. -/
def qAnonymousSet (C : G.LocalConfiguration) : Finset V :=
  G.outNeighborFinsetOf C.Q \ retainedVertexSet G C

set_option maxHeartbeats 2000000 in
theorem q_outgoingCaptured (C : G.LocalConfiguration) (q : V) (hq : q ∈ C.Q) :
    ∀ v, G.Adj q v → v ∈ retainedVertexSet G C ∪ qAnonymousSet G C := by
  intro v hqv
  by_cases hv : v ∈ retainedVertexSet G C
  · exact Finset.mem_union_left _ hv
  · apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr ⟨q, hq, hqv⟩, hv⟩

set_option maxHeartbeats 2000000 in
theorem q_outdegree_split (C : G.LocalConfiguration) (q : V) (hq : q ∈ C.Q) :
    G.outdegree q = directCount G (retainedVertexSet G C) q +
      directCount G (qAnonymousSet G C) q := by
  have hDis : Disjoint (retainedVertexSet G C) (qAnonymousSet G C) := by
    rw [Finset.disjoint_left]
    intro v hvR hvU
    exact (Finset.mem_sdiff.mp hvU).2 hvR
  have hCap : G.outNeighborFinset q ⊆
      retainedVertexSet G C ∪ qAnonymousSet G C := by
    intro v hv
    exact q_outgoingCaptured G C q hq v
      ((Digraph.mem_outNeighborFinset (G := G)).mp hv)
  rw [outdegree_eq_directCount_of_captured G
      (retainedVertexSet G C ∪ qAnonymousSet G C) q
      hCap,
    directCount_union_of_disjoint G _ _ _ hDis]

set_option maxHeartbeats 2000000 in
theorem sixteen_le_q_retained_add_twice_anonymous (C : G.LocalConfiguration)
    (L : Labels G 1 C) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    16 ≤ edgeCount G C.Q (retainedVertexSet G C) +
      2 * (qAnonymousSet G C).card := by
  have hqCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hEach (i : Fin 2) := q_outdegree_split G C (L.q i).1 (L.q i).2
  have hAnon (i : Fin 2) :
      directCount G (qAnonymousSet G C) (L.q i).1 ≤ (qAnonymousSet G C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hMinSum := add_le_add (hMin (L.q 0).1) (hMin (L.q 1).1)
  rw [edgeCount_eq_sum_fin G C.Q (retainedVertexSet G C) L.q]
  simp only [Fin.sum_univ_two]
  rw [hEach 0, hEach 1] at hMinSum
  have h0 := hAnon 0
  have h1 := hAnon 1
  omega

set_option maxHeartbeats 2000000 in
theorem totalHToQ_toNat (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hHCard : C.H.card = 7) :
    (totalHToQ (graphArc G L)).toNat = edgeCount G C.H C.Q := by
  have hEach : ∀ i : Fin 7,
      (count 2 fun q ↦ aToQ (graphArc G L) (1 + i) q).toNat =
        directCount G C.Q (L.a ⟨i.val + 1, by omega⟩).1 := by
    intro i
    rw [toNat_count_eq_fin_sum 2 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Q L.q _
    intro q
    rw [aToQ_graph G L (1 + i) q (by omega) q.isLt]
    simp [Nat.add_comm]
  rw [totalHToQ, toNat_sumCount, ← Fin.sum_univ_eq_sum_range]
  have hEq : (∑ i : Fin 7,
      (count 2 fun q ↦ aToQ (graphArc G L) (1 + i) q).toNat) =
      ∑ i : Fin 7, directCount G C.Q (hLabelEquiv G C L hHCard i).1 := by
    apply Finset.sum_congr rfl
    intro i _
    simpa [hLabelEquiv_val, Nat.add_comm] using hEach i
  have hSum : (∑ i : Fin 7,
      (count 2 fun q ↦ aToQ (graphArc G L) (1 + i) q).toNat) =
      edgeCount G C.H C.Q := by
    rw [hEq, edgeCount_eq_sum_fin G C.H C.Q (hLabelEquiv G C L hHCard)]
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.Q
  have hqCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  rw [hHCard, hqCard] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
theorem totalPToQ_toNat (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hHCard : C.H.card = 7) :
    (totalPToQ (graphArc G L)).toNat = edgeCount G C.P C.Q := by
  have hEach : ∀ i : Fin 5,
      (pQOut (graphArc G L) i).toNat = directCount G C.Q (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hHCard (by omega) i i.isLt).2.2.1
  rw [totalPToQ, toNat_sumCount, ← Fin.sum_univ_eq_sum_range]
  have hEq : (∑ i : Fin 5, (pQOut (graphArc G L) i).toNat) =
      ∑ i : Fin 5, directCount G C.Q (L.p i).1 := by
    apply Finset.sum_congr rfl
    intro i _
    exact hEach i
  have hSum : (∑ i : Fin 5, (pQOut (graphArc G L) i).toNat) =
      edgeCount G C.P C.Q := by
    rw [hEq, edgeCount_eq_sum_fin G C.P C.Q L.p]
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.Q
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  rw [hp, hq] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
theorem edgeCount_A_Q_eq_H_Q (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    edgeCount G C.A C.Q = edgeCount G C.H C.Q := by
  have hDis : Disjoint ({C.a1} : Finset V) C.H := by
    rw [Finset.disjoint_left]
    intro v hv hs
    have hvEq : v = C.a1 := Finset.mem_singleton.mp hv
    subst v
    obtain ⟨i, hi⟩ := (hLabelEquiv G C L hHCard).surjective ⟨C.a1, hs⟩
    have ha : (L.a ⟨i.val + 1, by omega⟩).1 = C.a1 := by
      simpa using congrArg Subtype.val hi
    have hzero : (L.a (0 : Fin 8)).1 = C.a1 := L.a_zero
    have hfin : (⟨i.val + 1, by omega⟩ : Fin 8) = 0 := by
      apply L.a.injective
      exact Subtype.ext (ha.trans hzero.symm)
    have := Fin.ext_iff.mp hfin
    simp at this
  have hSub : {C.a1} ∪ C.H ⊆ C.A := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hvEq : v = C.a1 := Finset.mem_singleton.mp hv
      subst v
      exact Digraph.LocalConfiguration.a1_mem_A (G := G) C
    · exact Digraph.LocalConfiguration.H_subset_A (G := G) C hv
  have hAH : C.A = {C.a1} ∪ C.H := by
    symm
    apply Finset.eq_of_subset_of_card_le hSub
    rw [Finset.card_union_of_disjoint hDis, Finset.card_singleton, hHCard]
    have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    omega
  rw [hAH]
  unfold edgeCount
  rw [Finset.sum_union hDis]
  have hZero : edgeCount G {C.a1} C.Q = 0 := by
    unfold edgeCount
    simp only [Finset.sum_singleton]
    unfold directCount CertificateBridge.internalFirstNeighbors
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q hq hAdj
    obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hq⟩
    rw [fixedAOne, all_eq_true_iff] at hFixed
    have h0 := hFixed (13 + i.val) (by omega)
    have hn : decide (G.Adj C.a1 q) = false := by
      have hi3 : ¬13 + i.val ≤ 3 := by omega
      simpa [graphArc, L.a_zero, show ¬13 + i.val < 8 by omega,
        show ¬13 + i.val < 13 by omega, show 13 + i.val < 15 by omega,
        congrArg Subtype.val hi, hi3] using h0
    exact (decide_eq_false_iff_not.mp hn) hAdj
  simpa [edgeCount, hZero]

set_option maxHeartbeats 2000000 in
theorem q_retained_upper (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    edgeCount G C.Q (retainedVertexSet G C) ≤
      (hQDefect 2 (graphArc G L)).toNat +
        (qMissing (graphArc G L)).toNat + 5 := by
  have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = 1 := by
    simpa using (Fintype.card_congr L.z).symm
  have hAQ := cross_edgeCount_add_reverse_le G C.A C.Q hG
  have hPQ := cross_edgeCount_add_reverse_le G C.P C.Q hG
  have hQQ := internal_edgeCount_le_choose_two G C.Q hG
  have hQZ := edgeCount_le_card_mul_card G C.Q (externalTargets G C)
  rw [hACard, hQCard] at hAQ
  rw [hPCard, hQCard] at hPQ
  rw [hQCard] at hQQ
  rw [hQCard, hZCard] at hQZ
  simp [Nat.choose] at hQQ
  have hAQEq := edgeCount_A_Q_eq_H_Q G C L hHCard hFixed
  have hHQ := totalHToQ_toNat G C L hHCard
  have hPQEq := totalPToQ_toNat G C L hHCard
  have h14 : (14 : BitVec 8).toNat = 14 := by decide
  have h10 : (10 : BitVec 8).toNat = 10 := by decide
  have hHDef : (hQDefect 2 (graphArc G L)).toNat =
      14 - edgeCount G C.A C.Q := by
    have hCap := edgeCount_le_card_mul_card G C.H C.Q
    rw [hHCard, hQCard] at hCap
    have hLe : totalHToQ (graphArc G L) ≤ (14 : BitVec 8) := by
      rw [BitVec.le_def, hHQ, h14]
      omega
    change ((14 : BitVec 8) - totalHToQ (graphArc G L)).toNat = _
    rw [BitVec.toNat_sub_of_le hLe, h14, hHQ, ← hAQEq]
  have hQMiss : (qMissing (graphArc G L)).toNat =
      10 - edgeCount G C.P C.Q := by
    have hCap := edgeCount_le_card_mul_card G C.P C.Q
    rw [hPCard, hQCard] at hCap
    have hLe : totalPToQ (graphArc G L) ≤ (10 : BitVec 8) := by
      rw [BitVec.le_def, hPQEq, h10]
      omega
    rw [qMissing, BitVec.toNat_sub_of_le hLe, h10, hPQEq]
  have hRetained : edgeCount G C.Q (retainedVertexSet G C) =
      edgeCount G C.Q C.A + edgeCount G C.Q C.P + edgeCount G C.Q C.Q +
        edgeCount G C.Q (externalTargets G C) := by
    -- The four retained blocks are pairwise disjoint.
    have hAP : Disjoint C.A C.P := Finset.disjoint_of_subset_right
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
    have hAllZ : Disjoint (C.A ∪ C.P ∪ C.Q) (externalTargets G C) := by
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
    simp only [retainedVertexSet]
    rw [edgeCount_union_of_disjoint G C.Q (C.A ∪ C.P ∪ C.Q)
      (externalTargets G C) hAllZ,
      edgeCount_union_of_disjoint G C.Q (C.A ∪ C.P) C.Q hAPQ,
      edgeCount_union_of_disjoint G C.Q C.A C.P hAP]
  rw [hRetained, hHDef, hQMiss]
  omega

set_option maxHeartbeats 2000000 in
theorem qAnonymousLower_le_card (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hFixed : fixedAOne (graphArc G L) = true) :
    (qAnonymousLower 2 (graphArc G L)).toNat ≤ (qAnonymousSet G C).card := by
  have hSixteen := sixteen_le_q_retained_add_twice_anonymous G C L hMin
  have hUpper := q_retained_upper G C L hG hHCard hFixed
  have hHQ := totalHToQ_toNat G C L hHCard
  have hPQ := totalPToQ_toNat G C L hHCard
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hHCap := edgeCount_le_card_mul_card G C.H C.Q
  have hPCap := edgeCount_le_card_mul_card G C.P C.Q
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
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
  change (if d == 0 then (5 : BitVec 8) else if d.ule 2 then 4
    else if d.ule 4 then 3 else if d.ule 6 then 2
    else if d.ule 8 then 1 else 0).toNat ≤ _
  split <;> rename_i h0
  · simp only [beq_iff_eq] at h0
    have hd := congrArg BitVec.toNat h0
    rw [hn0] at hd
    rw [hn5]
    omega
  split <;> rename_i h2
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h2
    rw [hn2] at h2
    rw [hn4]
    omega
  split <;> rename_i h4
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h4
    rw [hn4] at h4
    rw [hn3]
    omega
  split <;> rename_i h6
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h6
    rw [hn6] at h6
    rw [hn2]
    omega
  split <;> rename_i h8
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h8
    rw [hn8] at h8
    rw [hn1]
    omega
  · simp

set_option maxHeartbeats 2000000 in
theorem labelled_outgoing_retained {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (source : Nat)
    (hs : source < 13) :
    G.outNeighborFinset (labelledVertex G L source) ⊆ retainedVertexSet G C := by
  intro v hv
  have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hv
  by_cases hsA : source < 8
  · have hv' : v ∈ G.outNeighborFinset (L.a ⟨source, hsA⟩).1 := by
      simpa [labelledVertex, hsA] using hv
    have hCap :=
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG (L.a ⟨source, hsA⟩).1 (L.a _).2 hv'
    rcases Finset.mem_union.mp hCap with hvA | hvB
    · simp [retainedVertexSet, hvA]
    · rw [← Digraph.LocalConfiguration.P_union_Q] at hvB
      rcases Finset.mem_union.mp hvB with hvP | hvQ
      · simp [retainedVertexSet, hvP]
      · simp [retainedVertexSet, hvQ]
  · have hCap := BSixKThree.P_outgoingCaptured_general G C hG
      (L.p ⟨source - 8, by omega⟩).1 (L.p _).2 (by
        simpa [labelledVertex, hsA, hs] using hv)
    rcases Finset.mem_union.mp hCap with hHPQ | hvZ
    · rcases Finset.mem_union.mp hHPQ with hHP | hvQ
      · rcases Finset.mem_union.mp hHP with hvH | hvP
        · simp [retainedVertexSet,
            Digraph.LocalConfiguration.H_subset_A (G := G) C hvH]
        · simp [retainedVertexSet, hvP]
      · simp [retainedVertexSet, hvQ]
    · simp [retainedVertexSet, hvZ]

set_option maxHeartbeats 2000000 in
theorem reachesBothQ_adj {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 13)
    (hBoth : (if source < 8 then reachesBothQFromA (graphArc G L) source
      else reachesBothQFromP (graphArc G L) (source - 8)) = true) :
    ∀ q ∈ C.Q, G.Adj (labelledVertex G L source) q := by
  intro q hq
  obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hq⟩
  have hqVal : (L.q i).1 = q := congrArg Subtype.val hi
  by_cases hsA : source < 8
  · simp only [hsA, if_true, reachesBothQFromA, Bool.and_eq_true] at hBoth
    have hiCases : i = 0 ∨ i = 1 := by
      by_cases hi0 : i.val = 0
      · left; exact Fin.ext hi0
      · right; apply Fin.ext; omega
    rcases hiCases with rfl | rfl
    · rw [← hqVal]
      apply of_decide_eq_true
      simpa [labelledVertex, hsA] using hBoth.1
    · rw [← hqVal]
      apply of_decide_eq_true
      simpa [labelledVertex, hsA] using hBoth.2
  · simp only [hsA, if_false, reachesBothQFromP, Bool.and_eq_true] at hBoth
    have hiCases : i = 0 ∨ i = 1 := by
      by_cases hi0 : i.val = 0
      · left; exact Fin.ext hi0
      · right; apply Fin.ext; omega
    rcases hiCases with rfl | rfl
    · rw [← hqVal]
      have hb := hBoth.1
      rw [pToQ_graph G L (source - 8) 0 (by omega) (by omega)] at hb
      simpa [labelledVertex, hsA, hs] using of_decide_eq_true hb
    · rw [← hqVal]
      have hb := hBoth.2
      rw [pToQ_graph G L (source - 8) 1 (by omega) (by omega)] at hb
      simpa [labelledVertex, hsA, hs] using of_decide_eq_true hb

set_option maxHeartbeats 2000000 in
theorem qAnonymous_mem_second {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (source : Nat)
    (hs : source < 13)
    (hBoth : (if source < 8 then reachesBothQFromA (graphArc G L) source
      else reachesBothQFromP (graphArc G L) (source - 8)) = true) :
    qAnonymousSet G C ⊆
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  intro v hv
  have hvOutside := (Finset.mem_sdiff.mp hv).2
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hv).1 with ⟨q, hqQ, hqv⟩
  have hsq := reachesBothQ_adj G C L source hs hBoth q hqQ
  have hNot : ¬G.Adj (labelledVertex G L source) v := by
    intro hsv
    exact hvOutside (labelled_outgoing_retained G C L hG source hs
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv))
  have hne : v ≠ labelledVertex G L source := by
    intro heq
    apply hvOutside
    rw [heq]
    by_cases hsA : source < 8
    · simp [retainedVertexSet, labelledVertex, hsA, (L.a _).2]
    · simp [retainedVertexSet, labelledVertex, hsA, hs, (L.p _).2]
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨q, hsq, hqv⟩, hNot, hne⟩

set_option maxHeartbeats 2000000 in
theorem augmented_projected_le_second (C : G.LocalConfiguration)
    (L : Labels G 1 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true)
    (source : Nat) (hs : source < 13)
    (hBoth : (if source < 8 then reachesBothQFromA (graphArc G L) source
      else reachesBothQFromP (graphArc G L) (source - 8)) = true) :
    (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) source).toNat +
        (qAnonymousLower 2 (graphArc G L)).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  let R := (retainedVertexSet G C).filter fun v ↦
    v ∈ G.secondOutNeighborFinset (labelledVertex G L source)
  let U := qAnonymousSet G C
  have hProjected := projectedSecondCount_le_retained_second_card G C L hG
    (by omega) source hs
  have hLower := qAnonymousLower_le_card G C L hG hMin hHCard hFixed
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

set_option maxHeartbeats 2000000 in
theorem count_toNat_le (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat ≤ n := by
  rw [toNat_count_eq_fin_sum n f hn]
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases f i <;> decide
    _ = n := by simp

set_option maxHeartbeats 2000000 in
theorem qAnonymousLower_toNat_le_five (arc : Nat → Nat → Bool) :
    (qAnonymousLower 2 arc).toNat ≤ 5 := by
  simp only [qAnonymousLower, beq_self_eq_true, if_true]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]
  split <;> simp_all [BitVec.toNat_ofNat]

set_option maxHeartbeats 2000000 in
theorem projected_add_qLower_toNat (arc pToZ : Nat → Nat → Bool)
    (source : Nat) :
    (projectedSecondCount 1 arc pToZ source + qAnonymousLower 2 arc).toNat =
      (projectedSecondCount 1 arc pToZ source).toNat +
        (qAnonymousLower 2 arc).toNat := by
  change (count 16 (projectedSecond 1 arc pToZ source) +
    qAnonymousLower 2 arc).toNat =
      (count 16 (projectedSecond 1 arc pToZ source)).toNat +
        (qAnonymousLower 2 arc).toNat
  have hp := count_toNat_le 16 (projectedSecond 1 arc pToZ source) (by omega)
  have hq := qAnonymousLower_toNat_le_five arc
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
theorem bitvec_add_zero (x : BitVec 8) : x + 0 = x := by
  bv_decide

set_option maxHeartbeats 2000000 in
theorem aNonSeymour_true (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    aNonSeymour 2 1 (graphArc G L) (graphPToZ G L) = true := by
  rw [aNonSeymour, all_eq_true_iff]
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
        have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
        have hBCard : C.B.card = 7 := by
          rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
          have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
          have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
          change C.P.card + C.Q.card = 7
          omega
        change directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card at hA
        change directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card at hB
        omega), hDegree]
  by_cases hBoth : reachesBothQFromA (graphArc G L) a = true
  · have hAug := augmented_projected_le_second G C L hG hMin hHCard hFixed
      a (by omega) (by simpa [ha] using hBoth)
    have hAug' :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) a).toNat +
            (qAnonymousLower 2 (graphArc G L)).toNat ≤
          G.secondOutdegree (L.a ⟨a, ha⟩).1 := by
      simpa [labelledVertex, ha] using hAug
    rw [if_pos hBoth]
    rw [projected_add_qLower_toNat, hDegreeNat]
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

set_option maxHeartbeats 2000000 in
theorem pNonSeymour_true (C : G.LocalConfiguration) (L : Labels G 1 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hFixed : fixedAOne (graphArc G L) = true) :
    pNonSeymour 2 1 (graphArc G L) (graphPToZ G L) = true := by
  rw [pNonSeymour, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hDegree := pDegree_toNat G C L hG hHCard (by omega) p hp
  by_cases hBoth : reachesBothQFromP (graphArc G L) p = true
  · have hAug := augmented_projected_le_second G C L hG hMin hHCard hFixed
      (8 + p) (by omega) (by simpa using hBoth)
    have hAug' :
        (projectedSecondCount 1 (graphArc G L) (graphPToZ G L) (8 + p)).toNat +
            (qAnonymousLower 2 (graphArc G L)).toNat ≤
          G.secondOutdegree (L.p ⟨p, hp⟩).1 := by
      simpa [labelledVertex, show ¬8 + p < 8 by omega,
        show 8 + p < 13 by omega] using hAug
    rw [if_pos hBoth, projected_add_qLower_toNat, hDegree]
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

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.AugmentedBridge
