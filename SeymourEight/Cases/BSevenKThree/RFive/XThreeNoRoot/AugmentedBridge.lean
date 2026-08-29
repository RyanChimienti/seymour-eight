import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.AugmentedBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat = (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      norm_num

/-- Targets reached from `Q` but omitted from the retained finite model. -/
def qAnonymousSet (C : G.LocalConfiguration) : Finset V :=
  G.outNeighborFinsetOf C.Q \ retainedVertexSet G C

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
    by_cases hvR : v ∈ retainedVertexSet G C
    · exact Finset.mem_union_left _ hvR
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨q, hq, (Digraph.mem_outNeighborFinset (G := G)).mp hv⟩, hvR⟩)
  rw [outdegree_eq_directCount_of_captured G _ q hCap,
    directCount_union_of_disjoint G _ _ _ hDis]

theorem sixteen_le_q_retained_add_twice_anonymous {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    16 ≤ edgeCount G C.Q (retainedVertexSet G C) +
      2 * (qAnonymousSet G C).card := by
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

theorem totalHToQ_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6) :
    (totalHToQ (encodedArc (graphBits G L))).toNat = edgeCount G C.H C.Q := by
  have hEach : ∀ i : Fin 6,
      (hQOut (encodedArc (graphBits G L)) i).toNat =
        directCount G C.Q (hLabelEquiv G C L hHCard i).1 := by
    intro i
    rw [hQOut, toNat_count_eq_fin_sum 2 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Q L.q _
    intro q
    rw [hLabelEquiv_val]
    rw [show 1 + i.val = i.val + 1 by omega,
      aToQ_graphBits G C L hG hzLe (i+1) q (by omega) q.isLt]
    simp
  rw [totalHToQ, toNat_sumCount, ← Fin.sum_univ_eq_sum_range]
  have hEq : (∑ i : Fin 6, (hQOut (encodedArc (graphBits G L)) i).toNat) =
      ∑ i : Fin 6, directCount G C.Q (hLabelEquiv G C L hHCard i).1 := by
    apply Finset.sum_congr rfl
    intro i _
    exact hEach i
  rw [hEq, ← edgeCount_eq_sum_fin G C.H C.Q (hLabelEquiv G C L hHCard)]
  have hCap := edgeCount_le_card_mul_card G C.H C.Q
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  rw [hHCard, hQCard] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

theorem totalPToQ_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3) :
    (totalPToQ (encodedArc (graphBits G L))).toNat = edgeCount G C.P C.Q := by
  rw [totalPToQ, toNat_sumCount, ← Fin.sum_univ_eq_sum_range]
  have hEq : (∑ p : Fin 5,
      (count 2 fun q ↦ encodedArc (graphBits G L) (8+p) (13+q)).toNat) =
      ∑ p : Fin 5, directCount G C.Q (L.p p).1 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [toNat_count_eq_fin_sum 2 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Q L.q _
    intro q
    rw [pToQ_graphBits G C L hG hzLe p q p.isLt q.isLt]
    simp
  rw [hEq, ← edgeCount_eq_sum_fin G C.P C.Q L.p]
  have hCap := edgeCount_le_card_mul_card G C.P C.Q
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  rw [hp, hq] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

theorem edgeCount_H_Q_le_A_Q (C : G.LocalConfiguration) :
    edgeCount G C.H C.Q ≤ edgeCount G C.A C.Q := by
  have hSub := Digraph.LocalConfiguration.H_subset_A (G := G) C
  unfold edgeCount
  apply Finset.sum_le_sum_of_subset_of_nonneg hSub
  intro v hvA hvH
  omega

theorem q_retained_upper {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6) :
    edgeCount G C.Q (retainedVertexSet G C) ≤
      (qDefect 2 (encodedArc (graphBits G L))).toNat +
        (qMissing 2 (encodedArc (graphBits G L))).toNat + 5 + 2*zCount := by
  have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = zCount := by
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
  have hHQ := totalHToQ_toNat G C L hG hzLe hHCard
  have hPQEq := totalPToQ_toNat G C L hG hzLe
  have hHCap := edgeCount_le_card_mul_card G C.H C.Q
  rw [hHCard, hQCard] at hHCap
  have hHLe : totalHToQ (encodedArc (graphBits G L)) ≤ (12 : BitVec 8) := by
    rw [BitVec.le_def, hHQ]
    have h12 : (12 : BitVec 8).toNat = 12 := by decide
    rw [h12]
    omega
  have hPLe : totalPToQ (encodedArc (graphBits G L)) ≤ (10 : BitVec 8) := by
    rw [BitVec.le_def, hPQEq]
    have h10 : (10 : BitVec 8).toNat = 10 := by decide
    rw [h10]
    have hCap := edgeCount_le_card_mul_card G C.P C.Q
    rw [hPCard, hQCard] at hCap
    omega
  have hHDef : (qDefect 2 (encodedArc (graphBits G L))).toNat =
      12 - edgeCount G C.H C.Q := by
    change ((12 : BitVec 8) - totalHToQ (encodedArc (graphBits G L))).toNat = _
    rw [BitVec.toNat_sub_of_le hHLe, hHQ]
    rw [show (12 : BitVec 8).toNat = 12 by decide]
  have hQMiss : (qMissing 2 (encodedArc (graphBits G L))).toNat =
      10 - edgeCount G C.P C.Q := by
    change ((10 : BitVec 8) - totalPToQ (encodedArc (graphBits G L))).toNat = _
    rw [BitVec.toNat_sub_of_le hPLe, hPQEq]
    rw [show (10 : BitVec 8).toNat = 10 by decide]
  have hRetained : edgeCount G C.Q (retainedVertexSet G C) =
      edgeCount G C.Q C.A + edgeCount G C.Q C.P + edgeCount G C.Q C.Q +
        edgeCount G C.Q (externalTargets G C) := by
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
        · rcases Finset.mem_union.mp hvZ with hvKnown | hvRoot
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvKnown
                (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
          · by_cases hr : ∃ p ∈ C.P, G.Adj p C.s
            · have hvs : v = C.s := by simpa [rootSecondFinset, hr] using hvRoot
              subst v
              exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
            · simp [rootSecondFinset, hr] at hvRoot
        · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvZ
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvZ
    rw [retainedVertexSet, ← Digraph.LocalConfiguration.P_union_Q (G := G) C]
    simp only [← Finset.union_assoc]
    rw [edgeCount_union_of_disjoint G C.Q (C.A ∪ C.P ∪ C.Q)
      (externalTargets G C) hAllZ,
      edgeCount_union_of_disjoint G C.Q (C.A ∪ C.P) C.Q hAPQ,
      edgeCount_union_of_disjoint G C.Q C.A C.P hAP]
  have hHA := edgeCount_H_Q_le_A_Q G C
  rw [hRetained, hHDef, hQMiss]
  omega

theorem qAnonymousLower_le_card {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hzLe : zCount ≤ 3) (hHCard : C.H.card = 6)
    (hz : zCount = 1 ∨ zCount = 2) :
    (qAnonymousLower 2 zCount (encodedArc (graphBits G L))).toNat ≤
      (qAnonymousSet G C).card := by
  have hSixteen := sixteen_le_q_retained_add_twice_anonymous G C L hMin
  have hUpper := q_retained_upper G C L hG hzLe hHCard
  have hHQ := totalHToQ_toNat G C L hG hzLe hHCard
  have hPQ := totalPToQ_toNat G C L hG hzLe
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hHCap := edgeCount_le_card_mul_card G C.H C.Q
  have hPCap := edgeCount_le_card_mul_card G C.P C.Q
  rw [hHCard, hQCard] at hHCap
  rw [hPCard, hQCard] at hPCap
  have hHLe : totalHToQ (encodedArc (graphBits G L)) ≤ (12 : BitVec 8) := by
    rw [BitVec.le_def, hHQ, show (12 : BitVec 8).toNat = 12 by decide]
    omega
  have hPLe : totalPToQ (encodedArc (graphBits G L)) ≤ (10 : BitVec 8) := by
    rw [BitVec.le_def, hPQ, show (10 : BitVec 8).toNat = 10 by decide]
    omega
  have hDefBound : (qDefect 2 (encodedArc (graphBits G L))).toNat ≤ 12 := by
    change ((12 : BitVec 8) - totalHToQ (encodedArc (graphBits G L))).toNat ≤ 12
    rw [BitVec.toNat_sub_of_le hHLe, show (12 : BitVec 8).toNat = 12 by decide]
    omega
  have hMissBound : (qMissing 2 (encodedArc (graphBits G L))).toNat ≤ 10 := by
    change ((10 : BitVec 8) - totalPToQ (encodedArc (graphBits G L))).toNat ≤ 10
    rw [BitVec.toNat_sub_of_le hPLe, show (10 : BitVec 8).toNat = 10 by decide]
    omega
  let d := qDefect 2 (encodedArc (graphBits G L)) +
    qMissing 2 (encodedArc (graphBits G L))
  have hdNat : d.toNat = (qDefect 2 (encodedArc (graphBits G L))).toNat +
      (qMissing 2 (encodedArc (graphBits G L))).toNat := by
    dsimp [d]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [← hdNat] at hUpper
  have hn0 : (0 : BitVec 8).toNat = 0 := by decide
  have hn1 : (1 : BitVec 8).toNat = 1 := by decide
  have hn2 : (2 : BitVec 8).toNat = 2 := by decide
  have hn3 : (3 : BitVec 8).toNat = 3 := by decide
  have hn4 : (4 : BitVec 8).toNat = 4 := by decide
  have hn5 : (5 : BitVec 8).toNat = 5 := by decide
  have hn6 : (6 : BitVec 8).toNat = 6 := by decide
  have hn8 : (8 : BitVec 8).toNat = 8 := by decide
  rcases hz with rfl | rfl
  · change (if d == 0 then (5 : BitVec 8) else if d.ule 2 then 4
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
  · change (if d == 0 then (4 : BitVec 8) else if d.ule 2 then 3
      else if d.ule 4 then 2 else if d.ule 6 then 1 else 0).toNat ≤ _
    split <;> rename_i h0
    · simp only [beq_iff_eq] at h0
      have hd := congrArg BitVec.toNat h0
      rw [hn0] at hd
      rw [hn4]
      omega
    split <;> rename_i h2
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h2
      rw [hn2] at h2
      rw [hn3]
      omega
    split <;> rename_i h4
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h4
      rw [hn4] at h4
      rw [hn2]
      omega
    split <;> rename_i h6
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h6
      rw [hn6] at h6
      rw [hn1]
      omega
    · simp

theorem labelled_outgoing_retained {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (source : Nat)
    (hs : source < 13) :
    G.outNeighborFinset (labelledVertex G L source) ⊆ retainedVertexSet G C := by
  intro v hv
  by_cases hsA : source < 8
  · have hCap :=
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG (L.a ⟨source, hsA⟩).1 (L.a _).2 (by
          simpa [labelledVertex, hsA] using hv)
    rcases Finset.mem_union.mp hCap with hvA | hvB
    · simp [retainedVertexSet, hvA]
    · simp [retainedVertexSet, hvB]
  · have hCap := BSixKThree.P_outgoingCaptured_general G C hG
      (L.p ⟨source-8, by omega⟩).1 (L.p _).2 (by
        simpa [labelledVertex, hsA, hs] using hv)
    rcases Finset.mem_union.mp hCap with hHPQ | hvZ
    · rcases Finset.mem_union.mp hHPQ with hHP | hvQ
      · rcases Finset.mem_union.mp hHP with hvH | hvP
        · simp [retainedVertexSet,
            Digraph.LocalConfiguration.H_subset_A (G := G) C hvH]
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ))
    · simp [retainedVertexSet, hvZ]

theorem reachesBothQ_adj {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (source : Nat) (hs : source < 13)
    (hBoth : reachesBothQ (encodedArc (graphBits G L)) source = true) :
    ∀ q ∈ C.Q, G.Adj (labelledVertex G L source) q := by
  intro q hq
  obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hq⟩
  have hqVal : (L.q i).1 = q := congrArg Subtype.val hi
  simp only [reachesBothQ, Bool.and_eq_true] at hBoth
  have hiCases : i = 0 ∨ i = 1 := by
    by_cases hi0 : i.val = 0
    · left; exact Fin.ext hi0
    · right; apply Fin.ext; omega
  rcases hiCases with rfl | rfl
  · rw [← hqVal]
    have h := hBoth.1
    rw [encodedArc_graphBits G C L hG hzLe source 13 hs (by omega)] at h
    simpa [labelledVertex] using of_decide_eq_true h
  · rw [← hqVal]
    have h := hBoth.2
    rw [encodedArc_graphBits G C L hG hzLe source 14 hs (by omega)] at h
    simpa [labelledVertex] using of_decide_eq_true h

theorem qAnonymous_mem_second {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (source : Nat) (hs : source < 13)
    (hBoth : reachesBothQ (encodedArc (graphBits G L)) source = true) :
    qAnonymousSet G C ⊆
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  intro v hv
  have hvOutside := (Finset.mem_sdiff.mp hv).2
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hv).1 with ⟨q, hqQ, hqv⟩
  have hsq := reachesBothQ_adj G C L hG hzLe source hs hBoth q hqQ
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
    · have hsP : labelledVertex G L source = (L.p ⟨source-8, by omega⟩).1 := by
        simp [labelledVertex, hsA, hs]
      rw [hsP]
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Digraph.LocalConfiguration.P_subset_B (G := G) C (L.p _).2))
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨q, hsq, hqv⟩, hNot, hne⟩

theorem secondCount_le_retained_card {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (source : Nat) (hs : source < 13) :
    (secondCount zCount (encodedArc (graphBits G L)) source).toNat ≤
      ((retainedVertexSet G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (labelledVertex G L source)).card := by
  apply count_le_filterCard (retainedVertexSet G C)
    (retainedLabelEquiv G C L hG)
    (strictSecond (encodedArc (graphBits G L)) source)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    (by omega)
  intro target ht
  simpa using strictSecond_true_mem G C L hG hzLe source target hs target.isLt ht

theorem augmented_projected_le_second {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hzLe : zCount ≤ 3) (hHCard : C.H.card = 6)
    (hz : zCount = 1 ∨ zCount = 2) (source : Nat) (hs : source < 13)
    (hBoth : reachesBothQ (encodedArc (graphBits G L)) source = true) :
    (secondCount zCount (encodedArc (graphBits G L)) source).toNat +
        (qAnonymousLower 2 zCount (encodedArc (graphBits G L))).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  let R := (retainedVertexSet G C).filter fun v ↦
    v ∈ G.secondOutNeighborFinset (labelledVertex G L source)
  let U := qAnonymousSet G C
  have hProjected := secondCount_le_retained_card G C L hG hzLe source hs
  have hLower := qAnonymousLower_le_card G C L hG hMin hzLe hHCard hz
  have hDis : Disjoint R U := by
    rw [Finset.disjoint_left]
    intro v hvR hvU
    exact (Finset.mem_sdiff.mp hvU).2 (Finset.mem_filter.mp hvR).1
  have hUnion : R ∪ U ⊆
      G.secondOutNeighborFinset (labelledVertex G L source) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvR | hvU
    · exact (Finset.mem_filter.mp hvR).2
    · exact qAnonymous_mem_second G C L hG hzLe source hs hBoth hvU
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

theorem qAnonymousLower_toNat_le_five (y zCount : Nat)
    (arc : Nat → Nat → Bool) :
    (qAnonymousLower y zCount arc).toNat ≤ 5 := by
  unfold qAnonymousLower
  by_cases h21 : (decide (y = 2) && decide (zCount = 1)) = true
  · rw [if_pos h21]
    by_cases h0 : (qDefect y arc + qMissing y arc == 0) = true
    · rw [if_pos h0]; decide
    · rw [if_neg h0]
      by_cases h2 : (qDefect y arc + qMissing y arc).ule 2 = true
      · rw [if_pos h2]; decide
      · rw [if_neg h2]
        by_cases h4 : (qDefect y arc + qMissing y arc).ule 4 = true
        · rw [if_pos h4]; decide
        · rw [if_neg h4]
          by_cases h6 : (qDefect y arc + qMissing y arc).ule 6 = true
          · rw [if_pos h6]; decide
          · rw [if_neg h6]
            by_cases h8 : (qDefect y arc + qMissing y arc).ule 8 = true
            · rw [if_pos h8]; decide
            · rw [if_neg h8]; decide
  · rw [if_neg h21]
    by_cases h22 : (decide (y = 2) && decide (zCount = 2)) = true
    · rw [if_pos h22]
      by_cases h0 : (qDefect y arc + qMissing y arc == 0) = true
      · rw [if_pos h0]; decide
      · rw [if_neg h0]
        by_cases h2 : (qDefect y arc + qMissing y arc).ule 2 = true
        · rw [if_pos h2]; decide
        · rw [if_neg h2]
          by_cases h4 : (qDefect y arc + qMissing y arc).ule 4 = true
          · rw [if_pos h4]; decide
          · rw [if_neg h4]
            by_cases h6 : (qDefect y arc + qMissing y arc).ule 6 = true
            · rw [if_pos h6]; decide
            · rw [if_neg h6]; decide
    · rw [if_neg h22]; decide

theorem bitvec_add_zero (x : BitVec 8) : x + 0 = x := by
  bv_decide

theorem second_add_qLower_toNat (y zCount : Nat) (arc : Nat → Nat → Bool)
    (source : Nat) (hzLe : zCount ≤ 3) :
    (secondCount zCount arc source + qAnonymousLower y zCount arc).toNat =
      (secondCount zCount arc source).toNat +
        (qAnonymousLower y zCount arc).toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
  have hSecond : (secondCount zCount arc source).toNat ≤ 15 + zCount := by
    unfold secondCount
    rw [toNat_count_eq_fin_sum _ _ (by omega)]
    calc
      _ ≤ ∑ _i : Fin (15+zCount), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases strictSecond arc source i <;> decide
      _ = 15+zCount := by simp
  have hQ := qAnonymousLower_toNat_le_five y zCount arc
  omega

theorem aDegree_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (a : Nat) (ha : a < 8) :
    (aOut (encodedArc (graphBits G L)) a +
      aBOut (encodedArc (graphBits G L)) a).toNat =
      G.outdegree (L.a ⟨a, ha⟩).1 := by
  have hAO := aOut_toNat G C L hG hzLe a ha
  have hBO := aBOut_toNat G C L hG hzLe a ha
  rw [BitVec.toNat_add, hAO, hBO,
    Nat.mod_eq_of_lt (by
      have hA := Finset.card_le_card (Finset.filter_subset
        (G.Adj (L.a ⟨a, ha⟩).1) C.A)
      have hB := Finset.card_le_card (Finset.filter_subset
        (G.Adj (L.a ⟨a, ha⟩).1) C.B)
      have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
      have hBCard : C.B.card = 7 := by
        rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
          Finset.card_union_of_disjoint
            (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
        have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
        have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
        omega
      change directCount G C.A _ ≤ C.A.card at hA
      change directCount G C.B _ ≤ C.B.card at hB
      omega), A_outdegree_eq_A_add_B G C hG _ (L.a _).2]

theorem pDegree_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6) (p : Nat) (hp : p < 5) :
    (pDegree zCount (encodedArc (graphBits G L)) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hP := pOut_toNat G C L hG hzLe p hp
  have hH := pHOut_toNat G C L hG hzLe hHCard p hp
  have hAux := pAuxOut_toNat G C L hG hzLe p hp
  rw [pDegree, BitVec.toNat_add, BitVec.toNat_add, hP, hH, hAux]
  have hPLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.P)
  have hHLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) C.H)
  have hAuxLe := Finset.card_le_card (Finset.filter_subset
    (G.Adj (L.p ⟨p, hp⟩).1) (C.Q ∪ externalTargets G C))
  have hPC : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQC : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hZC : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hQZ : Disjoint C.Q (externalTargets G C) :=
    Finset.disjoint_of_subset_left (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      (BSixKThree.disjoint_B_externalTargets G C)
  change directCount G C.P _ ≤ C.P.card at hPLe
  change directCount G C.H _ ≤ C.H.card at hHLe
  change directCount G (C.Q ∪ externalTargets G C) _ ≤
    (C.Q ∪ externalTargets G C).card at hAuxLe
  rw [Finset.card_union_of_disjoint hQZ, hQC, hZC] at hAuxLe
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    directCount_union_of_disjoint G C.Q (externalTargets G C) _ hQZ]
  have hDegree := P_outdegree_eq_blocks G C L hG p hp
  omega

theorem pSecondCount_le_graph {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (hzLe : zCount ≤ 3)
    (p : Nat) (hp : p < 5) :
    (secondCount zCount (encodedArc (graphBits G L)) (8+p)).toNat ≤
      G.secondOutdegree (L.p ⟨p, hp⟩).1 := by
  have h := secondCount_le_retained_card G C L hG hzLe (8+p) (by omega)
  have hSub : ((retainedVertexSet G C).filter fun v ↦
      v ∈ G.secondOutNeighborFinset (labelledVertex G L (8+p))).card ≤
      G.secondOutdegree (labelledVertex G L (8+p)) := by
    unfold Digraph.secondOutdegree
    apply Finset.card_le_card
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  simpa [labelledVertex, show ¬8+p<8 by omega, show 8+p<13 by omega]
    using h.trans hSub

set_option maxHeartbeats 1000000 in
theorem augmentedNonSeymour_one_three_true
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 6)
    (hANon : aNonSeymour 3 (encodedArc (graphBits G L)) = true) :
    augmentedNonSeymour 1 3 (encodedArc (graphBits G L)) = true := by
  have hQ : qAnonymousLower 1 3 (encodedArc (graphBits G L)) = 0 := by
    simp [qAnonymousLower]
  rw [augmentedNonSeymour, hQ, Bool.and_eq_true]
  constructor
  · simpa [aNonSeymour, bitvec_add_zero] using hANon
  · rw [all_eq_true_iff]
    intro p hp
    simp only [ite_self, bitvec_add_zero, BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [pDegree_toNat G C L hG (by omega) hHCard p hp]
    have hSecond :
        (secondCount 3 (encodedArc (graphBits G L)) (8+p)).toNat ≤
          G.secondOutdegree (L.p ⟨p, hp⟩).1 :=
      pSecondCount_le_graph (zCount := 3) G C L hG (by omega) p hp
    have hLess : G.secondOutdegree (L.p ⟨p, hp⟩).1 <
        G.outdegree (L.p ⟨p, hp⟩).1 :=
      Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨(L.p ⟨p, hp⟩).1, h⟩)
    omega

set_option maxHeartbeats 1000000 in
-- The anonymous-`Q` correction adds a second finite count for each source.
theorem augmentedNonSeymour_two_true {zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6)
    (hz : zCount = 1 ∨ zCount = 2) :
    augmentedNonSeymour 2 zCount (encodedArc (graphBits G L)) = true := by
  rw [augmentedNonSeymour, Bool.and_eq_true]
  constructor
  · rw [all_eq_true_iff]
    intro a ha
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    have hDegree := aDegree_toNat G C L hG hzLe a ha
    by_cases hBoth : reachesBothQ (encodedArc (graphBits G L)) a = true
    · rw [if_pos hBoth, second_add_qLower_toNat 2 zCount _ a hzLe, hDegree]
      have hAug := augmented_projected_le_second G C L hG hMin hzLe hHCard hz
        a (by omega) hBoth
      simpa [labelledVertex, ha] using hAug.trans_lt
        (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
          (fun h ↦ hNoSeymour ⟨_, h⟩))
    · rw [if_neg hBoth]
      rw [bitvec_add_zero]
      rw [hDegree]
      have hSecond := secondCount_le_graph G C L hG (by omega) a ha
      exact hSecond.trans_lt
        (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
          (fun h ↦ hNoSeymour ⟨_, h⟩))
  · rw [all_eq_true_iff]
    intro p hp
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    have hDegree := pDegree_toNat G C L hG hzLe hHCard p hp
    by_cases hBoth : reachesBothQ (encodedArc (graphBits G L)) (8+p) = true
    · rw [if_pos hBoth, second_add_qLower_toNat 2 zCount _ (8+p) hzLe,
        hDegree]
      have hAug := augmented_projected_le_second G C L hG hMin hzLe hHCard hz
        (8+p) (by omega) hBoth
      simpa [labelledVertex, show ¬8+p<8 by omega, show 8+p<13 by omega]
        using hAug.trans_lt
          (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
            (fun h ↦ hNoSeymour ⟨_, h⟩))
    · rw [if_neg hBoth]
      rw [bitvec_add_zero]
      rw [hDegree]
      exact (pSecondCount_le_graph G C L hG (by omega) p hp).trans_lt
        (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
          (fun h ↦ hNoSeymour ⟨_, h⟩))

theorem augmentedNonSeymour_true {yValue zCount : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzLe : zCount ≤ 3)
    (hHCard : C.H.card = 6)
    (hANon : aNonSeymour zCount (encodedArc (graphBits G L)) = true)
    (hyz : (yValue = 1 ∧ zCount = 3) ∨
      (yValue = 2 ∧ (zCount = 1 ∨ zCount = 2))) :
    augmentedNonSeymour yValue zCount (encodedArc (graphBits G L)) = true := by
  rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, hz⟩
  · exact augmentedNonSeymour_one_three_true G C L hG hNoSeymour hHCard hANon
  · exact augmentedNonSeymour_two_true G C L hG hMin hNoSeymour hzLe hHCard hz

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.AugmentedBridge
