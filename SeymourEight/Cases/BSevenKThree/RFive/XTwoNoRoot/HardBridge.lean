import SeymourEight.Cases.BSevenKThree.RFive.XTwoNoRoot.EasyBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Structure
import SeymourEight.Certificates.BSevenKThree.RFive.XTwo.AOneRigid
import SeymourEight.Shared.InnerDegreeThree

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.HardBridge

open Shared CertificateBridge Labels Encoding EasyBridge
open SeymourEight.BSixKThreeCore
open SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem finiteCount_eq_sumN (n : Nat) (f : Nat → Bool) :
    FiniteCore.count n f = sumN n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FiniteCore.count, sumN, ih]; rfl

theorem finiteAll_eq_allN (n : Nat) (f : Nat → Bool) :
    FiniteCore.all n f = allN n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FiniteCore.all, allN, ih]

theorem finiteAny_eq_anyN (n : Nat) (f : Nat → Bool) :
    FiniteCore.any n f = anyN n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FiniteCore.any, anyN, ih]

theorem minimumA_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 3) :
    (allN 8 fun a ↦ (3 : BitVec 8).ule (Core.internalA (graphArc G L) a)) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro a ha
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [internalA_toNat G C L a ha]
  have h := (hPivot (L.a ⟨a, ha⟩).1 (L.a _).2).1
  change C.k ≤ directCount G C.A (L.a ⟨a, ha⟩).1 at h
  simpa [hk] using h

theorem degreeThreeConsequences_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C) (hk : C.k = 3) :
    degreeThreeClassification (graphArc G L) = true ∧
      threeInnerWitnesses (graphArc G L) = true := by
  let arc := graphArc G L
  have hOriented := oriented_true G C L hG
  have hOr8 : (allN 8 fun i ↦ !arc i i && allN 8 fun j ↦
      decide (i = j) || !(arc i j && arc j i)) = true := by
    rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
    intro i hi
    have hiRow := (BSixKThreeCoreGraphBridge.allN_eq_true_iff 15 _).mp hOriented i
      (by omega)
    simp only [Bool.and_eq_true] at hiRow ⊢
    refine ⟨hiRow.1, ?_⟩
    rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
    intro j hj
    exact ((BSixKThreeCoreGraphBridge.allN_eq_true_iff 15 _).mp hiRow.2 j (by omega))
  have hMinimum := minimumA_true G C L hPivot hk
  have hOr : Shared.InnerDegreeThree.oriented arc = true := by
    simpa only [Shared.InnerDegreeThree.oriented,
      finiteAll_eq_allN] using hOr8
  have hMin : Shared.InnerDegreeThree.minimumThree arc = true := by
    simpa only [Shared.InnerDegreeThree.minimumThree,
      Shared.InnerDegreeThree.outCount, finiteAll_eq_allN,
      finiteCount_eq_sumN, Core.internalA] using hMinimum
  have hOutCount (source : Nat) :
      Shared.InnerDegreeThree.outCount arc source = Core.internalA arc source := by
    simp only [Shared.InnerDegreeThree.outCount, Core.internalA,
      finiteCount_eq_sumN]
  have hReaches (source target : Nat) :
      Shared.InnerDegreeThree.reaches arc source target =
        innerReaches arc source target := by
    simp only [Shared.InnerDegreeThree.reaches, innerReaches,
      finiteAny_eq_anyN]
  have hSecond (source target : Nat) :
      Shared.InnerDegreeThree.second arc source target =
        innerSecond arc source target := by
    simp only [Shared.InnerDegreeThree.second, innerSecond, hReaches]
  have hSecondCount (source : Nat) :
      Shared.InnerDegreeThree.secondCount arc source =
        innerSecondCount arc source := by
    rw [Shared.InnerDegreeThree.secondCount, innerSecondCount,
      finiteCount_eq_sumN]
    apply BSixKThreeCoreGraphBridge.sumN_congr
    intro target _
    exact hSecond source target
  have hDegreeThree (source : Nat) :
      Shared.InnerDegreeThree.degreeThree arc source = degreeThree arc source := by
    simp only [Shared.InnerDegreeThree.degreeThree, degreeThree, hOutCount]
  have hInnerSeymour (source : Nat) :
      Shared.InnerDegreeThree.innerSeymour arc source = innerSeymour arc source := by
    simp only [Shared.InnerDegreeThree.innerSeymour, innerSeymour,
      hOutCount, hSecondCount]
  have hDegreeThreeInner (source : Nat) :
      Shared.InnerDegreeThree.degreeThreeInner arc source =
        degreeThreeInner arc source := by
    simp only [Shared.InnerDegreeThree.degreeThreeInner, degreeThreeInner,
      hDegreeThree, hInnerSeymour]
  have hDegreeThreeInnerCount :
      sumN 8 (Shared.InnerDegreeThree.degreeThreeInner arc) =
        sumN 8 (degreeThreeInner arc) := by
    apply BSixKThreeCoreGraphBridge.sumN_congr
    intro source _
    exact hDegreeThreeInner source
  have hClassification := Shared.InnerDegreeThree.classification_of arc hOr hMin
  have hWitnesses := Shared.InnerDegreeThree.threeWitnesses_of arc hOr hMin
  constructor
  · simpa only [Shared.InnerDegreeThree.classification,
      degreeThreeClassification, finiteAll_eq_allN, hDegreeThree,
      hDegreeThreeInner] using
      hClassification
  · simpa only [Shared.InnerDegreeThree.threeWitnesses,
      threeInnerWitnesses, finiteCount_eq_sumN, hDegreeThreeInnerCount] using
      hWitnesses

theorem aOneInner_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hx : C.x = 2) :
    (allN 3 fun a ↦ degreeThreeInner (graphArc G L) (1 + a)) = true := by
  let arc := graphArc G L
  have hOriented := oriented_true G C L hG
  have hOr8 : (allN 8 fun i ↦ !arc i i && allN 8 fun j ↦
      decide (i = j) || !(arc i j && arc j i)) = true := by
    rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
    intro i hi
    have hiRow := (BSixKThreeCoreGraphBridge.allN_eq_true_iff 15 _).mp hOriented i
      (by omega)
    simp only [Bool.and_eq_true] at hiRow
    rw [Bool.and_eq_true, BSixKThreeCoreGraphBridge.allN_eq_true_iff]
    exact ⟨hiRow.1, fun j hj ↦
      ((BSixKThreeCoreGraphBridge.allN_eq_true_iff 15 _).mp hiRow.2 j (by omega))⟩
  have hFixed15 := fixed_true G C L hG
  have hFixed8 : (allN 8 fun j ↦ arc 0 j == decide (1 ≤ j && j ≤ 3)) = true := by
    rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
    intro j hj
    have h := (BSixKThreeCoreGraphBridge.allN_eq_true_iff 15 _).mp hFixed15 j
      (by omega)
    simpa [arc, show ¬(8 ≤ j ∧ j < 13) by omega] using h
  have hNoRPair := noR_true G C L hG
  simp only [Bool.and_eq_true] at hNoRPair
  have hNoR := hNoRPair.1
  have hMinimum := minimumA_true G C L hPivot hk
  have hDegree : (allN 3 fun a ↦ degreeThree arc (1 + a)) = true := by
    rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
    intro a ha
    unfold degreeThree
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [internalA_toNat G C L (1 + a) (by omega)]
    have hA1 : (L.a ⟨1 + a, by omega⟩).1 ∈ C.A1 := by
      simpa [Nat.add_comm] using L.a_aOne ⟨a, ha⟩
    rw [SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Structure.A1_internalDegree_eq_three
      G C hG hPivot hk hx _ hA1]
    decide
  have h := aOne_inner_of_rigid arc
  rw [hOr8, hFixed8, hNoR, hMinimum, hDegree] at h
  simpa [arc] using h

noncomputable def hEquiv (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hHCard : C.H.card = 5) : Fin 5 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 5 → {v : V // v ∈ C.H} := fun i ↦
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
      exact Subtype.ext (by simpa [f] using congrArg Subtype.val hij)
    have hval := congrArg Fin.val ha
    exact Nat.add_right_cancel hval
  · simpa using hHCard.symm

@[simp] theorem hEquiv_val (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hHCard : C.H.card = 5) (i : Fin 5) :
    (hEquiv G C L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

theorem qOut_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (u : Nat) (hu : u < 13) :
    (qOut (graphArc G L) u).toNat =
      directCount G C.Q (localVertex G L u) := by
  have h := BSixKThreeCoreGraphBridge.toNat_sumN_equiv G C.Q L.q
    (localVertex G L u) (by omega) (by omega)
  rw [qOut, ← h]
  apply congrArg BitVec.toNat
  apply BSixKThreeCoreGraphBridge.sumN_congr
  intro q hq
  rw [graphArc_eq_adj G C L u (13 + q) hu (by omega)]
  simp [localVertex, show ¬(13 + q < 8) by omega,
    show ¬(13 + q < 13) by omega, show 13 + q < 15 by omega,
    Nat.mod_eq_of_lt hq]

theorem hToQ_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hHCard : C.H.card = 5) :
    (hToQ (graphArc G L)).toNat = edgeCount G C.H C.Q := by
  rw [hToQ, BSixKThreeCoreGraphBridge.toNat_sumCountsN_of_le 5 2 _
    (by omega) (by
      intro i hi
      rw [qOut_toNat G C L (1 + i) (by omega)]
      have hCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hCard)]
  rw [← Fin.sum_univ_eq_sum_range,
    edgeCount_eq_sum_fin G C.H C.Q (hEquiv G C L hHCard)]
  apply Finset.sum_congr rfl
  intro i _
  rw [qOut_toNat G C L (1 + i) (by omega), hEquiv_val]
  simp [localVertex, show i.val + 1 < 8 by omega, Nat.add_comm]

theorem pToQ_toNat (C : G.LocalConfiguration) (L : Labels G 3 C) :
    (pToQ (graphArc G L)).toNat = edgeCount G C.P C.Q := by
  rw [pToQ, BSixKThreeCoreGraphBridge.toNat_sumCountsN_of_le 5 2 _
    (by omega) (by
      intro i hi
      rw [qOut_toNat G C L (8 + i) (by omega)]
      have hCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hCard)]
  rw [← Fin.sum_univ_eq_sum_range, edgeCount_eq_sum_fin G C.P C.Q L.p]
  apply Finset.sum_congr rfl
  intro i _
  rw [qOut_toNat G C L (8 + i) (by omega)]
  simp [localVertex, show ¬8 + i.val < 8 by omega,
    show 8 + i.val < 13 by omega]

def retainedSet (C : G.LocalConfiguration) : Finset V :=
  localSet G C ∪ externalTargets G C

/-- Targets reached from `Q` but outside the compact finite model. -/
def qAnonymousSet (C : G.LocalConfiguration) : Finset V :=
  G.outNeighborFinsetOf C.Q \ retainedSet G C

theorem q_outdegree_split (C : G.LocalConfiguration) (q : V) (hq : q ∈ C.Q) :
    G.outdegree q = directCount G (retainedSet G C) q +
      directCount G (qAnonymousSet G C) q := by
  have hDis : Disjoint (retainedSet G C) (qAnonymousSet G C) := by
    rw [Finset.disjoint_left]
    intro v hvR hvU
    exact (Finset.mem_sdiff.mp hvU).2 hvR
  have hCap : G.outNeighborFinset q ⊆ retainedSet G C ∪ qAnonymousSet G C := by
    intro v hv
    by_cases hvR : v ∈ retainedSet G C
    · exact Finset.mem_union_left _ hvR
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨
        (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨q, hq, (Digraph.mem_outNeighborFinset (G := G)).mp hv⟩, hvR⟩)
  rw [BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured G q _ hCap,
    directCount_union_of_disjoint G _ _ _ hDis]

theorem sixteen_le_q_retained_add_twice_anonymous (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    16 ≤ edgeCount G C.Q (retainedSet G C) +
      2 * (qAnonymousSet G C).card := by
  have hEach (i : Fin 2) := q_outdegree_split G C (L.q i).1 (L.q i).2
  have hAnon (i : Fin 2) :
      directCount G (qAnonymousSet G C) (L.q i).1 ≤ (qAnonymousSet G C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hMinSum := add_le_add (hMin (L.q 0).1) (hMin (L.q 1).1)
  rw [edgeCount_eq_sum_fin G C.Q (retainedSet G C) L.q]
  simp only [Fin.sum_univ_two]
  rw [hEach 0, hEach 1] at hMinSum
  have h0 := hAnon 0
  have h1 := hAnon 1
  omega

theorem q_retained_upper (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 5) :
    edgeCount G C.Q (retainedSet G C) ≤
      (qAnonymousDefect (graphArc G L)).toNat + 13 := by
  have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
  have hPCard : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = 3 := by
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
  have hHQ := hToQ_toNat G C L hHCard
  have hPQEq := pToQ_toNat G C L
  have hHCap := edgeCount_le_card_mul_card G C.H C.Q
  rw [hHCard, hQCard] at hHCap
  have hHLe : hToQ (graphArc G L) ≤ (10 : BitVec 8) := by
    rw [BitVec.le_def, hHQ, show (10 : BitVec 8).toNat = 10 by decide]
    omega
  have hPLe : pToQ (graphArc G L) ≤ (10 : BitVec 8) := by
    rw [BitVec.le_def, hPQEq, show (10 : BitVec 8).toNat = 10 by decide]
    have hCap := edgeCount_le_card_mul_card G C.P C.Q
    rw [hPCard, hQCard] at hCap
    omega
  have hDef : (qAnonymousDefect (graphArc G L)).toNat =
      (10 - edgeCount G C.H C.Q) + (10 - edgeCount G C.P C.Q) := by
    rw [qAnonymousDefect, BitVec.toNat_add]
    rw [BitVec.toNat_sub_of_le hHLe, BitVec.toNat_sub_of_le hPLe, hHQ, hPQEq]
    rw [show (10 : BitVec 8).toNat = 10 by decide]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hRetained : edgeCount G C.Q (retainedSet G C) =
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
        · exact (Finset.disjoint_left.mp
            (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
              (Finset.mem_union_left C.B hvA) hvZ
        · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvZ
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvZ
    rw [retainedSet, localSet, ← Digraph.LocalConfiguration.P_union_Q (G := G) C]
    simp only [← Finset.union_assoc]
    rw [edgeCount_union_of_disjoint G C.Q (C.A ∪ C.P ∪ C.Q)
      (externalTargets G C) hAllZ,
      edgeCount_union_of_disjoint G C.Q (C.A ∪ C.P) C.Q hAPQ,
      edgeCount_union_of_disjoint G C.Q C.A C.P hAP]
  have hHLeA : edgeCount G C.H C.Q ≤ edgeCount G C.A C.Q := by
    unfold edgeCount
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Digraph.LocalConfiguration.H_subset_A (G := G) C)
    intro v hvA hvH
    omega
  rw [hRetained, hDef]
  omega

theorem qAnonymousLower_le_card (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 5) :
    (qAnonymousLower (graphArc G L)).toNat ≤ (qAnonymousSet G C).card := by
  have hSixteen := sixteen_le_q_retained_add_twice_anonymous G C L hMin
  have hUpper := q_retained_upper G C L hG hHCard
  let d := qAnonymousDefect (graphArc G L)
  change edgeCount G C.Q (retainedSet G C) ≤ d.toNat + 13 at hUpper
  change (if d == 0 then (2 : BitVec 8) else if d.ule 2 then 1 else 0).toNat ≤ _
  split <;> rename_i h0
  · simp only [beq_iff_eq] at h0
    have hd := congrArg BitVec.toNat h0
    rw [show (0 : BitVec 8).toNat = 0 by decide] at hd
    rw [show (2 : BitVec 8).toNat = 2 by decide]
    omega
  split <;> rename_i h2
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h2
    rw [show (2 : BitVec 8).toNat = 2 by decide] at h2
    rw [show (1 : BitVec 8).toNat = 1 by decide]
    omega
  · simp

theorem innerSecond_true_iff (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (source target : Nat) (hs : source < 8)
    (ht : target < 8) :
    innerSecond (graphArc G L) source target = true ↔
      (L.a ⟨target, ht⟩).1 ∈
        internalSecondNeighbors (G := G) C.A (L.a ⟨source, hs⟩).1 := by
  unfold innerSecond innerReaches
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    internalSecondNeighbors, Finset.mem_filter]
  rw [graphArc_A G L source target hs ht]
  constructor
  · rintro ⟨⟨hne, hNot⟩, hReach⟩
    obtain ⟨middle, hm, hPath⟩ :=
      (BSixKThreeCoreGraphBridge.anyN_eq_true_iff 8 _).mp hReach
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
    rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
    rw [graphArc_A G L source middle hs hm] at hFirst
    rw [graphArc_A G L middle target hm ht] at hLast
    refine ⟨(L.a _).2, by simpa using hNot, ?_, (L.a ⟨middle, hm⟩).1,
      (L.a _).2, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩
    intro heq
    apply hne
    exact Fin.ext_iff.mp (L.a.injective (Subtype.ext heq))
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
      exact congrArg (fun q : Fin 8 ↦ (L.a q).1) (Fin.ext heq)
    refine ⟨⟨hst, by simp [hNot]⟩,
      (BSixKThreeCoreGraphBridge.anyN_eq_true_iff 8 _).mpr
        ⟨mi, mi.isLt, ?_⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hms, hmt⟩, ?_⟩, ?_⟩
    · rw [graphArc_A G L source mi hs mi.isLt]
      exact decide_eq_true (by simpa [hmVal] using hFirst)
    · rw [graphArc_A G L mi target mi.isLt ht]
      exact decide_eq_true (by simpa [hmVal] using hLast)

theorem innerSecondCount_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (source : Nat) (hs : source < 8) :
    (innerSecondCount (graphArc G L) source).toNat =
      (internalSecondNeighbors (G := G) C.A (L.a ⟨source, hs⟩).1).card := by
  rw [innerSecondCount,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount 8 _ (by omega),
    BSixKThreeCoreGraphBridge.trueCount_eq_filter_fin]
  let T := internalSecondNeighbors (G := G) C.A (L.a ⟨source, hs⟩).1
  let f : {i : Fin 8 // innerSecond (graphArc G L) source i = true} →
      {v : V // v ∈ T} := fun i ↦
    ⟨(L.a i.val).1, (innerSecond_true_iff G C L hG source i hs i.val.isLt).mp i.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply L.a.injective
      apply Subtype.ext
      exact congrArg (fun x : {v : V // v ∈ T} ↦ x.1) hij
    · rintro ⟨v, hv⟩
      have hvA := (Finset.mem_filter.mp hv).1
      obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
      have hSecond : innerSecond (graphArc G L) source i = true :=
        (innerSecond_true_iff G C L hG source i hs i.isLt).mpr (by
          simpa [congrArg Subtype.val hi] using hv)
      refine ⟨⟨i, hSecond⟩, ?_⟩
      apply Subtype.ext
      dsimp [f]
      exact congrArg Subtype.val hi
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  have hdomain : Fintype.card {i : Fin 8 //
      innerSecond (graphArc G L) source i = true} =
      ((Finset.univ : Finset (Fin 8)).filter
        (fun i : Fin 8 ↦ innerSecond (graphArc G L) source i.val = true)).card := by
    apply Fintype.card_ofFinset
  have htarget : Fintype.card {v : V // v ∈ T} = T.card := by simp
  rw [← hdomain, ← htarget]
  exact hcard

theorem aPOut_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (source : Nat) (hs : source < 8) :
    (aPOut (graphArc G L) source).toNat =
      directCount G C.P (L.a ⟨source, hs⟩).1 := by
  have h := BSixKThreeCoreGraphBridge.toNat_sumN_equiv G C.P L.p
    (L.a ⟨source, hs⟩).1 (by omega) (by omega)
  rw [aPOut, ← h]
  apply congrArg BitVec.toNat
  apply BSixKThreeCoreGraphBridge.sumN_congr
  intro p hp
  rw [graphArc_AP G L source p hs hp]
  simp [Nat.mod_eq_of_lt hp]

def hallNamedSet (C : G.LocalConfiguration) (v : V) : Finset V :=
  (externalTargets G C).filter fun e ↦ ∃ p ∈ C.P, G.Adj v p ∧ G.Adj p e

theorem hallCount_le_card (C : G.LocalConfiguration) (L : Labels G 3 C)
    (source : Nat) (hs : source < 8) :
    (hallCount (graphArc G L) (graphPToZ G L) source).toNat ≤
      (hallNamedSet G C (L.a ⟨source, hs⟩).1).card := by
  rw [hallCount,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount 3 _ (by omega),
    BSixKThreeCoreGraphBridge.trueCount_eq_filter_fin]
  let T := hallNamedSet G C (L.a ⟨source, hs⟩).1
  let f : {i : Fin 3 // hallReached (graphArc G L) (graphPToZ G L) source i = true} →
      {v : V // v ∈ T} := fun i ↦ ⟨(L.z i.val).1, by
    have hReach := i.2
    unfold hallReached at hReach
    rw [BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
    obtain ⟨p, hp, hPath⟩ := hReach
    simp only [Bool.and_eq_true] at hPath
    change (L.z i.val).1 ∈ hallNamedSet G C (L.a ⟨source, hs⟩).1
    rw [hallNamedSet, Finset.mem_filter]
    have hFirst := hPath.1
    have hLast := hPath.2
    rw [graphArc_AP G L source p hs hp] at hFirst
    rw [graphPToZ_eq G L p i hp i.val.isLt] at hLast
    exact ⟨(L.z _).2, (L.p ⟨p, hp⟩).1, (L.p _).2,
      of_decide_eq_true hFirst, of_decide_eq_true hLast⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply L.z.injective
    apply Subtype.ext
    exact congrArg (fun x : {v : V // v ∈ T} ↦ x.1) hij
  have hdomain : Fintype.card {i : Fin 3 //
      hallReached (graphArc G L) (graphPToZ G L) source i = true} =
      ((Finset.univ : Finset (Fin 3)).filter (fun i : Fin 3 ↦
        hallReached (graphArc G L) (graphPToZ G L) source i.val = true)).card := by
    apply Fintype.card_ofFinset
  have htarget : Fintype.card {v : V // v ∈ T} = T.card := by simp
  calc
    _ = Fintype.card {i : Fin 3 //
        hallReached (graphArc G L) (graphPToZ G L) source i = true} := hdomain.symm
    _ ≤ Fintype.card {v : V // v ∈ T} := Fintype.card_le_of_injective f hf
    _ = T.card := htarget

def selectedB (C : G.LocalConfiguration) (v : V) : Finset V :=
  internalFirstNeighbors G C.B v

def outsideHallSet (C : G.LocalConfiguration) (v : V) : Finset V :=
  G.outNeighborFinsetOf (selectedB G C v) \ localSet G C

theorem outsideHallSet_subset_second (C : G.LocalConfiguration) (hG : G.IsOriented)
    (v : V) (hvA : v ∈ C.A) :
    outsideHallSet G C v ⊆ G.secondOutNeighborFinset v := by
  intro w hw
  rcases Finset.mem_sdiff.mp hw with ⟨hwReach, hwOutside⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach with
    ⟨b, hbS, hbw⟩
  rcases Finset.mem_filter.mp hbS with ⟨hbB, hvb⟩
  have hNot : ¬G.Adj v w := by
    intro hvw
    have hCaptured :=
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG v hvA
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hvw)
    exact hwOutside hCaptured
  have hne : w ≠ v := by
    intro heq
    apply hwOutside
    rw [heq]
    exact Finset.mem_union_left _ hvA
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨b, hvb, hbw⟩, hNot, hne⟩

theorem hallNamedSet_subset_outside (C : G.LocalConfiguration) (hG : G.IsOriented)
    (v : V) : hallNamedSet G C v ⊆ outsideHallSet G C v := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨heExt, p, hpP, hvp, hpe⟩
  rw [outsideHallSet, Finset.mem_sdiff]
  constructor
  · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨
      Digraph.LocalConfiguration.P_subset_B (G := G) C hpP, hvp⟩, hpe⟩
  · intro heLocal
    exact (Finset.disjoint_left.mp
      (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG)) heLocal heExt

theorem qAnonymous_subset_outside (C : G.LocalConfiguration) (L : Labels G 3 C)
    (source : Nat) (hs : source < 8)
    (hBoth : reachesBothQ (graphArc G L) source = true) :
    qAnonymousSet G C ⊆ outsideHallSet G C (L.a ⟨source, hs⟩).1 := by
  intro w hw
  rcases Finset.mem_sdiff.mp hw with ⟨hwReach, hwOutside⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach with
    ⟨q, hqQ, hqw⟩
  obtain ⟨i, hi⟩ := L.q.surjective ⟨q, hqQ⟩
  have hBoth' := hBoth
  simp only [reachesBothQ, Bool.and_eq_true] at hBoth'
  have hvi : G.Adj (L.a ⟨source, hs⟩).1 (L.q i).1 := by
    by_cases hi0 : i.val = 0
    · have hieq : i = 0 := Fin.ext (by simpa using hi0)
      rw [hieq]
      have hArc := hBoth'.1
      rw [graphArc_AQ G L source 0 hs (by omega)] at hArc
      exact of_decide_eq_true hArc
    · have hi1 : i.val = 1 := by omega
      have hieq : i = 1 := Fin.ext (by simpa using hi1)
      rw [hieq]
      have hArc := hBoth'.2
      rw [graphArc_AQ G L source 1 hs (by omega)] at hArc
      exact of_decide_eq_true hArc
  rw [outsideHallSet, Finset.mem_sdiff]
  constructor
  · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
    refine ⟨(L.q i).1, Finset.mem_filter.mpr ⟨
      Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q i).2, hvi⟩, ?_⟩
    simpa [congrArg Subtype.val hi] using hqw
  · intro hwLocal
    apply hwOutside
    exact Finset.mem_union_left _ hwLocal

theorem outsideHall_lt_selected (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 8)
    (hInner : innerSeymour (graphArc G L) source = true) :
    (outsideHallSet G C (L.a ⟨source, hs⟩).1).card <
      (selectedB G C (L.a ⟨source, hs⟩).1).card := by
  let v := (L.a ⟨source, hs⟩).1
  let T := internalSecondNeighbors (G := G) C.A v
  let U := outsideHallSet G C v
  have hInternal := internalA_toNat G C L source hs
  have hSecond := innerSecondCount_toNat G C L hG source hs
  have hInnerNat : (Core.internalA (graphArc G L) source).toNat ≤
      (innerSecondCount (graphArc G L) source).toNat := by
    unfold innerSeymour at hInner
    simpa [BitVec.ule_eq_decide] using hInner
  have hTSub : T ⊆ G.secondOutNeighborFinset v := by
    intro w hw
    rcases Finset.mem_filter.mp hw with
      ⟨_, hNot, hne, middle, _, hFirst, hLast⟩
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨middle, hFirst, hLast⟩, hNot, hne⟩
  have hUSub : U ⊆ G.secondOutNeighborFinset v :=
    outsideHallSet_subset_second G C hG v (L.a _).2
  have hDis : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro w hwT hwU
    have hwA := (Finset.mem_filter.mp hwT).1
    exact (Finset.mem_sdiff.mp hwU).2 (Finset.mem_union_left C.B hwA)
  have hUnion : T ∪ U ⊆ G.secondOutNeighborFinset v :=
    Finset.union_subset hTSub hUSub
  have hCardUnion := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hDis] at hCardUnion
  have hNo := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hsV ↦ hNoSeymour ⟨v, hsV⟩)
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG v (L.a _).2
  have hDegree := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G v (localSet G C) hCap
  have hSplit := directCount_union_of_disjoint G C.A C.B v
    (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)
  change T.card + U.card ≤ G.secondOutdegree v at hCardUnion
  change U.card < directCount G C.B v
  rw [hDegree, localSet, hSplit] at hNo
  dsimp only [v] at hNo hCardUnion ⊢
  dsimp only [T] at hCardUnion
  dsimp only [U] at hCardUnion ⊢
  dsimp only [v] at hCardUnion ⊢
  omega

theorem selectedB_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (source : Nat) (hs : source < 8) :
    (aPOut (graphArc G L) source + qOut (graphArc G L) source).toNat =
      (selectedB G C (L.a ⟨source, hs⟩).1).card := by
  rw [BitVec.toNat_add, aPOut_toNat G C L source hs,
    qOut_toNat G C L source (by omega)]
  have hLV : localVertex G L source = (L.a ⟨source, hs⟩).1 := by
    simp [localVertex, hs]
  rw [hLV]
  have hP : directCount G C.P (L.a ⟨source, hs⟩).1 ≤ 5 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.p).symm)
  have hQ : directCount G C.Q (L.a ⟨source, hs⟩).1 ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.q).symm)
  rw [Nat.mod_eq_of_lt (by omega), ← directCount_union_of_disjoint G C.P C.Q _
    (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C),
    Digraph.LocalConfiguration.P_union_Q]
  rfl

theorem hallAugmented_le_outside (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 5) (source : Nat) (hs : source < 8)
    (hBoth : reachesBothQ (graphArc G L) source = true) :
    (hallCount (graphArc G L) (graphPToZ G L) source +
      qAnonymousLower (graphArc G L)).toNat ≤
      (outsideHallSet G C (L.a ⟨source, hs⟩).1).card := by
  let N := hallNamedSet G C (L.a ⟨source, hs⟩).1
  let Q := qAnonymousSet G C
  let U := outsideHallSet G C (L.a ⟨source, hs⟩).1
  have hNamed := hallCount_le_card G C L source hs
  have hAnon := qAnonymousLower_le_card G C L hG hMin hHCard
  have hNSub : N ⊆ U := hallNamedSet_subset_outside G C hG _
  have hQSub : Q ⊆ U := qAnonymous_subset_outside G C L source hs hBoth
  have hDis : Disjoint N Q := by
    rw [Finset.disjoint_left]
    intro v hvN hvQ
    have hvExt := (Finset.mem_filter.mp hvN).1
    exact (Finset.mem_sdiff.mp hvQ).2 (Finset.mem_union_right _ hvExt)
  have hUnion : N ∪ Q ⊆ U := Finset.union_subset hNSub hQSub
  have hCard := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hDis] at hCard
  have hHallBound :
      (hallCount (graphArc G L) (graphPToZ G L) source).toNat ≤ 3 := by
    rw [hallCount, BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount 3 _ (by omega)]
    exact BSixKThreeCoreGraphBridge.trueCount_le 3 _
  have hQBound : (qAnonymousLower (graphArc G L)).toNat ≤ 2 := by
    simp only [qAnonymousLower]
    split
    · decide
    · split <;> decide
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  dsimp [N, Q, U] at hNamed hAnon hCard ⊢
  omega

theorem hallCondition_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 5) :
    (allN 8 fun source ↦ hallCondition (graphArc G L) (graphPToZ G L) source) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro source hs
  unfold hallCondition
  by_cases hInner : innerSeymour (graphArc G L) source = true
  · rw [hInner]
    simp only [Bool.not_true, Bool.false_or]
    by_cases hOne : (qOut (graphArc G L) source == 1) = true
    · rw [hOne]
      rfl
    · have hOneFalse := Bool.eq_false_of_not_eq_true hOne
      rw [hOneFalse]
      simp only [Bool.false_or]
      simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
      have hOutside := outsideHall_lt_selected G C L hG hNoSeymour source hs hInner
      have hSelected := selectedB_toNat G C L source hs
      by_cases hBoth : reachesBothQ (graphArc G L) source = true
      · rw [if_pos hBoth]
        have hLower := hallAugmented_le_outside G C L hG hMin hHCard source hs hBoth
        rw [hSelected]
        omega
      · have hBothFalse := Bool.eq_false_of_not_eq_true hBoth
        rw [if_neg hBoth]
        have hLower := hallCount_le_card G C L source hs
        have hSub := hallNamedSet_subset_outside G C hG
          (L.a ⟨source, hs⟩).1
        have hCard := Finset.card_le_card hSub
        have hNamedThree : (hallNamedSet G C (L.a ⟨source, hs⟩).1).card ≤ 3 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            (by simpa using (Fintype.card_congr L.z).symm)
        rw [BitVec.toNat_add, BitVec.toNat_zero,
          Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
        rw [hSelected]
        omega
  · have hFalse := Bool.eq_false_of_not_eq_true hInner
    simp [hFalse]

theorem representedSecond_le_without_anonymous (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (u : Nat) (hu : u < 8) :
    (Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) u).toNat ≤
      (G.secondOutNeighborFinset (localVertex G L u) \ qAnonymousSet G C).card := by
  let arc := graphArc G L
  let ext := graphPToZ G L
  let source := localVertex G L u
  rw [Core.representedSecondCount, Core.secondLocal, BitVec.toNat_add,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount]
  · rw [Nat.mod_eq_of_lt (by
      have h1 := BSixKThreeCoreGraphBridge.trueCount_le 15
        (fun t ↦ decide (t ≠ u) && !arc u t && Core.reachedLocal arc u t)
      have h2 := BSixKThreeCoreGraphBridge.trueCount_le 3
        (Core.reachedExternal arc ext u)
      dsimp [arc, ext] at h1 h2
      simp only [ne_eq] at h1 ⊢
      omega)]
    have hInjective : Function.Injective
        (Sum.elim (fun i : Fin 15 ↦ (localEquiv G C L i).1)
          (fun i : Fin 3 ↦ (L.z i).1) : Fin 15 ⊕ Fin 3 → V) := by
      apply Sum.elim_injective.mpr
      refine ⟨fun _ _ h ↦ (localEquiv G C L).injective (Subtype.ext h),
        fun _ _ h ↦ L.z.injective (Subtype.ext h), ?_⟩
      intro i j hij
      exact (Finset.disjoint_left.mp
        (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
          (localEquiv G C L i).2 (hij ▸ (L.z j).2)
    apply BSixKThreeCoreGraphBridge.two_trueCounts_le_card
      (label₁ := fun i : Fin 15 ↦ (localEquiv G C L i).1)
      (label₂ := fun i : Fin 3 ↦ (L.z i).1)
      (hInjective := hInjective)
    · intro target hSelected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hSelected
      rcases hSelected with ⟨⟨hne, hNot⟩, hReach⟩
      rw [Core.reachedLocal, BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
      rcases hReach with ⟨middle, hm, hPath⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_, _⟩, hsm⟩, hmt⟩
      have hm13 : middle < 13 := by
        by_contra hn
        have hmA : ¬middle < 8 := by omega
        simp [graphArc, hmA, hn] at hmt
      have hsm' : G.Adj source (localVertex G L middle) := by
        simpa [arc, source, graphArc_eq_adj G C L u middle (by omega) (by omega)]
          using hsm
      have hmt' : G.Adj (localVertex G L middle) (localVertex G L target) := by
        simpa [arc, graphArc_eq_adj G C L middle target hm13 target.isLt] using hmt
      have hNot' : ¬G.Adj source (localVertex G L target) := by
        simpa [arc, source, graphArc_eq_adj G C L u target (by omega) target.isLt]
          using hNot
      have hne' : localVertex G L target ≠ source := by
        intro heq
        have hIdx : target = ⟨u, by omega⟩ :=
          (localEquiv G C L).injective (Subtype.ext (by
            rw [localEquiv_val, localEquiv_val]
            simpa [source] using heq))
        exact hne (Fin.ext_iff.mp hIdx)
      apply Finset.mem_sdiff.mpr
      constructor
      · rw [localEquiv_val, Digraph.mem_secondOutNeighborFinset,
          Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨localVertex G L middle, hsm', hmt'⟩, hNot', hne'⟩
      · intro hAnon
        exact (Finset.mem_sdiff.mp hAnon).2
          (Finset.mem_union_left _ (localEquiv G C L target).2)
    · intro target hReach
      rw [Core.reachedExternal, BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
      rcases hReach with ⟨p, hp, hPath⟩
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hsp, hpt⟩
      have hsp' : G.Adj source (L.p ⟨p, hp⟩).1 := by
        simpa [arc, source, localVertex, hu, graphArc_AP G L u p hu hp] using hsp
      have hpt' : G.Adj (L.p ⟨p, hp⟩).1 (L.z target).1 := by
        simpa [ext, graphPToZ_eq G L p target hp target.isLt] using hpt
      have hNot : ¬G.Adj source (L.z target).1 :=
        SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.A_not_adj_external
          G C hG source (L.z target).1 (by
            simp [source, localVertex, hu, (L.a _).2]) (L.z target).2
      have hne : (L.z target).1 ≠ source := by
        intro heq
        have hSourceA : source ∈ C.A := by
          simpa [source] using localVertex_mem_A G C L u hu
        exact (Finset.disjoint_left.mp
          (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
            (Finset.mem_union_left C.B hSourceA)
            (heq ▸ (L.z target).2)
      apply Finset.mem_sdiff.mpr
      constructor
      · rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨(L.p ⟨p, hp⟩).1, hsp', hpt'⟩, hNot, hne⟩
      · intro hAnon
        exact (Finset.mem_sdiff.mp hAnon).2
          (Finset.mem_union_right _ (L.z target).2)
  · omega
  · omega

theorem augmentedSecond_le (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 5) (u : Nat) (hu : u < 8)
    (hBoth : reachesBothQ (graphArc G L) u = true) :
    (Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) u +
      qAnonymousLower (graphArc G L)).toNat ≤
      G.secondOutdegree (localVertex G L u) := by
  let U := qAnonymousSet G C
  let S := G.secondOutNeighborFinset (localVertex G L u)
  have hRep := representedSecond_le_without_anonymous G C L hG u hu
  have hAnon := qAnonymousLower_le_card G C L hG hMin hHCard
  have hUSubOutside := qAnonymous_subset_outside G C L u hu hBoth
  have hLocalVertex : localVertex G L u = (L.a ⟨u, hu⟩).1 := by
    simp [localVertex, hu]
  have hUSub : U ⊆ S := by
    intro w hw
    change w ∈ G.secondOutNeighborFinset (localVertex G L u)
    rw [hLocalVertex]
    exact outsideHallSet_subset_second G C hG _ (L.a ⟨u, hu⟩).2
      (hUSubOutside hw)
  have hDis : Disjoint (S \ U) U := by
    rw [Finset.disjoint_left]
    exact fun _ hw hU ↦ (Finset.mem_sdiff.mp hw).2 hU
  have hUnion : (S \ U) ∪ U ⊆ S :=
    Finset.union_subset Finset.sdiff_subset hUSub
  have hCard := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hDis] at hCard
  have hRepBound :
      (Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) u).toNat ≤ 18 := by
    rw [Core.representedSecondCount, BitVec.toNat_add]
    have h1 := BSixKThreeCoreGraphBridge.trueCount_le 15
      (fun t ↦ decide (t ≠ u) && !graphArc G L u t &&
        Core.reachedLocal (graphArc G L) u t)
    have h2 := BSixKThreeCoreGraphBridge.trueCount_le 3
      (Core.reachedExternal (graphArc G L) (graphPToZ G L) u)
    rw [Core.secondLocal,
      BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount 15 _ (by omega),
      BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount 3 _ (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hQBound : (qAnonymousLower (graphArc G L)).toNat ≤ 2 := by
    simp only [qAnonymousLower]
    split
    · decide
    · split <;> decide
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  change _ ≤ S.card
  dsimp [U, S] at hRep hAnon hCard ⊢
  omega

theorem augmentedNonSeymour_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 5) :
    (allN 6 fun u ↦ Core.augmentedNonSeymour
      (graphArc G L) (graphPToZ G L) u) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro u hu
  unfold Core.augmentedNonSeymour
  have hLocal := localOut_toNat G C L u (by omega)
  let v := localVertex G L u
  have hvA : v ∈ C.A := localVertex_mem_A G C L u (by omega)
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG v hvA
  have hDegree := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G v (localSet G C) hCap
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩)
  have hPlain :
      (Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) u).toNat ≤
        G.secondOutdegree v := by
    simpa [v] using representedSecond_le G C L hG u (by omega) (by omega) (by omega)
  by_cases hBoth : reachesBothQ (graphArc G L) u = true
  · rw [if_pos hBoth]
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [hLocal, ← hDegree]
    exact (augmentedSecond_le G C L hG hMin hHCard u (by omega) hBoth).trans_lt
      hStrict
  · rw [if_neg hBoth]
    have hAdd : Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) u +
        0#8 =
          Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) u := by
      exact BitVec.add_zero _
    rw [hAdd]
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [hLocal, ← hDegree]
    exact hPlain.trans_lt hStrict

theorem rNonSeymour_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex) :
    (allN 2 fun r ↦
      (Core.representedSecondCount 3 (graphArc G L) (graphPToZ G L) (6 + r)).ult
        (Core.localOut (graphArc G L) (6 + r))) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro r hr
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hRep := representedSecond_le G C L hG (6 + r) (by omega) (by omega) (by omega)
  have hLocal := localOut_toNat G C L (6 + r) (by omega)
  let v := localVertex G L (6 + r)
  have hvA : v ∈ C.A := localVertex_mem_A G C L (6 + r) (by omega)
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG v hvA
  have hDegree := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G v (localSet G C) hCap
  rw [hLocal, ← hDegree]
  exact hRep.trans_lt (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩))

theorem representedPSecond_le (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (p : Nat) (hp : p < 5) :
    (Core.representedPSecondCount 3 (graphArc G L) (graphPToZ G L) (8 + p)).toNat ≤
      G.secondOutdegree (localVertex G L (8 + p)) := by
  let arc := graphArc G L
  let ext := graphPToZ G L
  let source := localVertex G L (8 + p)
  rw [Core.representedPSecondCount, Core.secondLocal, BitVec.toNat_add,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount]
  · rw [Nat.mod_eq_of_lt (by
      have h1 := BSixKThreeCoreGraphBridge.trueCount_le 15
        (fun t ↦ decide (t ≠ 8 + p) && !arc (8 + p) t &&
          Core.reachedLocal arc (8 + p) t)
      have h2 := BSixKThreeCoreGraphBridge.trueCount_le 3
        (Core.reachedExternalStrict arc ext (8 + p))
      dsimp [arc, ext] at h1 h2
      simp only [ne_eq] at h1 ⊢
      omega)]
    change _ ≤ (G.secondOutNeighborFinset source).card
    have hInjective : Function.Injective
        (Sum.elim (fun i : Fin 15 ↦ (localEquiv G C L i).1)
          (fun i : Fin 3 ↦ (L.z i).1) : Fin 15 ⊕ Fin 3 → V) := by
      apply Sum.elim_injective.mpr
      refine ⟨fun _ _ h ↦ (localEquiv G C L).injective (Subtype.ext h),
        fun _ _ h ↦ L.z.injective (Subtype.ext h), ?_⟩
      intro i j hij
      exact (Finset.disjoint_left.mp
        (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
          (localEquiv G C L i).2 (hij ▸ (L.z j).2)
    apply BSixKThreeCoreGraphBridge.two_trueCounts_le_card
      (label₁ := fun i : Fin 15 ↦ (localEquiv G C L i).1)
      (label₂ := fun i : Fin 3 ↦ (L.z i).1)
      (hInjective := hInjective)
    · intro target hSelected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hSelected
      rcases hSelected with ⟨⟨hne, hNot⟩, hReach⟩
      rw [Core.reachedLocal, BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
      rcases hReach with ⟨middle, hm, hPath⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_, _⟩, hsm⟩, hmt⟩
      have hm13 : middle < 13 := by
        by_contra hn
        have hmA : ¬middle < 8 := by omega
        simp [graphArc, hmA, hn] at hmt
      have hsm' : G.Adj source (localVertex G L middle) := by
        simpa [arc, source, graphArc_eq_adj G C L (8 + p) middle (by omega)
          (by omega)] using hsm
      have hmt' : G.Adj (localVertex G L middle) (localVertex G L target) := by
        simpa [arc, graphArc_eq_adj G C L middle target hm13 target.isLt] using hmt
      have hNot' : ¬G.Adj source (localVertex G L target) := by
        simpa [arc, source, graphArc_eq_adj G C L (8 + p) target (by omega)
          target.isLt] using hNot
      have hne' : localVertex G L target ≠ source := by
        intro heq
        have hIdx : target = ⟨8 + p, by omega⟩ :=
          (localEquiv G C L).injective (Subtype.ext (by
            rw [localEquiv_val, localEquiv_val]
            simpa [source] using heq))
        exact hne (Fin.ext_iff.mp hIdx)
      rw [localEquiv_val, Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨localVertex G L middle, hsm', hmt'⟩, hNot', hne'⟩
    · intro target hSelected
      rw [Core.reachedExternalStrict] at hSelected
      simp only [Bool.and_eq_true] at hSelected
      rcases hSelected with ⟨hNotDirect, hReach⟩
      rw [Core.reachedExternal, BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
      rcases hReach with ⟨middle, hm, hPath⟩
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hsm, hmt⟩
      have hsmLocal : G.Adj source (localVertex G L (8 + middle)) := by
        simpa [arc, source, graphArc_eq_adj G C L (8 + p)
          (8 + middle) (by omega) (by omega)] using hsm
      have hsm' : G.Adj source (L.p ⟨middle, hm⟩).1 := by
        simpa [localVertex, show ¬8 + middle < 8 by omega,
          show 8 + middle < 13 by omega] using hsmLocal
      have hmt' : G.Adj (L.p ⟨middle, hm⟩).1 (L.z target).1 := by
        simpa [ext, graphPToZ_eq G L middle target hm target.isLt] using hmt
      have hNot' : ¬G.Adj source (L.z target).1 := by
        have hFalse : graphPToZ G L p target = false := by
          simpa [show 8 + p - 8 = p by omega] using hNotDirect
        rw [graphPToZ_eq G L p target hp target.isLt] at hFalse
        have hSource : source = (L.p ⟨p, hp⟩).1 := by
          simp [source, localVertex, show ¬8 + p < 8 by omega,
            show 8 + p < 13 by omega]
        rw [hSource]
        exact of_decide_eq_false hFalse
      have hne : (L.z target).1 ≠ source := by
        intro heq
        have hSourceLocal : source ∈ localSet G C := by
          have h := (localEquiv G C L ⟨8 + p, by omega⟩).2
          rw [localEquiv_val] at h
          simpa [source] using h
        exact (Finset.disjoint_left.mp
          (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
            hSourceLocal (heq ▸ (L.z target).2)
      rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨(L.p ⟨middle, hm⟩).1, hsm', hmt'⟩, hNot', hne⟩
  · omega
  · omega

theorem pOut_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (p : Nat) (hp : p < 5) :
    (Core.localOut (graphArc G L) (8 + p) +
      sumN 3 (graphPToZ G L p)).toNat =
      G.outdegree (localVertex G L (8 + p)) := by
  rw [BitVec.toNat_add]
  have hLocal := localOut_toNat G C L (8 + p) (by omega)
  have hExt := externalOut_toNat G C L p hp (by omega) (by omega)
  rw [hLocal, hExt]
  have hpVertex : localVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [localVertex, show ¬8 + p < 8 by omega, show 8 + p < 13 by omega]
  rw [hpVertex]
  have hDis := BSixKThreeCoreGraphBridge.disjoint_local_external G C hG
  rw [Nat.mod_eq_of_lt (by
      have h1 : directCount G (localSet G C) (L.p ⟨p, hp⟩).1 ≤
          (localSet G C).card := Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤
          (externalTargets G C).card := Finset.card_le_card (Finset.filter_subset _ _)
      have hlc : (localSet G C).card = 15 := by
        simpa using (Fintype.card_congr (localEquiv G C L)).symm
      have hzc : (externalTargets G C).card = 3 := by
        simpa using (Fintype.card_congr L.z).symm
      omega), ← directCount_union_of_disjoint G (localSet G C)
        (externalTargets G C) (L.p ⟨p, hp⟩).1 hDis]
  have hCap : G.outNeighborFinset (L.p ⟨p, hp⟩).1 ⊆
      localSet G C ∪ externalTargets G C := by
    intro v hv
    have hv' := BSixKThree.P_outgoingCaptured_general G C hG
      (L.p ⟨p, hp⟩).1 (L.p _).2 hv
    rcases Finset.mem_union.mp hv' with hvLocal | hvExt
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hvLocal with hvHP | hvQ
      · rcases Finset.mem_union.mp hvHP with hvH | hvP
        · exact Finset.mem_union_left C.B
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
        · exact Finset.mem_union_right C.A
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
      · exact Finset.mem_union_right C.A
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
    · exact Finset.mem_union_right _ hvExt
  exact (BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured G
    (L.p ⟨p, hp⟩).1 _ hCap).symm

theorem pNonSeymour_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex) :
    (allN 5 fun p ↦
      (Core.representedPSecondCount 3 (graphArc G L) (graphPToZ G L) (8 + p)).ult
        (Core.localOut (graphArc G L) (8 + p) +
          sumN 3 (graphPToZ G L p))) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro p hp
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [pOut_toNat G C L hG p hp]
  exact (representedPSecond_le G C L hG p hp).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hs ↦ hNoSeymour ⟨localVertex G L (8 + p), hs⟩))

theorem hardCore_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hr : C.r = 5) (hx : C.x = 2)
    (hy : BSevenKThree.y G C = 2) (hHCard : C.H.card = 5) :
    Core.hardCore (graphArc G L) (graphPToZ G L) = true := by
  have hCore := core_true G C L hG hMin hNoSeymour hPivot hk hr
    (by omega) (by omega) hy
  have hDegree := degreeThreeConsequences_true G C L hG hPivot hk
  have hAOne := aOneInner_true G C L hG hPivot hk hx
  have hHall := hallCondition_true G C L hG hMin hNoSeymour hHCard
  have hAug := augmentedNonSeymour_true G C L hG hMin hNoSeymour hHCard
  have hR := rNonSeymour_true G C L hG hNoSeymour
  have hP := pNonSeymour_true G C L hG hNoSeymour
  rw [Core.hardCore]
  simp only [hCore, hDegree.1, hDegree.2, hAOne, hHall, hAug, hR, hP,
    Bool.and_true]

theorem contradiction
    (hCert : ∀ arc externalArc : Nat → Nat → Bool,
      Core.hardCore arc externalArc = false)
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hr : C.r = 5) (hx : C.x = 2)
    (hy : BSevenKThree.y G C = 2) (hHCard : C.H.card = 5) : False := by
  have hCore := hardCore_true G C L hG hMin hNoSeymour hPivot hk hr hx hy hHCard
  rw [hCert (graphArc G L) (graphPToZ G L)] at hCore
  contradiction

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.HardBridge
