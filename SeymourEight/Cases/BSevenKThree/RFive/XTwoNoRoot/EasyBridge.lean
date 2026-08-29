import SeymourEight.Cases.BSevenKThree.RFive.XTwoNoRoot.Encoding
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.GraphFacts
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.BooleanBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.EasyBridge

open Shared CertificateBridge Labels Encoding
open SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def localSet (C : G.LocalConfiguration) : Finset V := C.A ∪ C.B

noncomputable def localEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : Fin 15 ≃ {v : V // v ∈ localSet G C} := by
  let f : Fin 15 → {v : V // v ∈ localSet G C} := fun i ↦
    if hiA : i.val < 8 then ⟨(L.a ⟨i, hiA⟩).1, by simp [localSet, (L.a _).2]⟩
    else if hiP : i.val < 13 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1, by
        simp [localSet, Digraph.LocalConfiguration.P_subset_B (G := G) C (L.p _).2]⟩
    else ⟨(L.q ⟨i.val - 13, by omega⟩).1, by
      simp [localSet, Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q _).2]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvA | hvB
    · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
      refine ⟨⟨i, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, i.isLt] using congrArg Subtype.val hi
    · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hvB
      rcases Finset.mem_union.mp hvB with hvP | hvQ
      · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega,
          show i.val + 8 < 13 by omega] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hvQ⟩
        refine ⟨⟨i.val + 13, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 13 < 8 by omega,
          show ¬i.val + 13 < 13 by omega] using congrArg Subtype.val hi
  · have hAB := Digraph.LocalConfiguration.disjoint_A_B (G := G) C
    rw [show Fintype.card {v : V // v ∈ localSet G C} = (localSet G C).card by simp,
      localSet, Finset.card_union_of_disjoint hAB,
      ← Digraph.LocalConfiguration.P_union_Q (G := G) C,
      Finset.card_union_of_disjoint
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
    have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
    simp [ha, hp, hq]

@[simp] theorem localEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (i : Fin 15) :
    (localEquiv G C L i).1 = localVertex G L i := by
  by_cases hiA : i.val < 8
  · simp [localEquiv, localVertex, hiA]
  by_cases hiP : i.val < 13
  · simp [localEquiv, localVertex, hiA, hiP]
  · simp [localEquiv, localVertex, hiA, hiP]

theorem graphArc_eq_adj {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (i j : Nat) (hi : i < 13) (hj : j < 15) :
    graphArc G L i j = decide (G.Adj (localVertex G L i) (localVertex G L j)) := by
  by_cases hiA : i < 8
  · by_cases hjA : j < 8
    · simp [graphArc, localVertex, hiA, hjA]
    · by_cases hjP : j < 13
      · simp [graphArc, localVertex, hiA, hjA, hjP]
      · simp [graphArc, localVertex, hiA, hjA, hjP, hj]
  · by_cases hjA : j < 8
    · simp [graphArc, localVertex, hiA, hjA, hi]
    · by_cases hjP : j < 13
      · simp [graphArc, localVertex, hiA, hjA, hi, hjP]
      · simp [graphArc, localVertex, hiA, hjA, hi, hjP, hj]

theorem localOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (u : Nat) (hu : u < 13) :
    (localOut (graphArc G L) u).toNat =
      directCount G (localSet G C) (localVertex G L u) := by
  rw [localOut]
  have h := BSixKThreeCoreGraphBridge.toNat_sumN_equiv G (localSet G C)
    (localEquiv G C L) (localVertex G L u) (by omega) (by omega)
  rw [← h]
  apply congrArg BitVec.toNat
  apply BSixKThreeCoreGraphBridge.sumN_congr
  intro j hj
  rw [graphArc_eq_adj G C L u j hu hj, localEquiv_val]
  simp [Nat.mod_eq_of_lt hj]

theorem internalA_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (u : Nat) (hu : u < 8) :
    (internalA (graphArc G L) u).toNat = directCount G C.A (L.a ⟨u, hu⟩).1 := by
  have h := BSixKThreeCoreGraphBridge.toNat_sumN_equiv G C.A L.a
    (L.a ⟨u, hu⟩).1 (by omega) (by omega)
  rw [internalA, ← h]
  apply congrArg BitVec.toNat
  apply BSixKThreeCoreGraphBridge.sumN_congr
  intro j hj
  rw [graphArc_A G L u j hu hj]
  simp [Nat.mod_eq_of_lt hj]

noncomputable def bEquiv {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) : Fin 7 ≃ {v : V // v ∈ C.B} := by
  let f : Fin 7 → {v : V // v ∈ C.B} := fun i ↦
    if hi : i.val < 5 then
      ⟨(L.p ⟨i, hi⟩).1,
        Digraph.LocalConfiguration.P_subset_B (G := G) C (L.p _).2⟩
    else ⟨(L.q ⟨i.val - 5, by omega⟩).1,
      Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hv
    rcases Finset.mem_union.mp hv with hvP | hvQ
    · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
      refine ⟨⟨i, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, i.isLt] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hvQ⟩
      refine ⟨⟨i.val + 5, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 5 < 5 by omega] using congrArg Subtype.val hi
  · simp only [Fintype.card_fin, Fintype.card_coe]
    rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
      Finset.card_union_of_disjoint
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)]
    have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
    have hq : C.Q.card = 2 := by simpa using (Fintype.card_congr L.q).symm
    simp [hp, hq]

@[simp] theorem bEquiv_val {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (i : Fin 7) :
    (bEquiv G C L i).1 = localVertex G L (8 + i.val) := by
  by_cases hi : i.val < 5
  · simp [bEquiv, localVertex, hi, show 8 + i.val < 13 by omega]
  · have heq : (⟨i.val - 5, by omega⟩ : Fin 2) =
        ⟨8 + i.val - 13, by omega⟩ := Fin.ext (by simp; omega)
    simp [bEquiv, localVertex, hi, show ¬8 + i.val < 13 by omega,
      show 8 + i.val < 15 by omega, heq]

theorem outB_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (u : Nat) (hu : u < 8) :
    (outB (graphArc G L) u).toNat = directCount G C.B (L.a ⟨u, hu⟩).1 := by
  have h := BSixKThreeCoreGraphBridge.toNat_sumN_equiv G C.B (bEquiv G C L)
    (L.a ⟨u, hu⟩).1 (by omega) (by omega)
  rw [outB, ← h]
  apply congrArg BitVec.toNat
  apply BSixKThreeCoreGraphBridge.sumN_congr
  intro j hj
  rw [graphArc_eq_adj G C L u (8 + j) (by omega) (by omega), bEquiv_val]
  simp [localVertex, hu, Nat.mod_eq_of_lt hj]

theorem externalOut_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (p : Nat) (hp : p < 5)
    (hzPos : 0 < zCount) (hz : zCount < 256) :
    (SeymourEight.BSixKThreeCore.sumN zCount (graphPToZ G L p)).toNat =
      directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
  have h := BSixKThreeCoreGraphBridge.toNat_sumN_equiv G
    (externalTargets G C) L.z (L.p ⟨p, hp⟩).1 hzPos hz
  rw [← h]
  apply congrArg BitVec.toNat
  apply BSixKThreeCoreGraphBridge.sumN_congr
  intro j hj
  rw [graphPToZ_eq G L p j hp hj]
  simp [Nat.mod_eq_of_lt hj]

theorem representedSecond_le {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (u : Nat) (hu : u < 8) (hzPos : 0 < zCount) (hz : zCount < 16) :
    (representedSecondCount zCount (graphArc G L) (graphPToZ G L) u).toNat ≤
      G.secondOutdegree (localVertex G L u) := by
  let arc := graphArc G L
  let ext := graphPToZ G L
  let source := localVertex G L u
  have hCountBound : 15 + zCount < 256 := by omega
  rw [representedSecondCount, secondLocal, BitVec.toNat_add,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount,
    BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount]
  · rw [Nat.mod_eq_of_lt (lt_of_le_of_lt
      (Nat.add_le_add (BSixKThreeCoreGraphBridge.trueCount_le 15 _)
        (BSixKThreeCoreGraphBridge.trueCount_le zCount _)) hCountBound)]
    change _ ≤ (G.secondOutNeighborFinset source).card
    have hInjective : Function.Injective
        (Sum.elim (fun i : Fin 15 ↦ (localEquiv G C L i).1)
          (fun i : Fin zCount ↦ (L.z i).1) : Fin 15 ⊕ Fin zCount → V) := by
      apply Sum.elim_injective.mpr
      refine ⟨fun _ _ h ↦ (localEquiv G C L).injective (Subtype.ext h),
        fun _ _ h ↦ L.z.injective (Subtype.ext h), ?_⟩
      intro i j hij
      exact (Finset.disjoint_left.mp
        (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
          (localEquiv G C L i).2 (hij ▸ (L.z j).2)
    apply BSixKThreeCoreGraphBridge.two_trueCounts_le_card
      (label₁ := fun i : Fin 15 ↦ (localEquiv G C L i).1)
      (label₂ := fun i : Fin zCount ↦ (L.z i).1)
      (hInjective := hInjective)
    · intro target hSelected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hSelected
      rcases hSelected with ⟨⟨hne, hNot⟩, hReach⟩
      rw [reachedLocal, BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
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
        simpa [arc, graphArc_eq_adj G C L middle target hm13 target.isLt]
          using hmt
      have hNot' : ¬G.Adj source (localVertex G L target) := by
        simpa [arc, source, graphArc_eq_adj G C L u target (by omega) target.isLt]
          using hNot
      have hTargetSource : localVertex G L target ≠ source := by
        intro heq
        have hIdx : target = ⟨u, by omega⟩ :=
          (localEquiv G C L).injective (Subtype.ext (by
            rw [localEquiv_val, localEquiv_val]
            simpa [source] using heq))
        exact hne (Fin.ext_iff.mp hIdx)
      rw [localEquiv_val, Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨localVertex G L middle, hsm', hmt'⟩, hNot', hTargetSource⟩
    · intro target hReach
      rw [reachedExternal, BSixKThreeCoreGraphBridge.anyN_eq_true_iff] at hReach
      rcases hReach with ⟨p, hp, hPath⟩
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hsp, hpt⟩
      have hsp' : G.Adj source (L.p ⟨p, hp⟩).1 := by
        simpa [arc, source, localVertex, show u < 8 by omega,
          graphArc_AP G L u p (by omega) hp] using hsp
      have hpt' : G.Adj (L.p ⟨p, hp⟩).1 (L.z target).1 := by
        simpa [ext, graphPToZ_eq G L p target hp target.isLt] using hpt
      have hNot : ¬G.Adj source (L.z target).1 :=
        SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.A_not_adj_external
          G C hG source (L.z target).1 (by
            have huA : localVertex G L u ∈ C.A := by
              simp [localVertex, show u < 8 by omega, (L.a _).2]
            exact huA) (L.z target).2
      have hTargetSource : (L.z target).1 ≠ source := by
        intro heq
        have huLocal := (localEquiv G C L ⟨u, by omega⟩).2
        rw [localEquiv_val] at huLocal
        have hzSource : source ∈ externalTargets G C := heq ▸ (L.z target).2
        exact (Finset.disjoint_left.mp
          (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG))
            huLocal hzSource
      rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨(L.p ⟨p, hp⟩).1, hsp', hpt'⟩, hNot, hTargetSource⟩
  · omega
  · omega

theorem oriented_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    (SeymourEight.BSixKThreeCore.allN 15 fun i ↦ !graphArc G L i i &&
      SeymourEight.BSixKThreeCore.allN 15 fun j ↦
      decide (i = j) || !(graphArc G L i j && graphArc G L j i)) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true, BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  constructor
  · by_cases hi13 : i < 13
    · rw [graphArc_eq_adj G C L i i hi13 hi]
      simpa using hG.1 (localVertex G L i)
    · have hiA : ¬i < 8 := by omega
      simp [graphArc, hi13, hiA]
  · intro j hj
    by_cases hij : i = j
    · simp [hij]
    by_cases hi13 : i < 13
    · by_cases hj13 : j < 13
      · rw [graphArc_eq_adj G C L i j hi13 hj,
          graphArc_eq_adj G C L j i hj13 hi]
        by_cases ha : G.Adj (localVertex G L i) (localVertex G L j)
        · simp [hij, ha, hG.2 ha]
        · simp [hij, ha]
      · have hjA : ¬j < 8 := by omega
        simp [graphArc, hi13, hj13, hjA, hij]
    · have hiA : ¬i < 8 := by omega
      simp [graphArc, hi13, hiA, hij]

theorem fixed_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    (SeymourEight.BSixKThreeCore.allN 15 fun j ↦ graphArc G L 0 j ==
      decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 13)) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro j hj
  by_cases hjA : j < 8
  · have hzero : (L.a ⟨0, by omega⟩).1 = C.a1 := by simpa using L.a_zero
    rw [graphArc_A G L 0 j (by omega) hjA, hzero]
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
          intro heq
          subst j
          exact hG.1 C.a1 (by simpa [L.a_zero] using ha)
        by_cases hj6 : j < 6
        · have heq : (⟨j, hjA⟩ : Fin 8) = ⟨(j - 4) + 4, by omega⟩ :=
            Fin.ext (by simp; omega)
          have hx : (L.a ⟨j, hjA⟩).1 ∈ C.X := by
            rw [heq]; exact L.a_x ⟨j - 4, by omega⟩
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hm hx
        · have heq : (⟨j, hjA⟩ : Fin 8) = ⟨(j - 6) + 6, by omega⟩ :=
            Fin.ext (by simp; omega)
          have hr : (L.a ⟨j, hjA⟩).1 ∈ C.R := by
            rw [heq]; exact L.a_r ⟨j - 6, by omega⟩
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C))
              (Finset.mem_union_left _ (Finset.mem_union_left _ hm)) hr
      simp [hA1, hn, show ¬(8 ≤ j ∧ j < 13) by omega]
  · by_cases hjP : j < 13
    · have hp : j - 8 < 5 := by omega
      have ha : G.Adj C.a1 (L.p ⟨j - 8, hp⟩).1 :=
        (Finset.mem_filter.mp (L.p ⟨j - 8, hp⟩).2).2
      have hzero : (L.a ⟨0, by omega⟩).1 = C.a1 := by simpa using L.a_zero
      have hjEq : j = 8 + (j - 8) := by omega
      rw [hjEq, graphArc_AP G L 0 (j - 8) (by omega) hp, hzero]
      simp [ha, show 8 ≤ j by omega, hjP]
    · have hjQ : 13 ≤ j := by omega
      have hn : ¬G.Adj C.a1 (localVertex G L j) := by
        intro ha
        have hqMem : localVertex G L j ∈ C.Q := by
          simp [localVertex, hjA, hjP, hj, (L.q _).2]
        exact (Finset.mem_sdiff.mp hqMem).2
          (Finset.mem_filter.mpr ⟨
            Digraph.LocalConfiguration.Q_subset_B (G := G) C hqMem, ha⟩)
      rw [graphArc_eq_adj G C L 0 j (by omega) hj]
      have hn' : ¬G.Adj (localVertex G L 0) (localVertex G L j) := by
        simpa [localVertex, L.a_zero] using hn
      simp [hn', show ¬(1 ≤ j ∧ j ≤ 3) by omega,
        show ¬(8 ≤ j ∧ j < 13) by omega]

theorem noR_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    ((SeymourEight.BSixKThreeCore.allN 3 fun i ↦
        SeymourEight.BSixKThreeCore.allN 2 fun j ↦ !graphArc G L (1 + i) (6 + j)) &&
      (SeymourEight.BSixKThreeCore.allN 5 fun i ↦
        SeymourEight.BSixKThreeCore.allN 2 fun j ↦ !graphArc G L (8 + i) (6 + j))) = true := by
  simp only [Bool.and_eq_true, BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  constructor
  · intro i hi j hj
    rw [graphArc_A G L (1 + i) (6 + j) (by omega) (by omega)]
    have hn := BSixKThreeCoreGraphBridge.A1_not_adj_R G C hG
      (L.a ⟨1 + i, by omega⟩).1 (L.a ⟨6 + j, by omega⟩).1
      (by simpa [Nat.add_comm] using L.a_aOne ⟨i, hi⟩)
      (by simpa [Nat.add_comm] using L.a_r ⟨j, hj⟩)
    simp [hn]
  · intro i hi j hj
    rw [graphArc_PA G L i (6 + j) hi (by omega)]
    have hn := BSixKThreeCoreGraphBridge.P_not_adj_R G C
      (L.p ⟨i, hi⟩).1 (L.a ⟨6 + j, by omega⟩).1 (L.p _).2
      (by simpa [Nat.add_comm] using L.a_r ⟨j, hj⟩)
    simp [hn]

theorem localVertex_mem_A {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (u : Nat) (hu : u < 8) : localVertex G L u ∈ C.A := by
  simp [localVertex, show u < 8 by omega, (L.a _).2]

theorem hRows_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hr : C.r = 5) :
    (SeymourEight.BSixKThreeCore.allN 5 fun h ↦
      pivotRow (graphArc G L) (1 + h) &&
        (8 : BitVec 8).ule (localOut (graphArc G L) (1 + h))) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro h hh
  rw [Bool.and_eq_true]
  let u := (L.a ⟨1 + h, by omega⟩).1
  have huA : u ∈ C.A := (L.a _).2
  have hInternal := internalA_toNat G C L (1 + h) (by omega)
  have hB := outB_toNat G C L (1 + h) (by omega)
  have hLocal := localOut_toNat G C L (1 + h) (by omega)
  have hLV : localVertex G L (1 + h) = u := by
    simp [localVertex, u, show 1 + h < 8 by omega]
  rw [hLV] at hLocal
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG u huA
  have hDegree := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G u (localSet G C) hCap
  have hp := hPivot u huA
  dsimp [u] at hp hDegree ⊢
  constructor
  · rw [pivotRow, Bool.and_eq_true]
    constructor
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hInternal]
      simpa [hk, Shared.directCount, CertificateBridge.internalFirstNeighbors]
        using hp.1
    · rw [Bool.or_eq_true]
      by_cases heq : internalA (graphArc G L) (1 + h) = 3
      · right
        simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
        rw [hB]
        have hCard : Shared.directCount G C.A u = C.k := by
          rw [← hInternal, congrArg BitVec.toNat heq, hk]
          decide
        have htie := hp.2 (by
          simpa [Shared.directCount, CertificateBridge.internalFirstNeighbors] using hCard)
        simpa [hr, Shared.directCount, CertificateBridge.internalFirstNeighbors]
          using htie
      · left
        simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
        change 3 < (internalA (graphArc G L) (1 + h)).toNat
        have hGe : 3 ≤ (internalA (graphArc G L) (1 + h)).toNat := by
          rw [hInternal]
          have hpi := hp.1
          change C.k ≤ Shared.directCount G C.A (L.a ⟨1 + h, by omega⟩).1 at hpi
          omega
        have hNe : (internalA (graphArc G L) (1 + h)).toNat ≠ 3 := by
          intro hn
          apply heq
          apply BitVec.eq_of_toNat_eq
          simpa using hn
        omega
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [hLocal, ← hDegree]
    exact hMin u

theorem pRows_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hzPos : 0 < zCount)
    (hz : zCount < 16) :
    (SeymourEight.BSixKThreeCore.allN 5 fun p ↦ (8 : BitVec 8).ule
      (localOut (graphArc G L) (8 + p) +
        SeymourEight.BSixKThreeCore.sumN zCount (graphPToZ G L p))) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add]
  have hLocal := localOut_toNat G C L (8 + p) (by omega)
  have hExt := externalOut_toNat G C L p hp hzPos (by omega)
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
      have hzc : (externalTargets G C).card = zCount := by
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
  rw [← BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured G
    (L.p ⟨p, hp⟩).1 _ hCap]
  exact hMin _

theorem nonSeymour_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hzPos : 0 < zCount) (hz : zCount < 16) :
    (SeymourEight.BSixKThreeCore.allN 6 fun u ↦
      (representedSecondCount zCount (graphArc G L) (graphPToZ G L) u).ult
        (localOut (graphArc G L) u)) = true := by
  rw [BSixKThreeCoreGraphBridge.allN_eq_true_iff]
  intro u hu
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hRep := representedSecond_le G C L hG u (by omega) hzPos hz
  have hLocal := localOut_toNat G C L u (by omega)
  let v := localVertex G L u
  have hvA : v ∈ C.A := localVertex_mem_A G C L u (by omega)
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG v hvA
  have hDegree := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G v (localSet G C) hCap
  rw [hLocal, ← hDegree]
  exact hRep.trans_lt (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩))

theorem qReached_true_iff {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) (q : Nat) (hq : q < 2) :
    qReached (graphArc G L) q = true ↔ (L.q ⟨q, hq⟩).1 ∈ reachedQ G C := by
  rw [qReached, Bool.or_eq_true]
  constructor
  · intro h
    rcases h with hA | hP
    · obtain ⟨i, hi, hArc⟩ :=
        (BSixKThreeCoreGraphBridge.anyN_eq_true_iff 3 _).mp hA
      rw [graphArc_AQ G L (1 + i) q (by omega) hq] at hArc
      rw [reachedQ, Finset.mem_inter]
      exact ⟨(L.q _).2, (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨(L.a ⟨1 + i, by omega⟩).1,
          Finset.mem_union_left _ (by
            simpa [Nat.add_comm] using L.a_aOne ⟨i, hi⟩),
          of_decide_eq_true hArc⟩⟩
    · obtain ⟨p, hp, hArc⟩ :=
        (BSixKThreeCoreGraphBridge.anyN_eq_true_iff 5 _).mp hP
      rw [graphArc_PQ G L p q hp hq] at hArc
      rw [reachedQ, Finset.mem_inter]
      exact ⟨(L.q _).2, (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨(L.p ⟨p, hp⟩).1, Finset.mem_union_right _ (L.p _).2,
          of_decide_eq_true hArc⟩⟩
  · intro hm
    rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_inter.mp hm).2 with ⟨u, hu, huq⟩
    rcases Finset.mem_union.mp hu with huA | huP
    · left
      rw [BSixKThreeCoreGraphBridge.anyN_eq_true_iff]
      obtain ⟨i, hi⟩ := L.a.surjective ⟨u,
        Digraph.LocalConfiguration.A1_subset_A (G := G) C huA⟩
      have hiRange : 1 ≤ i.val ∧ i.val ≤ 3 := by
        have hiA1 : (L.a i).1 ∈ C.A1 := by
          simpa [congrArg Subtype.val hi] using huA
        have hiAdj : G.Adj C.a1 (L.a i).1 := (Finset.mem_filter.mp hiA1).2
        constructor
        · have hiNe : i ≠ 0 := by
            intro hz
            rw [hz, L.a_zero] at hiAdj
            exact hG.1 C.a1 hiAdj
          omega
        · by_contra hn
          have hi4 : 4 ≤ i.val := by omega
          by_cases hi6 : i.val < 6
          · have heq : i = ⟨(i.val - 4) + 4, by omega⟩ :=
              Fin.ext (by simp; omega)
            have hiX : (L.a i).1 ∈ C.X := by
              rw [heq]; exact L.a_x ⟨i.val - 4, by omega⟩
            exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hiA1 hiX
          · have heq : i = ⟨(i.val - 6) + 6, by omega⟩ :=
              Fin.ext (by simp; omega)
            have hiR : (L.a i).1 ∈ C.R := by
              rw [heq]; exact L.a_r ⟨i.val - 6, by omega⟩
            exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C))
                (Finset.mem_union_left _ (Finset.mem_union_left _ hiA1)) hiR
      refine ⟨i.val - 1, by omega, ?_⟩
      rw [graphArc_AQ G L (1 + (i.val - 1)) q (by omega) hq]
      simpa [show 1 + (i.val - 1) = i.val by omega,
        congrArg Subtype.val hi] using decide_eq_true huq
    · right
      rw [BSixKThreeCoreGraphBridge.anyN_eq_true_iff]
      obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [graphArc_PQ G L i q i.isLt hq]
      simpa [congrArg Subtype.val hi] using decide_eq_true huq

theorem qReachCount_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    (SeymourEight.BSixKThreeCore.sumN 2 (qReached (graphArc G L))).toNat =
      BSevenKThree.y G C := by
  rw [BSixKThreeCoreGraphBridge.toNat_sumN_eq_trueCount 2 _ (by omega),
    BSixKThreeCoreGraphBridge.trueCount_eq_filter_fin]
  change ((Finset.univ : Finset (Fin 2)).filter
      (fun i ↦ qReached (graphArc G L) i.val = true)).card = (reachedQ G C).card
  let f : {i : Fin 2 // qReached (graphArc G L) i.val = true} →
      {v : V // v ∈ reachedQ G C} := fun i ↦
    ⟨(L.q i.val).1,
      (qReached_true_iff G C L hG i.val i.val.isLt).mp i.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      dsimp [f] at hij ⊢
      have hv : (L.q i.val).1 = (L.q j.val).1 :=
        congrArg (fun x : {v : V // v ∈ reachedQ G C} ↦ x.1) hij
      apply Subtype.ext
      apply L.q.injective
      apply Subtype.ext
      exact hv
    · rintro ⟨v, hv⟩
      obtain ⟨i, hi⟩ := L.q.surjective ⟨v, (Finset.mem_inter.mp hv).1⟩
      have hiReach : qReached (graphArc G L) i = true :=
        (qReached_true_iff G C L hG i i.isLt).mpr (by
          simpa [congrArg Subtype.val hi] using hv)
      refine ⟨⟨i, hiReach⟩, ?_⟩
      apply Subtype.ext
      dsimp [f]
      exact congrArg Subtype.val hi
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  have hdomain : Fintype.card {i : Fin 2 // qReached (graphArc G L) i.val = true} =
      ((Finset.univ : Finset (Fin 2)).filter
        (fun i ↦ qReached (graphArc G L) i.val = true)).card := by
    apply Fintype.card_ofFinset
  rw [← hdomain]
  simpa using hcard

theorem qReachStatus_true {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hy : BSevenKThree.y G C = yValue) :
    SeymourEight.BSixKThreeCore.sumN 2 (qReached (graphArc G L)) ==
      BitVec.ofNat 8 yValue := by
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [qReachCount_toNat G C L hG, hy]
  have hyLt : yValue < 256 := by
    rw [← hy]
    change (reachedQ G C).card < 256
    have hSub : reachedQ G C ⊆ C.Q := Finset.inter_subset_left
    have hQCard : C.Q.card = 2 := by
      simpa using (Fintype.card_congr L.q).symm
    have := Finset.card_le_card hSub
    omega
  simp [Nat.mod_eq_of_lt hyLt]

theorem core_true {zCount yValue : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 3) (hr : C.r = 5)
    (hzPos : 0 < zCount) (hz : zCount < 16)
    (hy : BSevenKThree.y G C = yValue) :
    core zCount yValue (graphArc G L) (graphPToZ G L) = true := by
  have hOr := oriented_true G C L hG
  have hFixed := fixed_true G C L hG
  have hR := noR_true G C L hG
  have hQ := qReachStatus_true G C L hG hy
  have hH := hRows_true G C L hG hPivot hMin hk hr
  have hP := pRows_true G C L hG hMin hzPos hz
  have hNS := nonSeymour_true G C L hG hNoSeymour hzPos hz
  rw [core]
  simp only [hOr, hFixed, hR, hQ, hH, hP, hNS, Bool.true_and,
    Bool.and_true]

theorem contradiction {zCount yValue : Nat}
    (hCert : ∀ arc externalArc : Nat → Nat → Bool,
      core zCount yValue arc externalArc = false)
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hr : C.r = 5) (hzPos : 0 < zCount)
    (hz : zCount < 16) (hy : BSevenKThree.y G C = yValue) : False := by
  have hCore := core_true G C L hG hMin hNoSeymour hPivot hk hr hzPos hz hy
  rw [hCert (graphArc G L) (graphPToZ G L)] at hCore
  contradiction
end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.EasyBridge
