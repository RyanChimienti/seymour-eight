import SeymourEight.Cases.BSevenKTwo.RSix.XThreeNoRoot.UnreachedEncoding
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.BooleanBridge
import SeymourEight.Cases.BSevenKTwo.RSeven.XThreeNoRoot.GraphFacts
import SeymourEight.Cases.BSixKThree.Counting
import Mathlib.Data.Bool.Basic

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedGraphFacts

open Shared Shared.FiniteCore Labels UnreachedEncoding Core UnreachedCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def retainedSet (C : G.LocalConfiguration) (q : V) : Finset V :=
  C.A ∪ C.P ∪ (C.Z ∪ {q})

def labelledVertex (L : UnreachedLabels G C q) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 14 then (L.p ⟨n - 8, by omega⟩).1
  else if hnZ : n < 18 then (L.z ⟨n - 14, by omega⟩).1
  else if n = 18 then q else C.s

noncomputable def retainedEquiv (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : UnreachedLabels G C q) :
    Fin 19 ≃ {v : V // v ∈ retainedSet G C q} := by
  let f : Fin 19 → {v : V // v ∈ retainedSet G C q} := fun i =>
    if hiA : i.val < 8 then
      ⟨(L.a ⟨i, hiA⟩).1,
        Finset.mem_union_left (C.Z ∪ {q})
          (Finset.mem_union_left C.P (L.a _).2)⟩
    else if hiP : i.val < 14 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left (C.Z ∪ {q})
          (Finset.mem_union_right C.A (L.p _).2)⟩
    else if hiZ : i.val < 18 then
      ⟨(L.z ⟨i.val - 14, by omega⟩).1,
        Finset.mem_union_right (C.A ∪ C.P)
          (Finset.mem_union_left {q} (L.z _).2)⟩
    else ⟨q, Finset.mem_union_right (C.A ∪ C.P)
      (Finset.mem_union_right C.Z (by simp))⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAP | hvE
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega,
          show i.val + 8 < 14 by omega] using congrArg Subtype.val hi
    · rcases Finset.mem_union.mp hvE with hvZ | hvq
      · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
        refine ⟨⟨i.val + 14, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 14 < 8 by omega,
          show ¬i.val + 14 < 14 by omega,
          show i.val + 14 < 18 by omega] using congrArg Subtype.val hi
      · refine ⟨18, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hvq).symm
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hEAP : Disjoint (C.A ∪ C.P) (C.Z ∪ {q}) := by
      rw [Finset.disjoint_left]
      intro v hvAP hvE
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · rcases Finset.mem_union.mp hvE with hvZ | hvq
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
            (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
        · have hv : v = q := Finset.mem_singleton.mp hvq
          subst v
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
      · rcases Finset.mem_union.mp hvE with hvZ | hvq
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
        · have hv : v = q := Finset.mem_singleton.mp hvq
          subst v
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hqQ
    rw [show Fintype.card {v : V // v ∈ retainedSet G C q} =
        (retainedSet G C q).card by simp,
      retainedSet, Finset.card_union_of_disjoint hEAP,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have hz : C.Z.card = 4 := by
      simpa using (Fintype.card_congr L.z).symm
    have hqNotZ : q ∉ C.Z := by
      intro hqZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqZ
        (Finset.mem_union_right ({C.s} ∪ C.A)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
    have he : (C.Z ∪ {q}).card = 5 := by simp [hz, hqNotZ]
    have hfin : Fintype.card (Fin 19) = 19 := by simp
    omega

noncomputable def hEquiv (C : G.LocalConfiguration) (q : V)
    (L : UnreachedLabels G C q) (hHCard : C.H.card = 5) :
    Fin 5 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 5 → {v : V // v ∈ C.H} := fun i =>
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, by
      by_cases hi : i.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi⟩)
      · exact Finset.mem_union_right C.A1 (by
          simpa [show i.val - 2 + 3 = i.val + 1 by omega] using
            L.a_x ⟨i.val - 2, by omega⟩)⟩
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
    have haval : i.val + 1 = j.val + 1 := Fin.ext_iff.mp ha
    omega
  · simpa using hHCard.symm

@[simp] theorem hEquiv_val (C : G.LocalConfiguration) (q : V)
    (L : UnreachedLabels G C q) (hHCard : C.H.card = 5) (i : Fin 5) :
    (hEquiv G C q L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

noncomputable def aOneEquiv (C : G.LocalConfiguration) (q : V)
    (L : UnreachedLabels G C q) (hk : C.k = 2) :
    Fin 2 ≃ {v : V // v ∈ C.A1} := by
  let f : Fin 2 → {v : V // v ∈ C.A1} := fun i =>
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
    have hv : i.val + 1 = j.val + 1 := Fin.ext_iff.mp ha
    omega
  · change C.A1.card = 2 at hk
    simpa using hk.symm

@[simp] theorem aOneEquiv_val (C : G.LocalConfiguration) (q : V)
    (L : UnreachedLabels G C q) (hk : C.k = 2) (i : Fin 2) :
    (aOneEquiv G C q L hk i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

noncomputable def xEquiv (C : G.LocalConfiguration) (q : V)
    (L : UnreachedLabels G C q) (hx : C.x = 3) :
    Fin 3 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 3 → {v : V // v ∈ C.X} := fun i =>
    ⟨(L.a ⟨i.val + 3, by omega⟩).1, L.a_x i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 3, by omega⟩ : Fin 8) =
        ⟨j.val + 3, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hv : i.val + 3 = j.val + 3 := Fin.ext_iff.mp ha
    omega
  · change C.X.card = 3 at hx
    simpa using hx.symm

@[simp] theorem xEquiv_val (C : G.LocalConfiguration) (q : V)
    (L : UnreachedLabels G C q) (hx : C.x = 3) (i : Fin 3) :
    (xEquiv G C q L hx i).1 = (L.a ⟨i.val + 3, by omega⟩).1 := rfl

@[simp] theorem retainedEquiv_val (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : UnreachedLabels G C q) (i : Fin 19) :
    (retainedEquiv G C q hqQ L i).1 = labelledVertex G L i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 14
  · simp [retainedEquiv, labelledVertex, hiA, hiP]
  by_cases hiZ : i.val < 18
  · simp [retainedEquiv, labelledVertex, hiA, hiP, hiZ]
  · have hi18 : i.val = 18 := by omega
    simp [retainedEquiv, labelledVertex, hi18]

def pivotNeighborSet (C : G.LocalConfiguration) : Finset V := C.A1 ∪ C.P

def representedTargetSet (C : G.LocalConfiguration) : Finset V := C.X ∪ C.Z

def pivotNeighborVertex (L : UnreachedLabels G C q) (i : Nat) : V :=
  labelledVertex G L (UnreachedCore.uVertex i)

def representedTargetVertex (L : UnreachedLabels G C q) (i : Nat) : V :=
  labelledVertex G L (UnreachedCore.secondTarget i)

noncomputable def pivotNeighborEquiv (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : UnreachedLabels G C q) (hk : C.k = 2) :
    Fin 8 ≃ {v : V // v ∈ pivotNeighborSet G C} := by
  let f : Fin 8 → {v : V // v ∈ pivotNeighborSet G C} := fun i ↦
    ⟨pivotNeighborVertex G L i.val, by
      by_cases hi : i.val < 2
      · apply Finset.mem_union_left C.P
        change labelledVertex G L (UnreachedCore.uVertex i.val) ∈ C.A1
        rw [show UnreachedCore.uVertex i.val = 1 + i.val by simp [UnreachedCore.uVertex, hi]]
        have hv : labelledVertex G L (1 + i.val) =
            (L.a ⟨1 + i.val, by omega⟩).1 := by
          simp only [labelledVertex, dif_pos (by omega : 1 + i.val < 8)]
        rw [hv]
        simpa [Nat.add_comm] using L.a_aOne ⟨i.val, hi⟩
      · apply Finset.mem_union_right C.A1
        change labelledVertex G L (UnreachedCore.uVertex i.val) ∈ C.P
        rw [show UnreachedCore.uVertex i.val = 6 + i.val by simp [UnreachedCore.uVertex, hi]]
        simp [labelledVertex, show ¬6 + i.val < 8 by omega,
          show 6 + i.val < 14 by omega]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    have hIndex : UnreachedCore.uVertex i.val = UnreachedCore.uVertex j.val := by
      have hFin : (⟨UnreachedCore.uVertex i.val, by unfold UnreachedCore.uVertex; split <;> omega⟩ : Fin 19) =
          ⟨UnreachedCore.uVertex j.val, by unfold UnreachedCore.uVertex; split <;> omega⟩ := by
        apply (retainedEquiv G C q hqQ L).injective
        apply Subtype.ext
        simpa [retainedEquiv_val, f, pivotNeighborVertex] using
          congrArg Subtype.val hij
      exact Fin.ext_iff.mp hFin
    apply Fin.ext
    simp only [UnreachedCore.uVertex] at hIndex
    split at hIndex <;> split at hIndex <;> omega
  · have hDis : Disjoint C.A1 C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
        (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA)
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    rw [show Fintype.card {v : V // v ∈ pivotNeighborSet G C} =
        (pivotNeighborSet G C).card by simp,
      pivotNeighborSet, Finset.card_union_of_disjoint hDis]
    have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    change C.A1.card = 2 at hk
    simp [hk, hp]

@[simp] theorem pivotNeighborEquiv_val (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : UnreachedLabels G C q) (hk : C.k = 2) (i : Fin 8) :
    (pivotNeighborEquiv G C q hqQ L hk i).1 =
      pivotNeighborVertex G L i.val := rfl

noncomputable def representedTargetEquiv (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : UnreachedLabels G C q) (hx : C.x = 3) :
    Fin 7 ≃ {v : V // v ∈ representedTargetSet G C} := by
  let f : Fin 7 → {v : V // v ∈ representedTargetSet G C} := fun i ↦
    ⟨representedTargetVertex G L i.val, by
      by_cases hi : i.val < 3
      · apply Finset.mem_union_left C.Z
        change labelledVertex G L (UnreachedCore.secondTarget i.val) ∈ C.X
        rw [show UnreachedCore.secondTarget i.val = 3 + i.val by simp [UnreachedCore.secondTarget, hi]]
        have hv : labelledVertex G L (3 + i.val) =
            (L.a ⟨3 + i.val, by omega⟩).1 := by
          simp only [labelledVertex, dif_pos (by omega : 3 + i.val < 8)]
        rw [hv]
        simpa [Nat.add_comm] using L.a_x ⟨i.val, hi⟩
      · apply Finset.mem_union_right C.X
        change labelledVertex G L (UnreachedCore.secondTarget i.val) ∈ C.Z
        rw [show UnreachedCore.secondTarget i.val = 11 + i.val by simp [UnreachedCore.secondTarget, hi]]
        simp [labelledVertex, show ¬11 + i.val < 8 by omega,
          show ¬11 + i.val < 14 by omega, show 11 + i.val < 18 by omega]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    have hIndex : UnreachedCore.secondTarget i.val = UnreachedCore.secondTarget j.val := by
      have hFin : (⟨UnreachedCore.secondTarget i.val,
          by unfold UnreachedCore.secondTarget; split <;> omega⟩ : Fin 19) =
          ⟨UnreachedCore.secondTarget j.val, by unfold UnreachedCore.secondTarget; split <;> omega⟩ := by
        apply (retainedEquiv G C q hqQ L).injective
        apply Subtype.ext
        simpa [retainedEquiv_val, f, representedTargetVertex] using
          congrArg Subtype.val hij
      exact Fin.ext_iff.mp hFin
    apply Fin.ext
    simp only [UnreachedCore.secondTarget] at hIndex
    split at hIndex <;> split at hIndex <;> omega
  · have hDis : Disjoint C.X C.Z := by
      rw [Finset.disjoint_left]
      intro v hvX hvZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
        (Finset.mem_union_right C.A1 hvX)
    rw [show Fintype.card {v : V // v ∈ representedTargetSet G C} =
        (representedTargetSet G C).card by simp,
      representedTargetSet, Finset.card_union_of_disjoint hDis]
    have he : C.Z.card = 4 := by
      simpa using (Fintype.card_congr L.z).symm
    change C.X.card = 3 at hx
    rw [he]
    simp [hx]

@[simp] theorem representedTargetEquiv_val (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : UnreachedLabels G C q) (hx : C.x = 3) (i : Fin 7) :
    (representedTargetEquiv G C q hqQ L hx i).1 =
      representedTargetVertex G L i.val := rfl

private abbrev graphBits (L : UnreachedLabels G C q) : UnreachedCore.Encoding :=
  UnreachedEncoding.coreBits G.Adj L

theorem coreArc_graphBits (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hqUnreached : q ∉ reachedQ G C)
    (L : UnreachedLabels G C q) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 14) (ht : target < 19) :
    UnreachedCore.coreArc (graphBits G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  have hA0P : ∀ i : Fin 6, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 6, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i => hG.2 (hA0P i)
  have hA0Q : ¬G.Adj (L.a 0).1 q := by
    rw [L.a_zero]
    intro ha1q
    exact (Finset.mem_sdiff.mp hqQ).2
      (Finset.mem_filter.mpr ⟨Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ,
        ha1q⟩)
  have hPq : ∀ i : Fin 6, ¬G.Adj (L.p i).1 q := by
    intro i hi
    apply hqUnreached
    exact Finset.mem_inter.mpr ⟨hqQ,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨(L.p i).1, Finset.mem_union_right C.A1 (L.p i).2, hi⟩⟩
  have hPR : ∀ i : Fin 6, ∀ r : Fin 2,
      ¬G.Adj (L.p i).1 (L.a ⟨r + 6, by omega⟩).1 :=
    fun i r => RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
      G C _ _ (L.p i).2 (L.a_r r)
  unfold UnreachedCore.coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA, aArc_coreBits G.Adj L source target hsA htA]
      simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 14
      · rw [if_pos htP]
        unfold Core.aToP
        by_cases hs0 : source = 0
        · subst source; simp [hA0P, labelledVertex, htA, htP]
        by_cases hsH : source < 6
        · rw [if_neg hs0, if_pos hsH]
          change hToP (graphBits G L) (source - 1) (target - 8) = _
          rw [hToP_coreBits G.Adj L (source - 1) (target - 8)
            (by omega) (by omega)]
          have hfin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          simp [labelledVertex, hsA, htA, htP, hfin]
        · rw [if_neg hs0, if_neg hsH]
          change rToP (graphBits G L) (source - 6) (target - 8) = _
          rw [rToP_coreBits G.Adj L (source - 6) (target - 8)
            (by omega) (by omega)]
          have hfin : (⟨source - 6 + 6, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          simp [labelledVertex, hsA, htA, htP, hfin]
      · by_cases htZ : target < 18
        · rw [if_neg htP, if_pos htZ]
          have hnot := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
            G C hG (L.a ⟨source, hsA⟩).1 (L.z ⟨target - 14, by omega⟩).1
            (L.a _).2 (L.z _).2
          simp only [labelledVertex, dif_pos hsA, dif_neg htA,
            dif_neg htP, dif_pos htZ]
          exact (decide_eq_false_iff_not.mpr hnot).symm
        · have htq : target = 18 := by omega
          subst target
          rw [if_neg htP, if_neg (by omega : ¬18 < 18), if_pos rfl,
            aToQ_coreBits G.Adj L source hsA]
          by_cases hs0 : source = 0
          · subst source
            simp only [labelledVertex, dif_pos (by omega : 0 < 8),
              dif_neg (by omega : ¬18 < 8), dif_neg (by omega : ¬18 < 14),
              dif_neg (by omega : ¬18 < 18), ne_eq,
              not_true_eq_false]
            exact (decide_eq_false_iff_not.mpr (by simpa using hA0Q)).symm
          · simp only [labelledVertex, dif_pos hsA,
              dif_neg (by omega : ¬18 < 8), dif_neg (by omega : ¬18 < 14),
              dif_neg (by omega : ¬18 < 18)]
            rw [show decide (source ≠ 0 ∧
                G.Adj (L.a ⟨source, hsA⟩).1 q) =
                decide (G.Adj (L.a ⟨source, hsA⟩).1 q) by
              exact Bool.decide_congr ⟨And.right, fun h => ⟨hs0, h⟩⟩]
            simp
  · have hsP : source < 14 := hs
    rw [if_neg hsA, if_pos hsP]
    by_cases htA : target < 8
    · rw [if_pos htA]
      unfold Core.pToA
      by_cases htH : 0 < target ∧ target < 6
      · rw [if_pos (by simpa [Bool.and_eq_true] using htH)]
        change pToH (graphBits G L) (source - 8) (target - 1) = _
        rw [pToH_coreBits G.Adj L (source - 8) (target - 1)
          (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, show target - 1 + 1 = target by omega]
      · rw [if_neg (by simpa [Bool.and_eq_true] using htH)]
        have hc : target = 0 ∨ target = 6 ∨ target = 7 := by omega
        rcases hc with rfl | rfl | rfl
        · simp [labelledVertex, hsA, hsP, hP0]
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 0
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 1
    · rw [if_neg htA]
      by_cases htP : target < 14
      · rw [if_pos htP, pArc_coreBits G.Adj L (source - 8) (target - 8)
          (by omega) (by omega)]
        have himp : G.Adj (L.p ⟨source - 8, by omega⟩).1
            (L.p ⟨target - 8, by omega⟩).1 → source - 8 ≠ target - 8 := by
          intro ha heq
          apply hG.1 (L.p ⟨source - 8, by omega⟩).1
          have hf : (⟨source - 8, by omega⟩ : Fin 6) =
              ⟨target - 8, by omega⟩ := Fin.ext heq
          simpa [hf] using ha
        rw [show decide (source - 8 ≠ target - 8 ∧
            G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) =
            decide (G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) by
          exact Bool.decide_congr ⟨And.right, fun h => ⟨himp h, h⟩⟩]
        simp [labelledVertex, hsA, hsP, htA, htP]
      · by_cases htZ : target < 18
        · rw [if_neg htP, if_pos htZ,
            pToZ_coreBits G.Adj L (source - 8) (target - 14) (by omega) (by omega)]
          simp [labelledVertex, hsA, hsP, htA, htP, htZ]
        · have htq : target = 18 := by omega
          subst target
          rw [if_neg htP, if_neg (by omega : ¬18 < 18)]
          simp only [labelledVertex, dif_neg (by omega : ¬18 < 8),
            dif_neg (by omega : ¬18 < 14), dif_neg (by omega : ¬18 < 18),
            hsA, hsP]
          exact (decide_eq_false_iff_not.mpr (hPq ⟨source - 8, by omega⟩)).symm


theorem directCount_graphBits_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (hqUnreached : q ∉ reachedQ G C)
    (L : UnreachedLabels G C q)
    (hG : G.IsOriented) (hNoRoot : epsilonS G C = 0)
    (source : Nat) (hs : source < 14) :
    (UnreachedCore.directCount (graphBits G L) source).toNat =
      G.outdegree (labelledVertex G L source) := by
  rw [UnreachedCore.directCount, toNat_count_eq_fin_sum 19 _ (by omega)]
  have hCount : (∑ j : Fin 19, if UnreachedCore.coreArc (graphBits G L) source j then 1 else 0) =
      Shared.directCount G (retainedSet G C q) (labelledVertex G L source) := by
    symm
    apply directCount_eq_sum_bool G (retainedSet G C q)
      (retainedEquiv G C q hqQ L) _
    intro j
    rw [retainedEquiv_val,
      coreArc_graphBits G C q hqQ hqUnreached L hG source j hs j.isLt]
    simp
  rw [hCount]
  apply (outdegree_eq_directCount_of_captured G _ _ ?_).symm
  by_cases hsA : source < 8
  · simp only [labelledVertex, dif_pos hsA]
    intro v hv
    rcases Finset.mem_union.mp
        (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
          G C hG _ (L.a _).2 hv) with hvA | hvB
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvA)
    · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C, hQ] at hvB
      rcases Finset.mem_union.mp hvB with hvP | hvq
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvP)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hvq)
  · simp only [labelledVertex, dif_neg hsA, dif_pos hs]
    intro v hv
    have hc := BSixKThree.P_outgoingCaptured_general G C hG
      (L.p ⟨source - 8, by omega⟩).1 (L.p _).2 hv
    rcases Finset.mem_union.mp hc with hvLocal | hvExt
    · rcases Finset.mem_union.mp hvLocal with hvHP | hvQ
      · rcases Finset.mem_union.mp hvHP with hvH | hvP
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvP)
      · rw [hQ] at hvQ
        exact Finset.mem_union_right _ (Finset.mem_union_right _ hvQ)
    · have hRootEmpty : rootSecondFinset G C = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [epsilonS] using hNoRoot
      have hExt : externalTargets G C = C.Z := by
        simp [externalTargets, hRootEmpty]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (hExt ▸ hvExt))

theorem strictSecondLocal_true_mem (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hqUnreached : q ∉ reachedQ G C)
    (L : UnreachedLabels G C q) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 14) (ht : target < 19)
    (hSecond : UnreachedCore.strictSecondLocal (graphBits G L) source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  simp only [UnreachedCore.strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 14 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_graphBits G C q hqQ hqUnreached L hG source middle hs
    (by omega)] at hFirst
  rw [coreArc_graphBits G C q hqQ hqUnreached L hG middle target hm ht] at hLast
  rw [coreArc_graphBits G C q hqQ hqUnreached L hG source target hs ht] at hNotArc
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 19) = ⟨source, by omega⟩ := by
      apply (retainedEquiv G C q hqQ L).injective
      apply Subtype.ext
      simpa using heq
    have hneNat : target ≠ source := by simpa using hne
    exact hneNat (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

theorem localSecondCount_le_graph (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hqUnreached : q ∉ reachedQ G C)
    (L : UnreachedLabels G C q) (hG : G.IsOriented)
    (source : Nat) (hs : source < 14) :
    (UnreachedCore.localSecondCount (graphBits G L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  have hFiltered := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.GraphFacts.count_le_filterCard
    (V := V) (retainedSet G C q) (retainedEquiv G C q hqQ L)
    (UnreachedCore.strictSecondLocal (graphBits G L) source)
    (fun v => v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    (by omega) (by
      intro j hj
      rw [retainedEquiv_val]
      exact strictSecondLocal_true_mem G C q hqQ hqUnreached L hG
        source j hs j.isLt hj)
  unfold UnreachedCore.localSecondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

theorem nonSeymour_graphBits_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (hqUnreached : q ∉ reachedQ G C)
    (L : UnreachedLabels G C q)
    (hG : G.IsOriented) (hNoRoot : epsilonS G C = 0)
    (hNoSeymour : ¬G.HasSeymourVertex) (source : Nat) (hs : source < 14) :
    (UnreachedCore.localSecondCount (graphBits G L) source).ult
      (UnreachedCore.directCount (graphBits G L) source) = true := by
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [directCount_graphBits_toNat G C q hqQ hQ hqUnreached L hG hNoRoot source hs]
  exact (localSecondCount_le_graph G C q hqQ hqUnreached L hG source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h => hNoSeymour ⟨labelledVertex G L source, h⟩))

theorem aOut_toNat (C : G.LocalConfiguration) (q : V) (L : UnreachedLabels G C q)
    (source : Nat) (hs : source < 8) :
    (Core.aOut (graphBits G L) source).toNat =
      Shared.directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [Core.aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  rw [aArc_coreBits G.Adj L source j hs j.isLt]
  simp

theorem aPOut_toNat (C : G.LocalConfiguration) (q : V) (L : UnreachedLabels G C q)
    (source : Nat) (hs : source < 8) :
    (Core.aPOut (graphBits G L) source).toNat =
      Shared.directCount G C.P (L.a ⟨source, hs⟩).1 := by
  rw [Core.aPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  unfold Core.aToP
  by_cases hs0 : source = 0
  · subst source
    rw [if_pos rfl]
    simp only [true_iff]
    have ha0 : (⟨0, hs⟩ : Fin 8) = 0 := Fin.ext (by simp)
    rw [ha0, L.a_zero]
    exact (Finset.mem_filter.mp (L.p j).2).2
  by_cases hsH : source < 6
  · rw [if_neg hs0, if_pos hsH]
    rw [hToP_coreBits G.Adj L (source - 1) j (by omega) j.isLt]
    have ha : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
        ⟨source, hs⟩ := Fin.ext (by simp; omega)
    simp [ha]
  · rw [if_neg hs0, if_neg hsH]
    rw [rToP_coreBits G.Adj L (source - 6) j (by omega) j.isLt]
    have ha : (⟨source - 6 + 6, by omega⟩ : Fin 8) =
        ⟨source, hs⟩ := Fin.ext (by simp; omega)
    simp [ha]

theorem aBOut_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : UnreachedLabels G C q)
    (source : Nat) (hs : source < 8) :
    (Core.aBOut (graphBits G L) source).toNat =
      Shared.directCount G C.B (L.a ⟨source, hs⟩).1 := by
  rw [Core.aBOut, BitVec.toNat_add, aPOut_toNat G C q L source hs]
  have hqCount : (bitCount (Core.aToQ (graphBits G L) source)).toNat =
      Shared.directCount G {q} (L.a ⟨source, hs⟩).1 := by
    rw [aToQ_coreBits G.Adj L source hs]
    by_cases hs0 : source = 0
    · subst source
      have hn : ¬G.Adj (L.a 0).1 q := by
        rw [L.a_zero]
        intro ha
        exact (Finset.mem_sdiff.mp hqQ).2
          (Finset.mem_filter.mpr ⟨Digraph.LocalConfiguration.Q_subset_B
            (G := G) C hqQ, ha⟩)
      rw [Shared.directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_eq_empty_iff.mpr (by
          intro x hx
          have hxq : x = q := Finset.mem_singleton.mp hx
          subst x
          exact hn)]
      simp [bitCount]
    · by_cases ha : G.Adj (L.a ⟨source, hs⟩).1 q <;>
        simp [bitCount, Shared.directCount,
          CertificateBridge.internalFirstNeighbors, hs0, ha,
          Finset.filter_singleton]
  rw [hqCount]
  have hDis : Disjoint C.P {q} := by
    rw [Finset.disjoint_left]
    intro v hvP hvq
    have hv : v = q := Finset.mem_singleton.mp hvq
    subst v
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hqQ
  have hSmall : Shared.directCount G C.P (L.a ⟨source, hs⟩).1 +
      Shared.directCount G {q} (L.a ⟨source, hs⟩).1 < 256 := by
    have h1 : Shared.directCount G C.P (L.a ⟨source, hs⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : Shared.directCount G {q} (L.a ⟨source, hs⟩).1 ≤ ({q} : Finset V).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have hqcard : ({q} : Finset V).card = 1 := by simp
    omega
  rw [Nat.mod_eq_of_lt hSmall,
    ← directCount_union_of_disjoint G C.P {q} _ hDis]
  have hPBq : C.P ∪ {q} = C.B := by
    rw [← hQ]
    exact Digraph.LocalConfiguration.P_union_Q (G := G) C
  rw [hPBq]

theorem pBlockCounts (C : G.LocalConfiguration) (q : V) (L : UnreachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 5)
    (p : Nat) (hp : p < 6) :
    (Core.pOut (graphBits G L) p).toNat =
        Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ∧
    (Core.pHOut (graphBits G L) p).toNat =
        Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ∧
    (Core.pEOut (graphBits G L) p).toNat =
        Shared.directCount G C.Z (L.p ⟨p, hp⟩).1 := by
  constructor
  · rw [Core.pOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P L.p _
    intro j
    rw [pArc_coreBits G.Adj L p j hp j.isLt]
    by_cases hpj : p = j.val
    · have hn : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.p j).1 := by
        have he : (⟨p, hp⟩ : Fin 6) = j := Fin.ext hpj
        simpa [he] using hG.1 (L.p j).1
      have he : (⟨p, hp⟩ : Fin 6) = j := Fin.ext hpj
      simp [hpj, hG.1 (L.p j).1]
    · simp [hpj]
  constructor
  · rw [Core.pHOut, toNat_count_eq_fin_sum 5 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H (hEquiv G C q L hHCard) _
    intro j
    rw [pToH_coreBits G.Adj L p j hp j.isLt]
    simp
  · rw [Core.pEOut, toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Z L.z _
    intro j
    rw [pToZ_coreBits G.Adj L p j hp j.isLt]
    simp

theorem hPOut_toNat (C : G.LocalConfiguration) (q : V) (L : UnreachedLabels G C q)
    (h : Nat) (hh : h < 5) :
    (Core.hPOut (graphBits G L) h).toNat =
      Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1 := by
  rw [Core.hPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [hToP_coreBits G.Adj L h j hh j.isLt]
  simp

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedGraphFacts
