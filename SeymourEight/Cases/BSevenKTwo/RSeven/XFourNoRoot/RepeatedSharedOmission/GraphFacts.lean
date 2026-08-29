import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.Encoding
import SeymourEight.Shared.FinsetBridge
import SeymourEight.Shared.LocalDegree
import SeymourEight.Shared.AlmostTournamentKing

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared RepeatedSharedOmissionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem p_eq_B (C : G.LocalConfiguration) (hBCard : C.B.card = 7)
    (hr : C.r = 7) : C.P = C.B := by
  apply Finset.eq_of_subset_of_card_le
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  change C.P.card = 7 at hr
  omega

/-- Every outgoing arc of a root outneighbor lands in `A ∪ B`. -/
theorem A_outgoingCaptured (C : G.LocalConfiguration) (hG : G.IsOriented)
    (u : V) (huA : u ∈ C.A) : G.outNeighborFinset u ⊆ C.A ∪ C.B := by
  intro v huvOut
  have huv : G.Adj u v := (Digraph.mem_outNeighborFinset (G := G)).mp huvOut
  by_cases hvA : v ∈ C.A
  · exact Finset.mem_union_left C.B hvA
  have hsu : G.Adj C.s u := (Digraph.mem_outNeighborFinset (G := G)).mp huA
  have hvs : v ≠ C.s := by
    intro h
    subst v
    exact hG.2 hsu huv
  have hvB : v ∈ C.B := by
    rw [Digraph.LocalConfiguration.B, Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨u, hsu, huv⟩,
      fun hsv ↦ hvA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv), hvs⟩
  exact Finset.mem_union_right C.A hvB

theorem P_not_adj_R (C : G.LocalConfiguration) (p r : V)
    (hp : p ∈ C.P) (hr : r ∈ C.R) : ¬G.Adj p r := by
  intro hpr
  have hrX : r ∈ C.X := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨p, Finset.mem_union_right C.A1 hp, hpr⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
      intro hParts
      apply (Finset.mem_sdiff.mp hr).2
      rcases Finset.mem_union.mp hParts with hrA1 | hra1
      · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hrA1)
      · exact Finset.mem_union_right (C.A1 ∪ C.X) hra1
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))

theorem A_not_adj_Z (C : G.LocalConfiguration) (_hG : G.IsOriented)
    (a z : V) (ha : a ∈ C.A) (hz : z ∈ C.Z) : ¬G.Adj a z := by
  intro haz
  have hsa : G.Adj C.s a := (Digraph.mem_outNeighborFinset (G := G)).mp ha
  have hzNotA : z ∉ C.A := by
    intro hzA
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
        (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hzA))
  have hzNotS : z ≠ C.s := by
    intro h
    subst z
    exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hz
  have hzB : z ∈ C.B := by
    rw [Digraph.LocalConfiguration.B, Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨a, hsa, haz⟩,
      fun hsz ↦ hzNotA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsz), hzNotS⟩
  exact (Finset.disjoint_left.mp
    (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
      (Finset.mem_union_right ({C.s} ∪ C.A) hzB)

theorem A1_not_adj_R (C : G.LocalConfiguration) (u r : V)
    (hu : u ∈ C.A1) (hr : r ∈ C.R) : ¬G.Adj u r := by
  intro hur
  have hrX : r ∈ C.X := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨u, Finset.mem_union_left C.P hu, hur⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
      intro hm
      apply (Finset.mem_sdiff.mp hr).2
      rcases Finset.mem_union.mp hm with hA1 | ha1
      · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1)
      · exact Finset.mem_union_right (C.A1 ∪ C.X) ha1
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))

def retainedVertexSet (C : G.LocalConfiguration) : Finset V := C.A ∪ C.P ∪ C.Z

def labelledVertex (L : Profile21111Labels G C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 15 then (L.p ⟨n - 8, by omega⟩).1
  else if hnZ : n < 19 then (L.z ⟨n - 15, by omega⟩).1
  else (L.z 0).1

noncomputable def retainedLabelEquiv (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) :
    Fin 19 ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin 19 → {v : V // v ∈ retainedVertexSet G C} := fun i =>
    if hiA : i.val < 8 then
      ⟨(L.a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left C.Z (Finset.mem_union_left C.P (L.a _).2)⟩
    else if hiP : i.val < 15 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left C.Z (Finset.mem_union_right C.A (L.p _).2)⟩
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
    have hAPZ : Disjoint (C.A ∪ C.P) C.Z := by
      rw [Finset.disjoint_left]
      intro v hvAP hvZ
      apply (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · exact Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA)
      · exact Finset.mem_union_right ({C.s} ∪ C.A)
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp,
      retainedVertexSet, Finset.card_union_of_disjoint hAPZ,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hz : C.Z.card = 4 := by simpa using (Fintype.card_congr L.z).symm
    simp [ha, hp, hz]

@[simp] theorem retainedLabelEquiv_val (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (i : Fin 19) :
    (retainedLabelEquiv G C L i).1 = labelledVertex G L i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hHCard : C.H.card = 6) :
    Fin 6 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 6 → {v : V // v ∈ C.H} := fun i =>
    ⟨(L.a ⟨i + 1, by omega⟩).1, by
      by_cases hi : i.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi⟩)
      · apply Finset.mem_union_right C.A1
        simpa [show i.val - 2 + 3 = i.val + 1 by omega] using
          L.a_x ⟨i - 2, by omega⟩⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have hidx : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval : i.val + 1 = j.val + 1 := congrArg Fin.val hidx
    omega
  · simpa using hHCard.symm

@[simp] theorem hLabelEquiv_val (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hHCard : C.H.card = 6)
    (i : Fin 6) :
    (hLabelEquiv G C L hHCard i).1 = (L.a ⟨i + 1, by omega⟩).1 := by
  rfl

theorem coreArc_coreBits (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hG : G.IsOriented)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (source target : Nat) (hs : source < 15) (ht : target < 19) :
    ThetaFourCore.coreArc
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hPLoop : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.p i).1 :=
    fun i => hG.1 _
  have hPOrient : ∀ i j : Fin 7, G.Adj (L.p i).1 (L.p j).1 →
      ¬G.Adj (L.p j).1 (L.p i).1 := by
    intro i j hij
    exact hG.2 hij
  have hA0P : ∀ i : Fin 7, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i => hG.2 (hA0P i)
  have hPR : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 7).1 :=
    fun i => P_not_adj_R G C _ _ (L.p i).2 L.a_r
  unfold ThetaFourCore.coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA, aArc_coreBits G.Adj _ _ _ source target hsA htA]
      simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP]
        have hti : target - 8 < 7 := by omega
        simp only [ThetaFourCore.aToP]
        by_cases hs0 : source = 0
        · subst source
          simp [hA0P, labelledVertex, htA, htP]
        by_cases hs7 : source < 7
        · have hsh : source - 1 < 6 := by omega
          rw [if_neg hs0, if_pos hs7, ThetaFourCore.hToP,
            pToH_coreBits G.Adj _ _ _ (target - 8) (source - 1) hti hsh]
          have haeq : (L.a ⟨source - 1 + 1, by omega⟩).1 =
              (L.a ⟨source, hsA⟩).1 := by
            have hiEq : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
                ⟨source, hsA⟩ := Fin.ext (by simp; omega)
            rw [hiEq]
          rw [haeq]
          rcases hPHComplete ⟨target - 8, hti⟩ ⟨source - 1, hsh⟩ with hp | hh
          · have hn := hG.2 hp
            rw [haeq] at hp hn
            simp [hp, hn, labelledVertex, hsA, htA, htP]
          · have hn := hG.2 hh
            rw [haeq] at hh hn
            simp [hh, hn, labelledVertex, hsA, htA, htP]
        · have hs7eq : source = 7 := by omega
          subst source
          rw [if_neg (by omega : ¬7 = 0), if_neg (by omega : ¬7 < 7),
            rToP_coreBits G.Adj _ _ _ (target - 8) hti]
          simp [labelledVertex, htA, htP]
      · simp [htP, ht, labelledVertex, hsA, htA,
          A_not_adj_Z G C hG (L.a ⟨source, hsA⟩).1
            (L.z ⟨target - 15, by omega⟩).1 (L.a _).2 (L.z _).2]
  · have hsP : source < 15 := hs
    rw [if_neg hsA, if_pos hsP]
    by_cases htA : target < 8
    · rw [if_pos htA]
      simp only [ThetaFourCore.pToA]
      by_cases htH : 0 < target ∧ target < 7
      · rw [if_pos (by simpa [Bool.and_eq_true] using htH)]
        rw [pToH_coreBits G.Adj _ _ _ (source - 8) (target - 1)
          (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, show target - 1 + 1 = target by omega]
      · rw [if_neg (by simpa [Bool.and_eq_true] using htH)]
        have htCase : target = 0 ∨ target = 7 := by omega
        rcases htCase with rfl | rfl
        · simp [labelledVertex, hsA, hsP, hP0]
        · simp [labelledVertex, hsA, hsP, hPR]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP, pArc_coreBits G.Adj _ _ _ hPLoop hPComplete hPOrient
          (source - 8) (target - 8) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, htP]
      · rw [if_neg htP]
        have htZ : target < 19 := ht
        rw [if_pos htZ, pToZ_coreBits G.Adj _ _ _ (source - 8) (target - 15)
          (by omega) (by omega)]
        have hTarget : labelledVertex G L target =
            (L.z ⟨target - 15, by omega⟩).1 := by
          simp [labelledVertex, htA, htP, ht]
        have hSource : labelledVertex G L source =
            (L.p ⟨source - 8, by omega⟩).1 := by
          simp [labelledVertex, hsA, hsP]
        rw [hSource, hTarget]

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
