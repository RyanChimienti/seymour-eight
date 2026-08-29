import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Labels
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Structure
import SeymourEight.Certificates.BSevenKThree.RSeven.XTwo.High
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.GraphFacts

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.HighBridge

open Shared Shared.FiniteCore Labels Structure
open Shared.InnerDegreeThree
open SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.HighCore
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def graphArc {zCount : Nat} (L : Labels G zCount C) (i j : Nat) : Bool :=
  if hi : i < 8 then if hj : j < 8 then
    decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1)
  else false else false

theorem oriented_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    oriented (graphArc G L) = true := by
  rw [oriented, all_eq_true_iff]
  intro i hi
  simp only [graphArc, dif_pos hi, Bool.and_eq_true]
  constructor
  · simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    simp only [dif_pos hj]
    by_cases heq : i = j
    · simp [heq]
    by_cases hadj : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
    · simp [heq, hadj, hG.2 hadj]
    · simp [heq, hadj]

theorem fixedPivotRow_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    fixedPivotRow (graphArc G L) = true := by
  rw [fixedPivotRow, all_eq_true_iff]
  intro target ht
  simp only [graphArc, dif_pos (by omega : 0 < 8), dif_pos ht]
  have hZero : (L.a ⟨0, by omega⟩).1 = C.a1 := by
    have heq : (⟨0, by omega⟩ : Fin 8) = 0 := Fin.ext rfl
    rw [heq, L.a_zero]
  by_cases hA1 : 1 ≤ target ∧ target ≤ 3
  · have hadj : G.Adj (L.a ⟨0, by omega⟩).1 (L.a ⟨target, ht⟩).1 := by
      rw [hZero]
      have hTarget : (L.a ⟨target, ht⟩).1 =
          (L.a ⟨(target - 1) + 1, by omega⟩).1 := by
        congr 2
        apply Fin.ext
        change target = target - 1 + 1
        omega
      rw [hTarget]
      exact (Finset.mem_filter.mp (L.a_aOne ⟨target - 1, by omega⟩)).2
    simp [hA1]
    simpa using hadj
  · have hn : ¬G.Adj (L.a ⟨0, by omega⟩).1 (L.a ⟨target, ht⟩).1 := by
      intro hadj
      have hm : (L.a ⟨target, ht⟩).1 ∈ C.A1 := by
        apply Finset.mem_filter.mpr
        rw [← hZero]
        exact ⟨(L.a _).2, hadj⟩
      rcases show target = 0 ∨ (4 ≤ target ∧ target ≤ 5) ∨
          (6 ≤ target ∧ target ≤ 7) by omega with h0 | hX | hR
      · have heq : (⟨target, ht⟩ : Fin 8) = 0 := Fin.ext h0
        rw [heq, L.a_zero] at hadj
        rw [hZero] at hadj
        exact hG.1 C.a1 hadj
      · have heq : (⟨target, ht⟩ : Fin 8) =
            ⟨(target - 4) + 4, by omega⟩ := Fin.ext (by simp; omega)
        rw [heq] at hm
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hm
            (L.a_x ⟨target - 4, by omega⟩)
      · have heq : (⟨target, ht⟩ : Fin 8) =
            ⟨(target - 6) + 6, by omega⟩ := Fin.ext (by simp; omega)
        rw [heq] at hm
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C))
            (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
            (L.a_r ⟨target - 6, by omega⟩)
    simp [hA1]
    simpa using hn

theorem outCount_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (source : Nat) (hs : source < 8) :
    (outCount (graphArc G L) source).toNat =
      Shared.directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [outCount, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  simp [graphArc, hs, j.isLt]

theorem minimumThree_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hPivot : IsMinimalPivot G C) (hk : C.k = 3) :
    minimumThree (graphArc G L) = true := by
  rw [minimumThree, all_eq_true_iff]
  intro source hs
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [outCount_toNat G C L source hs]
  simpa [Shared.directCount, CertificateBridge.internalFirstNeighbors, hk]
    using (hPivot (L.a ⟨source, hs⟩).1 (L.a _).2).1

theorem rUnreached_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    HighCore.rUnreached (graphArc G L) = true := by
  rw [HighCore.rUnreached, all_eq_true_iff]
  intro a ha
  rw [all_eq_true_iff]
  intro r hr
  simp only [graphArc, dif_pos (by omega : 1 + a < 8),
    dif_pos (by omega : 6 + r < 8)]
  have hn := BSixKThreeCoreGraphBridge.A1_not_adj_R G C hG
    (L.a ⟨a + 1, by omega⟩).1 (L.a ⟨r + 6, by omega⟩).1
    (L.a_aOne ⟨a, ha⟩) (L.a_r ⟨r, hr⟩)
  have hs : (L.a ⟨1 + a, by omega⟩).1 = (L.a ⟨a + 1, by omega⟩).1 := by
    congr 2
    apply Fin.ext
    change 1 + a = a + 1
    omega
  have ht : (L.a ⟨6 + r, by omega⟩).1 = (L.a ⟨r + 6, by omega⟩).1 := by
    congr 2
    apply Fin.ext
    change 6 + r = r + 6
    omega
  simp [hs, ht, hn]

theorem second_true_iff {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 8) (ht : target < 8) :
    second (graphArc G L) source target = true ↔
      (L.a ⟨target, ht⟩).1 ∈
        CertificateBridge.internalSecondNeighbors (G := G) C.A
          (L.a ⟨source, hs⟩).1 := by
  unfold second reaches graphArc
  simp only [dif_pos hs, dif_pos ht, Bool.and_eq_true, decide_eq_true_eq,
    CertificateBridge.internalSecondNeighbors, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hne, hNot⟩, hReach⟩
    obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 8 _).mp hReach
    simp only [Bool.and_eq_true, decide_eq_true_eq,
      dif_pos hm] at hPath
    rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
    refine ⟨(L.a ⟨target, ht⟩).2, by simpa using hNot, ?_,
      (L.a ⟨middle, hm⟩).1, (L.a _).2,
      hFirst, hLast⟩
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
    refine ⟨⟨hst, by simp [hNot]⟩, (any_eq_true_iff 8 _).mpr
      ⟨mi, mi.isLt, ?_⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq,
      dif_pos mi.isLt]
    refine ⟨⟨⟨hms, hmt⟩, by simpa [hmVal] using hFirst⟩,
      by simpa [hmVal] using hLast⟩

theorem secondCount_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (source : Nat) (hs : source < 8) :
    (secondCount (graphArc G L) source).toNat =
      (CertificateBridge.internalSecondNeighbors (G := G) C.A
        (L.a ⟨source, hs⟩).1).card := by
  rw [secondCount, toNat_count_eq_fin_sum 8 _ (by omega)]
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
  have hiff := second_true_iff G C L hG source j hs j.isLt
  by_cases hb : second (graphArc G L) source j = true
  · have hp : (L.a j).1 ∈ T := hiff.mp hb
    simp [hb, hp]
  · have hp : ¬((L.a j).1 ∈ T) := fun h ↦ hb (hiff.mpr h)
    simp [hb, hp]

theorem external_subset_second {zCount : Nat} (C : G.LocalConfiguration)
    (_L : Labels G zCount C) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hBCard : C.B.card = 7)
    (hk : C.k = 3) (hr : C.r = 7) (hx : C.x = 2)
    (u : V) (hu : u ∈ C.A1) :
    externalTargets G C ⊆ G.secondOutNeighborFinset u := by
  intro v hv
  have hNot := XThreeNoRoot.GraphFacts.A_not_adj_external G C hG u v
    (Digraph.LocalConfiguration.A1_subset_A (G := G) C hu) hv
  have hne : v ≠ u := by
    intro heq
    subst v
    exact XThreeNoRoot.GraphFacts.external_not_mem_A G C hG u hv
      (Digraph.LocalConfiguration.A1_subset_A (G := G) C hu)
  have hReach : ∃ p ∈ C.P, G.Adj p v := by
    rcases Finset.mem_union.mp hv with hvZ | hvRoot
    · exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_sdiff.mp hvZ).1
    · by_cases h : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : v = C.s := by simpa [rootSecondFinset, h] using hvRoot
        simpa [hvs] using h
      · simp [rootSecondFinset, h] at hvRoot
  obtain ⟨p, hp, hpv⟩ := hReach
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨p, A1_adj_P G C hG hPivot hBCard hk hr hx u p hu hp, hpv⟩,
    hNot, hne⟩

theorem highCore_true {zCount : Nat} (hzSix : 6 ≤ zCount)
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 7)
    (hx : C.x = 2) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    highCore (graphArc G L) = true := by
  have hOr := oriented_true G C L hG
  have hFixed := fixedPivotRow_true G C L hG
  have hMin := minimumThree_true G C L hPivot hk
  have hR := rUnreached_true G C L hG
  have hSecond : all 3 (fun a ↦
      (secondCount (graphArc G L) (1 + a) + 6).ult 10) = true := by
    rw [all_eq_true_iff]
    intro a ha
    let u := (L.a ⟨a + 1, by omega⟩).1
    let T := CertificateBridge.internalSecondNeighbors (G := G) C.A u
    have hu : u ∈ C.A1 := L.a_aOne ⟨a, ha⟩
    have hExtSub := external_subset_second G C L hG hPivot hBCard hk hr hx u hu
    have hTSub : T ⊆ G.secondOutNeighborFinset u := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨_, hNot, hne, w, _, huw, hwv⟩
      rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨w, huw, hwv⟩, hNot, hne⟩
    have hDisj : Disjoint T (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvT hvZ
      exact XThreeNoRoot.GraphFacts.external_not_mem_A G C hG v hvZ
        (Finset.mem_filter.mp hvT).1
    have hUnion : T ∪ externalTargets G C ⊆ G.secondOutNeighborFinset u :=
      Finset.union_subset hTSub hExtSub
    have hCardLe := Finset.card_le_card hUnion
    rw [Finset.card_union_of_disjoint hDisj] at hCardLe
    have hzCard : (externalTargets G C).card = zCount := by
      simpa using (Fintype.card_congr L.z).symm
    have hOut : G.outdegree u = 10 := by
      rw [XTwoNoRoot.GraphFacts.A_outdegree_eq_A_add_P G C hG hPB u
        (Digraph.LocalConfiguration.A1_subset_A (G := G) C hu),
        A1_internalDegree_eq_three G C hG hPivot hk hx u hu]
      have hPDirect : Shared.directCount G C.P u = 7 := by
        change (C.P.filter (G.Adj u)).card = 7
        have hFilter : C.P.filter (G.Adj u) = C.P := by
          apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
          apply Finset.card_le_card
          intro p hp
          exact Finset.mem_filter.mpr
            ⟨hp, A1_adj_P G C hG hPivot hBCard hk hr hx u p hu hp⟩
        rw [hFilter]
        simpa using (Fintype.card_congr L.p).symm
      rw [hPDirect]
    have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨u, h⟩)
    have hNat : T.card + 6 < 10 := by
      rw [hOut] at hStrict
      unfold Digraph.secondOutdegree at hStrict
      omega
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [BitVec.toNat_add, secondCount_toNat G C L hG (1 + a) (by omega)]
    have huEq : (L.a ⟨1 + a, by omega⟩).1 = u := by
      dsimp [u]
      congr 2
      apply Fin.ext
      change 1 + a = a + 1
      omega
    rw [huEq]
    change (T.card + 6) % 256 < 10
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hNat
  simp only [highCore, hOr, hFixed, hMin, hR, hSecond, Bool.and_self]

theorem contradiction {zCount : Nat} (hzSix : 6 ≤ zCount)
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 7)
    (hx : C.x = 2) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) : False := by
  have hCore := highCore_true G hzSix C L hG hPivot hBCard hk hr hx hPB hNoSeymour
  have hUnsat := high_unsat (graphArc G L)
  simp [hCore] at hUnsat

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.HighBridge
