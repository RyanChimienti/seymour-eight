import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.UnreachedHand
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.GraphBridge

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoRoot.Hand

open Shared CertificateBridge
open RSix.XTwoNoRoot.HandScratch

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem p_to_H_three_le (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hr : C.r = 6) (hy : BSevenKTwo.y G C = 0)
    (hECard : (externalTargets G C).card = 5) :
    3 ≤ edgeCount G C.P C.H := by
  have hPCard : C.P.card = 6 := hr
  have hLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hPQ : edgeCount G C.P C.Q = 0 := by
    unfold edgeCount directCount internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q hq hpq
    exact no_arc_to_q_of_y_zero G C q p hq hy
      (Finset.mem_union_right C.A1 hp) hpq
  have hPP := internal_edgeCount_le_choose_two G C.P hG
  have hPE := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard] at hPP hPE
  rw [hECard] at hPE
  norm_num [Nat.choose] at hPP
  rw [hPQ] at hAccounting
  omega

theorem false_of_unreached_five_by_distinguished
    (C : G.LocalConfiguration) (q u : V)
    (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hx : C.x = 2) (hECard : (externalTargets G C).card = 5)
    (huA1 : u ∈ C.A1) (huDegree : G.outdegree u = 8)
    (huX : ∀ x ∈ C.X, G.Adj u x)
    (huP : ∀ p ∈ C.P, G.Adj u p)
    (hNoW : ∀ w ∈
      (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q}), ¬G.Adj u w)
    (hEdge : 5 ≤ edgeCount G C.X
      (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q})) : False := by
  let T := BSixKTwoCoreGraphBridge.protectedTargets G C
  let W := T ∪ {q}
  let U := W ∩ G.outNeighborFinsetOf C.X
  have hXCard : C.X.card = 2 := hx
  have hMono : edgeCount G C.X W ≤ edgeCount G C.X U := by
    apply BSixKThree.edgeCount_mono_right G
    intro x hxmem w hwW hxw
    exact Finset.mem_inter.mpr ⟨hwW,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr ⟨x, hxmem, hxw⟩⟩
  have hCap := edgeCount_le_card_mul_card G C.X U
  rw [hXCard] at hCap
  have hUCard : 3 ≤ U.card := by
    change 5 ≤ edgeCount G C.X W at hEdge
    omega
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have huH : u ∈ C.H := Finset.mem_union_left C.X huA1
  have hTsubA : T ⊆ C.A := by
    intro w hwT
    have hUnion := BSixKTwoCoreGraphBridge.H_union_protectedTargets_eq_A G C
    rw [← hUnion]
    exact Finset.mem_union_right C.H hwT
  have hExternalSecond : externalTargets G C ⊆
      G.secondOutNeighborFinset u := by
    intro z hzmem
    rcases Finset.mem_union.mp hzmem with hz | hroot
    · have hzReach := (Finset.mem_sdiff.mp hz).1
      obtain ⟨p, hpP, hpz⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp hzReach
      have huz : ¬G.Adj u z :=
        RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
          G C hG u z huA hz
      have hzu : z ≠ u := by
        intro hEq
        subst z
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
            (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} huA))
      rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨p, huP p hpP, hpz⟩, huz, hzu⟩
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hReach' := hReach
        obtain ⟨p, hpP, hps⟩ := hReach
        have hzEq : z = C.s := by
          simpa [rootSecondFinset, hReach'] using hroot
        subst z
        have hus : ¬G.Adj u C.s := hG.2
          (Finset.mem_filter.mp
            (Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1)).2
        have hsu : C.s ≠ u := by
          exact fun h => Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
            (h ▸ huA)
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨p, huP p hpP, hps⟩, hus, hsu⟩
      · simp [rootSecondFinset, hReach] at hroot
  have hUSecond : U ⊆ G.secondOutNeighborFinset u := by
    intro w hwU
    rcases Finset.mem_inter.mp hwU with ⟨hwW, hwReach⟩
    obtain ⟨x, hxmem, hxw⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
    have huw : ¬G.Adj u w := hNoW w hwW
    have hwu : w ≠ u := by
      intro hEq
      subst w
      rcases Finset.mem_union.mp hwW with huT | huq
      · exact (Finset.disjoint_left.mp
          (BSixKTwoCoreGraphBridge.disjoint_H_protectedTargets G C hG)) huH huT
      · have huq' : u = q := Finset.mem_singleton.mp huq
        subst q
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) huA
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨x, huX x hxmem, hxw⟩, huw, hwu⟩
  have hDisEU : Disjoint (externalTargets G C) U := by
    rw [Finset.disjoint_left]
    intro w hwE hwU
    have hwW := (Finset.mem_inter.mp hwU).1
    rcases Finset.mem_union.mp hwW with hwT | hwq
    · rcases Finset.mem_union.mp hwE with hwZ | hwRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
            (Finset.mem_union_left C.B
              (Finset.mem_union_right {C.s} (hTsubA hwT)))
      · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
        · have hwEq : w = C.s := by
            simpa [rootSecondFinset, hReach] using hwRoot
          subst w
          exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
            (hTsubA hwT)
        · simp [rootSecondFinset, hReach] at hwRoot
    · have hw : w = q := Finset.mem_singleton.mp hwq
      subst w
      exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ) hwE
  have hUnionSecond : externalTargets G C ∪ U ⊆
      G.secondOutNeighborFinset u :=
    Finset.union_subset hExternalSecond hUSecond
  have hEight : 8 ≤ G.secondOutdegree u := by
    unfold Digraph.secondOutdegree
    have hCard := Finset.card_le_card hUnionSecond
    rw [Finset.card_union_of_disjoint hDisEU, hECard] at hCard
    omega
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hu ↦ hNoSeymour ⟨u, hu⟩)
  omega

theorem unreached_false_of_distinguished (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ w, 8 ≤ G.outdegree w)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 2) (hr : C.r = 6) (hx : C.x = 2)
    (hy : BSevenKTwo.y G C = 0)
    (hECard : (externalTargets G C).card = 5)
    (hDist : ∃ u ∈ C.A1, directCount G C.A u = 2 ∧
      directCount G C.A1 u = 0 ∧ ∀ x ∈ C.X, G.Adj u x) : False := by
  obtain ⟨u, huA1, huA, _huA1Zero, huX⟩ := hDist
  obtain ⟨v, hvA1, huv, hA1, huDegree, huP, hNoW⟩ :=
    distinguished_unreached_package G C q u hqQ hQ hG hPivot hk hr hy huA1 huA
  have hPH := p_to_H_three_le G C hG hMin hr hy hECard
  have hXW := x_to_protected_q_lower G C q u v hqQ hQ hG hMin hr hx hy
    huA1 hvA1 huv hA1 huX huP
  have hFive : 5 ≤ edgeCount G C.X
      (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q}) := by omega
  exact false_of_unreached_five_by_distinguished G C q u hqQ hG hNoSeymour
    hx hECard huA1 huDegree huX huP hNoW hFive

end SeymourEight.BSevenKTwo.RSix.XTwoRoot.Hand
