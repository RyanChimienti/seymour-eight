import SeymourEight.Cases.BSevenKTwo.RSix.XThreeNoRoot.Assembly
import SeymourEight.Cases.BSevenKTwo.Counting
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.HandScratch

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem no_arc_to_q_of_y_zero (C : G.LocalConfiguration) (q u : V)
    (hqQ : q ∈ C.Q) (hy : BSevenKTwo.y G C = 0)
    (hu : u ∈ C.A1 ∪ C.P) : ¬G.Adj u q := by
  intro huq
  have hq : q ∈ BSevenKTwo.reachedQ G C := Finset.mem_inter.mpr ⟨hqQ,
    (Digraph.mem_outNeighborFinsetOf (G := G)).mpr ⟨u, hu, huq⟩⟩
  have hzero : (BSevenKTwo.reachedQ G C).card = 0 := by
    simpa [BSevenKTwo.y] using hy
  rw [Finset.card_eq_zero.mp hzero] at hq
  simp at hq

theorem p_to_H_three_le (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hr : C.r = 6) (hy : BSevenKTwo.y G C = 0)
    (hNoRoot : epsilonS G C = 0) (hz : C.z = 5) :
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
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hPP := internal_edgeCount_le_choose_two G C.P hG
  have hPZ := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard] at hPP hPZ
  change C.Z.card = 5 at hz
  rw [hz] at hPZ
  norm_num [Nat.choose] at hPP
  rw [hPQ, hExt] at hAccounting
  omega

theorem x_to_protected_q_lower (C : G.LocalConfiguration) (q u v : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ w, 8 ≤ G.outdegree w)
    (hr : C.r = 6) (hx : C.x = 2) (hy : BSevenKTwo.y G C = 0)
    (_huA1 : u ∈ C.A1) (hvA1 : v ∈ C.A1) (huv : u ≠ v)
    (hA1 : C.A1 = {u, v})
    (huX : ∀ x ∈ C.X, G.Adj u x)
    (huP : ∀ p ∈ C.P, G.Adj u p) :
    edgeCount G C.P C.H + 2 ≤
      edgeCount G C.X
        (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q}) := by
  let T := BSixKTwoCoreGraphBridge.protectedTargets G C
  have hPCard : C.P.card = 6 := hr
  have hXCard : C.X.card = 2 := hx
  have hDisA1X := Digraph.LocalConfiguration.disjoint_A1_X (G := G) C
  have hDisHT := BSixKTwoCoreGraphBridge.disjoint_H_protectedTargets G C hG
  have hNoVQ : ¬G.Adj v q := no_arc_to_q_of_y_zero G C q v hqQ hy
    (Finset.mem_union_left C.P hvA1)
  have hB : C.P ∪ {q} = C.B := by
    rw [← hQ]
    exact Digraph.LocalConfiguration.P_union_Q (G := G) C
  have hDisPq : Disjoint C.P {q} := by
    rw [Finset.disjoint_left]
    intro w hwP hwq
    have hw : w = q := Finset.mem_singleton.mp hwq
    subst w
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
  have hvqZero : directCount G {q} v = 0 := by
    simp [directCount_singleton, epsilonAt, hNoVQ]
  have hvDegree : 8 ≤ directCount G C.H v + directCount G C.P v := by
    have hAB := RSix.XThreeNoRoot.Assembly.A_outdegree_eq_A_add_B
      G C hG v (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA1)
    rw [← BSixKTwoCoreGraphBridge.H_union_protectedTargets_eq_A G C,
      directCount_union_of_disjoint G C.H T v hDisHT,
      BSixKTwoCoreGraphBridge.directCount_protected_eq_zero_of_mem_A1
        G C hG v hvA1,
      Nat.add_zero,
      ← hB, directCount_union_of_disjoint G C.P {q} v hDisPq,
      hvqZero, Nat.add_zero] at hAB
    rw [← hAB]
    exact hMin v
  have hHOut : directCount G C.H v =
      directCount G C.A1 v + directCount G C.X v := by
    rw [Digraph.LocalConfiguration.H,
      directCount_union_of_disjoint G C.A1 C.X v hDisA1X]
  have hA1Out : directCount G C.A1 v ≤ 1 := by
    rw [hA1]
    unfold directCount internalFirstNeighbors
    calc
      (({u, v} : Finset V).filter fun w ↦ G.Adj v w).card ≤
          ({u} : Finset V).card := by
        apply Finset.card_le_card
        intro w hw
        rcases Finset.mem_filter.mp hw with ⟨hwuv, hvw⟩
        have hwCases : w = u ∨ w = v := by simpa using hwuv
        rcases hwCases with hwu | hwv
        · simp [hwu]
        · have hvv : G.Adj v v := by simpa [hwv] using hvw
          exact (hG.1 v hvv).elim
      _ = 1 := by simp
  have hVLower : 7 ≤ directCount G C.X v + directCount G C.P v := by
    omega
  have hCrossPv := cross_edgeCount_add_reverse_le G C.P {v} hG
  have hPvSource : edgeCount G {v} C.P = directCount G C.P v := by
    simp [edgeCount]
  rw [hPCard, hPvSource] at hCrossPv
  simp only [Finset.card_singleton, Nat.mul_one] at hCrossPv
  have hCrossXv := cross_edgeCount_add_reverse_le G C.X {v} hG
  have hXvSource : edgeCount G {v} C.X = directCount G C.X v := by
    simp [edgeCount]
  rw [hXCard, hXvSource] at hCrossXv
  simp only [Finset.card_singleton, Nat.mul_one] at hCrossXv
  have hXX := internal_edgeCount_le_choose_two G C.X hG
  rw [hXCard] at hXX
  norm_num [Nat.choose] at hXX
  have hDefect : edgeCount G C.P {v} + edgeCount G C.X {v} +
      edgeCount G C.X C.X ≤ 2 := by
    omega
  have huPCount : directCount G C.P u = 6 := by
    unfold directCount internalFirstNeighbors
    rw [Finset.filter_eq_self.mpr huP, hPCard]
  have hPuCross := cross_edgeCount_add_reverse_le G C.P {u} hG
  have huPSource : edgeCount G {u} C.P = directCount G C.P u := by
    simp [edgeCount]
  rw [huPSource, huPCount, hPCard] at hPuCross
  simp only [Finset.card_singleton, Nat.mul_one] at hPuCross
  have hPuZero : edgeCount G C.P {u} = 0 := by omega
  have huXCount : directCount G C.X u = 2 := by
    unfold directCount internalFirstNeighbors
    rw [Finset.filter_eq_self.mpr huX, hXCard]
  have hXuCross := cross_edgeCount_add_reverse_le G C.X {u} hG
  have huXSource : edgeCount G {u} C.X = directCount G C.X u := by
    simp [edgeCount]
  rw [huXSource, huXCount, hXCard] at hXuCross
  simp only [Finset.card_singleton, Nat.mul_one] at hXuCross
  have hXuZero : edgeCount G C.X {u} = 0 := by omega
  have hDisUV : Disjoint ({u} : Finset V) {v} := by
    simp [huv]
  have hA1Union : ({u} : Finset V) ∪ {v} = C.A1 := by
    simp [hA1]
  have hPH : edgeCount G C.P C.H =
      edgeCount G C.P {v} + edgeCount G C.P C.X := by
    rw [Digraph.LocalConfiguration.H,
      edgeCount_union_of_disjoint G C.P C.A1 C.X hDisA1X,
      ← hA1Union,
      edgeCount_union_of_disjoint G C.P {u} {v} hDisUV,
      hPuZero]
    omega
  have hXH : edgeCount G C.X C.H =
      edgeCount G C.X {v} + edgeCount G C.X C.X := by
    rw [Digraph.LocalConfiguration.H,
      edgeCount_union_of_disjoint G C.X C.A1 C.X hDisA1X,
      ← hA1Union,
      edgeCount_union_of_disjoint G C.X {u} {v} hDisUV,
      hXuZero]
    omega
  have hCrossXP := cross_edgeCount_add_reverse_le G C.X C.P hG
  rw [hXCard, hPCard] at hCrossXP
  have hPointwise : ∀ x ∈ C.X, G.outdegree x =
      directCount G C.H x + directCount G T x +
        directCount G C.P x + directCount G {q} x := by
    intro x hxmem
    have hAB := RSix.XThreeNoRoot.Assembly.A_outdegree_eq_A_add_B
      G C hG x (Digraph.LocalConfiguration.X_subset_A (G := G) C hxmem)
    rw [← BSixKTwoCoreGraphBridge.H_union_protectedTargets_eq_A G C,
      directCount_union_of_disjoint G C.H T x hDisHT,
      ← hB, directCount_union_of_disjoint G C.P {q} x hDisPq] at hAB
    omega
  have hXDegree : 16 ≤ edgeCount G C.X C.H + edgeCount G C.X T +
      edgeCount G C.X C.P + edgeCount G C.X {q} := by
    have hLower : 16 ≤ ∑ x ∈ C.X, G.outdegree x := by
      calc
        16 = ∑ _x ∈ C.X, 8 := by simp [hXCard]
        _ ≤ ∑ x ∈ C.X, G.outdegree x := by
          apply Finset.sum_le_sum
          intro x hxmem
          exact hMin x
    rw [show (∑ x ∈ C.X, G.outdegree x) =
        edgeCount G C.X C.H + edgeCount G C.X T +
          edgeCount G C.X C.P + edgeCount G C.X {q} by
      calc
        (∑ x ∈ C.X, G.outdegree x) = ∑ x ∈ C.X,
            (directCount G C.H x + directCount G T x +
              directCount G C.P x + directCount G {q} x) := by
          apply Finset.sum_congr rfl
          exact hPointwise
        _ = _ := by
          unfold edgeCount
          simp only [Finset.sum_add_distrib]] at hLower
    exact hLower
  have hTq : Disjoint T {q} := by
    rw [Finset.disjoint_left]
    intro w hwT hwq
    have hw : w = q := Finset.mem_singleton.mp hwq
    subst w
    have hqB := Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ
    have hqA : q ∈ C.A := by
      have hUnion := BSixKTwoCoreGraphBridge.H_union_protectedTargets_eq_A G C
      rw [← hUnion]
      exact Finset.mem_union_right C.H hwT
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hqA hqB
  have hXTq := edgeCount_union_of_disjoint G C.X T {q} hTq
  change edgeCount G C.P C.H + 2 ≤ edgeCount G C.X (T ∪ {q})
  omega

theorem false_of_unreached_five_by_distinguished
    (C : G.LocalConfiguration) (q u : V)
    (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hx : C.x = 2) (hz : C.z = 5)
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
  have hZSecond : C.Z ⊆ G.secondOutNeighborFinset u := by
    intro z hzmem
    have hzReach := (Finset.mem_sdiff.mp hzmem).1
    obtain ⟨p, hpP, hpz⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hzReach
    have huz : ¬G.Adj u z :=
      RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
        G C hG u z huA hzmem
    have hzu : z ≠ u := by
      intro hEq
      subst z
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hzmem
          (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} huA))
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨p, huP p hpP, hpz⟩, huz, hzu⟩
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
          (BSixKTwoCoreGraphBridge.disjoint_H_protectedTargets G C hG))
            huH huT
      · have huq' : u = q := Finset.mem_singleton.mp huq
        subst q
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) huA
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨x, huX x hxmem, hxw⟩, huw, hwu⟩
  have hDisZU : Disjoint C.Z U := by
    rw [Finset.disjoint_left]
    intro w hwZ hwU
    have hwW := (Finset.mem_inter.mp hwU).1
    rcases Finset.mem_union.mp hwW with hwT | hwq
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
          (Finset.mem_union_left C.B
            (Finset.mem_union_right {C.s} (hTsubA hwT)))
    · have hw : w = q := Finset.mem_singleton.mp hwq
      subst w
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
          (Finset.mem_union_right ({C.s} ∪ C.A)
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
  have hUnionSecond : C.Z ∪ U ⊆ G.secondOutNeighborFinset u :=
    Finset.union_subset hZSecond hUSecond
  have hEight : 8 ≤ G.secondOutdegree u := by
    unfold Digraph.secondOutdegree
    have hCard := Finset.card_le_card hUnionSecond
    rw [Finset.card_union_of_disjoint hDisZU] at hCard
    change C.Z.card = 5 at hz
    omega
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hu ↦ hNoSeymour ⟨u, hu⟩)
  omega

theorem distinguished_unreached_package (C : G.LocalConfiguration)
    (q u : V) (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 2) (hr : C.r = 6) (hy : BSevenKTwo.y G C = 0)
    (huA1 : u ∈ C.A1) (huA : directCount G C.A u = 2) :
    ∃ v, v ∈ C.A1 ∧ u ≠ v ∧ C.A1 = {u, v} ∧
      G.outdegree u = 8 ∧ (∀ p ∈ C.P, G.Adj u p) ∧
      ∀ w ∈ (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q}),
        ¬G.Adj u w := by
  have hA1Card : C.A1.card = 2 := hk
  have hEraseCard : (C.A1.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huA1, hA1Card]
  obtain ⟨v, hErase⟩ := Finset.card_eq_one.mp hEraseCard
  have hvErase : v ∈ C.A1.erase u := by simp [hErase]
  have hvA1 : v ∈ C.A1 := (Finset.mem_erase.mp hvErase).2
  have huv : u ≠ v := by
    exact fun huv ↦ (Finset.mem_erase.mp hvErase).1 huv.symm
  have hA1 : C.A1 = {u, v} := by
    rw [← Finset.insert_erase huA1, hErase]
  have huA_mem : u ∈ C.A :=
    Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have huATie : (C.A.filter (G.Adj u)).card = C.k := by
    change directCount G C.A u = C.k
    omega
  have huBLower : 6 ≤ directCount G C.B u := by
    simpa [hr, directCount, internalFirstNeighbors] using
      (hPivot u huA_mem).2 huATie
  have hDisPq : Disjoint C.P {q} := by
    rw [Finset.disjoint_left]
    intro w hwP hwq
    have hw : w = q := Finset.mem_singleton.mp hwq
    subst w
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
  have hB : C.P ∪ {q} = C.B := by
    rw [← hQ]
    exact Digraph.LocalConfiguration.P_union_Q (G := G) C
  have huq : ¬G.Adj u q := no_arc_to_q_of_y_zero G C q u hqQ hy
    (Finset.mem_union_left C.P huA1)
  have huqZero : directCount G {q} u = 0 := by
    simp [directCount_singleton, epsilonAt, huq]
  have huPCount : directCount G C.P u = 6 := by
    rw [← hB, directCount_union_of_disjoint G C.P {q} u hDisPq,
      huqZero, Nat.add_zero] at huBLower
    have huPUpper : directCount G C.P u ≤ 6 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hr
    omega
  have huP : ∀ p ∈ C.P, G.Adj u p := by
    have hPCard : C.P.card = 6 := hr
    have hFilter : C.P.filter (G.Adj u) = C.P := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      change C.P.card ≤ directCount G C.P u
      rw [hPCard, huPCount]
    intro p hp
    exact (Finset.mem_filter.mp (hFilter.symm ▸ hp)).2
  have huDegree : G.outdegree u = 8 := by
    have hAB := RSix.XThreeNoRoot.Assembly.A_outdegree_eq_A_add_B
      G C hG u huA_mem
    have huB : directCount G C.B u = 6 := by
      rw [← hB, directCount_union_of_disjoint G C.P {q} u hDisPq,
        huqZero, huPCount]
    omega
  have hTZero :=
    BSixKTwoCoreGraphBridge.directCount_protected_eq_zero_of_mem_A1
      G C hG u huA1
  have hNoW : ∀ w ∈
      (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q}),
      ¬G.Adj u w := by
    intro w hwW huw
    rcases Finset.mem_union.mp hwW with hwT | hwq
    · have hwFilter : w ∈
          (BSixKTwoCoreGraphBridge.protectedTargets G C).filter (G.Adj u) :=
        Finset.mem_filter.mpr ⟨hwT, huw⟩
      have hpos : 0 < directCount G
          (BSixKTwoCoreGraphBridge.protectedTargets G C) u := by
        unfold directCount internalFirstNeighbors
        exact Finset.card_pos.mpr ⟨w, hwFilter⟩
      omega
    · have hw : w = q := Finset.mem_singleton.mp hwq
      subst w
      exact huq huw
  exact ⟨v, hvA1, huv, hA1, huDegree, huP, hNoW⟩

theorem unreached_five_false_of_distinguished (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ w, 8 ≤ G.outdegree w)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 2) (hr : C.r = 6) (hx : C.x = 2)
    (hy : BSevenKTwo.y G C = 0) (hNoRoot : epsilonS G C = 0)
    (hz : C.z = 5)
    (hDist : ∃ u ∈ C.A1, directCount G C.A u = 2 ∧
      directCount G C.A1 u = 0 ∧ ∀ x ∈ C.X, G.Adj u x) : False := by
  obtain ⟨u, huA1, huA, _huA1Zero, huX⟩ := hDist
  obtain ⟨v, hvA1, huv, hA1, huDegree, huP, hNoW⟩ :=
    distinguished_unreached_package G C q u hqQ hQ hG hPivot hk hr hy huA1 huA
  have hPH := p_to_H_three_le G C hG hMin hr hy hNoRoot hz
  have hXW := x_to_protected_q_lower G C q u v hqQ hQ hG hMin hr hx hy
    huA1 hvA1 huv hA1 huX huP
  have hFive : 5 ≤ edgeCount G C.X
      (BSixKTwoCoreGraphBridge.protectedTargets G C ∪ {q}) := by omega
  exact false_of_unreached_five_by_distinguished G C q u hqQ hG hNoSeymour
    hx hz huA1 huDegree huX huP hNoW hFive

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.HandScratch
