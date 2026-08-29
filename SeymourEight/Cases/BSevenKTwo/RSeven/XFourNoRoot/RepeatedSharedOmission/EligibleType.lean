import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.TargetedDeletion

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# The eligible-X type bound

For an exact `X` vertex dominating `a1` and `R`, four disjoint classes of
strict second neighbours give the scalar restriction used by the finite core.
The argument is purely graph-theoretic.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared RepeatedSharedOmissionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def xLabelEquiv (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hXCard : C.X.card = 4) :
    Fin 4 ≃ {v : V // v ∈ C.X} := by
  let f : Fin 4 → {v : V // v ∈ C.X} := fun i =>
    ⟨(L.a ⟨i.1 + 3, by omega⟩).1, L.a_x i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.1 + 3, by omega⟩ : Fin 8) = ⟨j.1 + 3, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := Fin.ext_iff.mp ha
    change i.1 + 3 = j.1 + 3 at hval
    omega
  · simpa using hXCard.symm

@[simp] theorem xLabelEquiv_val (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hXCard : C.X.card = 4)
    (i : Fin 4) :
    (xLabelEquiv G C L hXCard i).1 = (L.a ⟨i.1 + 3, by omega⟩).1 := by
  rfl

noncomputable def aOneLabelEquiv (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hk : C.k = 2) :
    Fin 2 ≃ {v : V // v ∈ C.A1} := by
  let f : Fin 2 → {v : V // v ∈ C.A1} := fun i =>
    ⟨(L.a ⟨i.1 + 1, by omega⟩).1, L.a_aOne i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.1 + 1, by omega⟩ : Fin 8) = ⟨j.1 + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval := Fin.ext_iff.mp ha
    change i.1 + 1 = j.1 + 1 at hval
    omega
  · change C.A1.card = 2 at hk
    simpa using hk.symm

@[simp] theorem aOneLabelEquiv_val (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hk : C.k = 2) (i : Fin 2) :
    (aOneLabelEquiv G C L hk i).1 = (L.a ⟨i.1 + 1, by omega⟩).1 := by
  rfl

def reachesWithinH (C : G.LocalConfiguration) (source target : V) : Prop :=
  G.Adj source target ∨ ∃ middle ∈ C.H,
    middle ≠ source ∧ middle ≠ target ∧
      G.Adj source middle ∧ G.Adj middle target

theorem xReach_coreBits_iff (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (_T : TightCounts G C L)
    (_hG : G.IsOriented) (hHCard : C.H.card = 6)
    (x target : Nat) (hx : x < 4) (ht : target < 4) :
    ThetaFourCore.xReach
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) x target = true ↔
      reachesWithinH G C (L.a ⟨3 + x, by omega⟩).1
        (L.a ⟨3 + target, by omega⟩).1 := by
  unfold ThetaFourCore.xReach reachesWithinH
  rw [Bool.or_eq_true, aArc_coreBits G.Adj _ _ _ (3 + x) (3 + target)
    (by omega) (by omega), any_eq_true_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hDirect | ⟨middle, hm, ⟨⟨⟨hneS, hneT⟩, hFirst⟩, hLast⟩⟩)
    · exact Or.inl hDirect
    · right
      refine ⟨(L.a ⟨1 + middle, by omega⟩).1, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm] using
          (hLabelEquiv G C L hHCard ⟨middle, hm⟩).2
      · intro heq
        apply hneS
        have hi := L.a.injective (Subtype.ext heq)
        exact congrArg Fin.val hi
      · intro heq
        apply hneT
        have hi := L.a.injective (Subtype.ext heq)
        exact congrArg Fin.val hi
      · rw [aArc_coreBits G.Adj _ _ _ (3 + x) (1 + middle)
          (by omega) (by omega)] at hFirst
        exact of_decide_eq_true hFirst
      · rw [aArc_coreBits G.Adj _ _ _ (1 + middle) (3 + target)
          (by omega) (by omega)] at hLast
        exact of_decide_eq_true hLast
  · rintro (hDirect | ⟨middle, hmH, hneS, hneT, hFirst, hLast⟩)
    · exact Or.inl hDirect
    · obtain ⟨i, hi⟩ := (hLabelEquiv G C L hHCard).surjective ⟨middle, hmH⟩
      right
      refine ⟨i, i.isLt, ?_⟩
      have hmid : (L.a ⟨1 + i.1, by omega⟩).1 = middle := by
        simpa [Nat.add_comm] using congrArg Subtype.val hi
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro heq
        apply hneS
        rw [← hmid]
        have hfin : (⟨1 + i.1, by omega⟩ : Fin 8) = ⟨3 + x, by omega⟩ :=
          Fin.ext heq
        rw [hfin]
      · intro heq
        apply hneT
        rw [← hmid]
        have hfin : (⟨1 + i.1, by omega⟩ : Fin 8) =
            ⟨3 + target, by omega⟩ := Fin.ext heq
        rw [hfin]
      · rw [aArc_coreBits G.Adj _ _ _ (3 + x) (1 + i.1)
          (by omega) (by omega)]
        simpa [hmid] using decide_eq_true hFirst
      · rw [aArc_coreBits G.Adj _ _ _ (1 + i.1) (3 + target)
          (by omega) (by omega)]
        simpa [hmid] using decide_eq_true hLast

theorem eligibleType_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (hXCard : C.X.card = 4) (hHCard : C.H.card = 6) (hk : C.k = 2)
    (x : Nat) (hx : x < 4)
    (hEligible : ThetaFourCore.xEligible
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) x = true) :
    ThetaFourCore.eligibleType
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) x = true := by
  classical
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  let source := (L.a ⟨3 + x, by omega⟩).1
  let pMiss := C.P.filter fun p => ¬G.Adj source p
  let aMiss := C.A1.filter fun a => ¬G.Adj source a
  let xReached := C.X.filter fun y =>
    y ≠ source ∧ reachesWithinH G C source y
  let xStrict := xReached.filter fun y => ¬G.Adj source y
  let zReached := C.Z.filter fun z =>
    ∃ p ∈ C.P, G.Adj source p ∧ G.Adj p z
  let b := directCount G C.P source
  let dA := directCount G C.A1 source
  let dX := directCount G C.X source
  let r := xReached.card
  have hFacts := xEligible_graph_facts G C L T hG hRoot x hx hEligible
  have hSourceX : source ∈ C.X := by
    simpa [source, Nat.add_comm] using L.a_x ⟨x, hx⟩
  have hSourceA : source ∈ C.A :=
    Digraph.LocalConfiguration.X_subset_A (G := G) C hSourceX
  have hbBits : (ThetaFourCore.aPOut bits (3 + x)).toNat = b := by
    exact aPOut_toNat G C L T hG (3 + x) (by omega)
  have hrBits : (ThetaFourCore.count 4 (fun target =>
      decide (target ≠ x) && ThetaFourCore.xReach bits x target)).toNat = r := by
    rw [toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    rw [show r = xReached.card by rfl,
      filterCard_eq_sum_fin C.X (xLabelEquiv G C L hXCard)
        (fun y => y ≠ source ∧ reachesWithinH G C source y)]
    apply Finset.sum_congr rfl
    intro target htMem
    rw [xLabelEquiv_val]
    have hne : (L.a ⟨target.1 + 3, by omega⟩).1 ≠ source ↔
        target.1 ≠ x := by
      constructor
      · intro hn heq
        apply hn
        simp [source, heq, Nat.add_comm]
      · intro hn heq
        apply hn
        have hi := L.a.injective (Subtype.ext heq)
        have hv := Fin.ext_iff.mp hi
        change target.1 + 3 = 3 + x at hv
        omega
    have hReachIff : ThetaFourCore.xReach bits x target = true ↔
        reachesWithinH G C source (L.a ⟨target.1 + 3, by omega⟩).1 := by
      simpa [bits, source, Nat.add_comm] using
        xReach_coreBits_iff G C L T hG hHCard x target hx target.isLt
    simp [Bool.and_eq_true, hne, hReachIff]
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hACard : C.A1.card = 2 := by
    change C.A1.card = 2 at hk
    exact hk
  have hpSplit : pMiss.card + b = 7 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := C.P) (p := fun p => G.Adj source p)
    simpa [pMiss, b, directCount, CertificateBridge.internalFirstNeighbors,
      Nat.add_comm, hPCard] using h
  have haSplit : aMiss.card + dA = 2 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := C.A1) (p := fun a => G.Adj source a)
    simpa [aMiss, dA, directCount, CertificateBridge.internalFirstNeighbors,
      Nat.add_comm, hACard] using h
  have hDirectXSubset : C.X.filter (G.Adj source) ⊆ xReached := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyX, hsy⟩
    change y ∈ C.X.filter fun y => y ≠ source ∧ reachesWithinH G C source y
    apply Finset.mem_filter.mpr
    refine ⟨hyX, ?_, Or.inl hsy⟩
    intro heq
    subst y
    exact hG.1 source hsy
  have hDirectXEq : xReached.filter (G.Adj source) = C.X.filter (G.Adj source) := by
    apply Finset.Subset.antisymm
    · intro y hy
      have hyReach : y ∈ C.X.filter fun y =>
          y ≠ source ∧ reachesWithinH G C source y := by
        exact (Finset.mem_filter.mp hy).1
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyReach).1,
        (Finset.mem_filter.mp hy).2⟩
    · intro y hy
      exact Finset.mem_filter.mpr ⟨hDirectXSubset hy, (Finset.mem_filter.mp hy).2⟩
  have hxSplit : xStrict.card + dX = r := by
    have h := Finset.card_filter_add_card_filter_not
      (s := xReached) (p := fun y => G.Adj source y)
    rw [hDirectXEq] at h
    simpa [xStrict, dX, r, directCount,
      CertificateBridge.internalFirstNeighbors, Nat.add_comm] using h
  have hRCard : C.R.card = 1 := by
    have h := Digraph.LocalConfiguration.k_add_x_add_card_R_eq_seven
      (G := G) C hG.1 (by simpa using (Fintype.card_congr L.a).symm)
    change C.x = 4 at hXCard
    omega
  have hREq : C.R = {(L.a 7).1} := by
    obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hRCard
    have heq : (L.a 7).1 = r0 := by simpa [hr0] using L.a_r
    simp [hr0, heq]
  have hDirectA : directCount G C.A source = 2 + dA + dX := by
    have hHa1 : Disjoint C.H {C.a1} := by
      rw [Finset.disjoint_left]
      intro v hvH hv
      have hvEq := Finset.mem_singleton.mp hv
      subst v
      rcases Finset.mem_union.mp hvH with hvA1 | hvX
      · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
      · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
    have hPartsR := Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C,
      directCount_union_of_disjoint G (C.A1 ∪ C.X ∪ {C.a1}) C.R source hPartsR,
      directCount_union_of_disjoint G (C.A1 ∪ C.X) {C.a1} source hHa1,
      directCount_union_of_disjoint G C.A1 C.X source
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C),
      hREq, directCount_singleton, directCount_singleton]
    have ha1Arc : G.Adj source C.a1 := by simpa [source] using hFacts.2.1
    have hrArc : G.Adj source (L.a 7).1 := by simpa [source] using hFacts.2.2
    simp [dA, dX, epsilonAt, ha1Arc, hrArc]
    omega
  have hDegreeSplit : b + dA + dX = 6 := by
    have hDegree := A_outdegree_eq_A_add_P G C hG T.p_eq_B source hSourceA
    rw [hFacts.1, hDirectA] at hDegree
    change 8 = 2 + dA + dX + b at hDegree
    omega
  have hSecondBound : pMiss.card + aMiss.card + xStrict.card + zReached.card ≤
      G.secondOutdegree source := by
    let U := pMiss ∪ aMiss ∪ xStrict ∪ zReached
    have hUSubset : U ⊆ G.secondOutNeighborFinset source := by
      intro v hv
      simp only [U, Finset.mem_union] at hv
      rcases hv with ((hvP | hvA) | hvX) | hvZ
      · rcases Finset.mem_filter.mp hvP with ⟨hvPMem, hn⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨C.a1, hFacts.2.1, (Finset.mem_filter.mp hvPMem).2⟩, hn,
          fun heq => (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hSourceA
              (Digraph.LocalConfiguration.P_subset_B (G := G) C
                (heq ▸ hvPMem))⟩
      · rcases Finset.mem_filter.mp hvA with ⟨hvAMem, hn⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨C.a1, hFacts.2.1, (Finset.mem_filter.mp hvAMem).2⟩, hn,
          fun heq => (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
              (heq ▸ hvAMem) hSourceX⟩
      · rcases Finset.mem_filter.mp hvX with ⟨hvReach, hn⟩
        rcases (Finset.mem_filter.mp hvReach).2 with ⟨hne, hReach⟩
        rcases hReach with hDirect | ⟨middle, hmH, _, _, hsm, hmv⟩
        · exact (hn hDirect).elim
        · rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
          exact ⟨⟨middle, hsm, hmv⟩, hn, hne⟩
      · rcases Finset.mem_filter.mp hvZ with ⟨hvZ, p, hp, hsp, hpv⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨p, hsp, hpv⟩, A_not_adj_Z G C hG source v hSourceA hvZ,
          fun heq => (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
              (heq ▸ Finset.mem_union_right C.A1 hSourceX)⟩
    have hPA : Disjoint pMiss aMiss := by
      exact (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm.mono
        (Finset.filter_subset _ _) ((Finset.filter_subset _ _).trans
          (Finset.subset_union_left))
    have hPAX : Disjoint (pMiss ∪ aMiss) xStrict := by
      rw [Finset.disjoint_left]
      intro v hvPA hvX
      have hvXC : v ∈ C.X :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hvX).1).1
      rcases Finset.mem_union.mp hvPA with hvP | hvA
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
            (Finset.mem_union_right C.A1 hvXC) (Finset.mem_filter.mp hvP).1
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
            (Finset.mem_filter.mp hvA).1 hvXC
    have hAllZ : Disjoint (pMiss ∪ aMiss ∪ xStrict) zReached := by
      rw [Finset.disjoint_left]
      intro v hvLeft hvZ
      have hvZC := (Finset.mem_filter.mp hvZ).1
      rcases Finset.mem_union.mp hvLeft with hvPA | hvX
      · rcases Finset.mem_union.mp hvPA with hvP | hvA
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZC
              (Finset.mem_filter.mp hvP).1
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZC
              (Finset.mem_union_left C.X (Finset.mem_filter.mp hvA).1)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZC
            (Finset.mem_union_right C.A1
              (Finset.mem_filter.mp (Finset.mem_filter.mp hvX).1).1)
    have hUCard : U.card = pMiss.card + aMiss.card + xStrict.card + zReached.card := by
      simp only [U]
      rw [Finset.card_union_of_disjoint hAllZ,
        Finset.card_union_of_disjoint hPAX,
        Finset.card_union_of_disjoint hPA]
    rw [← hUCard]
    exact (Finset.card_le_card hUSubset)
  have hSecondLe : G.secondOutdegree source ≤ 7 :=
    Digraph.secondOutdegree_le_seven G hFacts.1 hNoSeymour
  have hReachBound : 3 + r + zReached.card ≤ 7 := by
    have hIdentity : pMiss.card + aMiss.card + xStrict.card = 3 + r := by
      omega
    omega
  have hzTwo (hb3 : 3 ≤ b) : 2 ≤ zReached.card := by
    have hSNonempty : (C.P.filter (G.Adj source)).Nonempty := by
      rw [← Finset.card_pos, show (C.P.filter (G.Adj source)).card = b by rfl]
      omega
    obtain ⟨p, hpS⟩ := hSNonempty
    rcases Finset.mem_filter.mp hpS with ⟨hpP, hsp⟩
    have hSubset : C.Z.filter (G.Adj p) ⊆ zReached := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
        ⟨p, hpP, hsp, (Finset.mem_filter.mp hz).2⟩⟩
    have hpIndex := L.p.surjective ⟨p, hpP⟩
    obtain ⟨i, hi⟩ := hpIndex
    have hCount := L.p_z_count i
    have hEq : directCount G C.Z p = profileDirectCount i := by
      simpa [congrArg Subtype.val hi] using hCount
    have hAtLeast : 2 ≤ directCount G C.Z p := by
      rw [hEq]
      unfold profileDirectCount
      by_cases hi0 : i.1 = 0
      · simp [hi0]
      · simp [hi0]
        split <;> omega
    exact hAtLeast.trans (Finset.card_le_card hSubset)
  have hzThree (hb4 : 4 ≤ b) : 3 ≤ zReached.card := by
    have hMany : 2 ≤ (C.P.filter (G.Adj source)).card := by
      change 2 ≤ b
      omega
    have hExists : ∃ p ∈ C.P.filter (G.Adj source), p ≠ (L.p 0).1 := by
      by_contra hn
      push Not at hn
      have hSub : C.P.filter (G.Adj source) ⊆ {(L.p 0).1} := by
        intro p hp
        simp [hn p hp]
      have := Finset.card_le_card hSub
      simp at this
      omega
    obtain ⟨p, hpS, hpNe⟩ := hExists
    rcases Finset.mem_filter.mp hpS with ⟨hpP, hsp⟩
    obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hpP⟩
    have hi0 : i ≠ 0 := by
      intro heq
      apply hpNe
      simpa [heq] using (congrArg Subtype.val hi).symm
    have hCount : 3 ≤ directCount G C.Z p := by
      have hc := L.p_z_count i
      rw [show (L.p i).1 = p by simpa using congrArg Subtype.val hi] at hc
      rw [hc]
      simp [profileDirectCount, hi0]
      split <;> omega
    have hSubset : C.Z.filter (G.Adj p) ⊆ zReached := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
        ⟨p, hpP, hsp, (Finset.mem_filter.mp hz).2⟩⟩
    exact hCount.trans (Finset.card_le_card hSubset)
  have hScalarTwo (hb3 : 3 ≤ b) : r ≤ 2 := by
    have hz := hzTwo hb3
    omega
  have hScalarOne (hb4 : 4 ≤ b) : r ≤ 1 := by
    have hz := hzThree hb4
    omega
  have hbLe : b ≤ 7 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hbPos : 1 ≤ b := by
    have := hDegreeSplit
    have hdALe : dA ≤ 2 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hACard
    have hdXLe : dX ≤ 3 := by
      have hSub : C.X.filter (G.Adj source) ⊆ C.X.erase source := by
        intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyX, hsy⟩
        exact Finset.mem_erase.mpr ⟨fun heq => hG.1 source (heq ▸ hsy), hyX⟩
      have hc := Finset.card_le_card hSub
      rw [Finset.card_erase_of_mem hSourceX, hXCard] at hc
      exact hc
    omega
  have hbEq : (ThetaFourCore.aPOut bits (3 + x)).toNat = b := hbBits
  have hrEq : (ThetaFourCore.count 4 (fun target =>
      decide (target ≠ x) && ThetaFourCore.xReach bits x target)).toNat = r := hrBits
  have hrLeThree : r ≤ 3 := by
    have hSub : xReached ⊆ C.X.erase source := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyX, hyNe, _⟩
      exact Finset.mem_erase.mpr ⟨hyNe, hyX⟩
    have hCard := Finset.card_le_card hSub
    rw [Finset.card_erase_of_mem hSourceX, hXCard] at hCard
    exact hCard
  have hCountForm :
      ThetaFourCore.count 4 (fun target =>
        !decide (target = x) && ThetaFourCore.xReach bits x target) =
      ThetaFourCore.count 4 (fun target =>
        decide (target ≠ x) && ThetaFourCore.xReach bits x target) := by
    congr 1
    funext target
    simp
  change ThetaFourCore.eligibleType bits x = true
  unfold ThetaFourCore.eligibleType
  by_cases hb1 : b = 1
  · have hBVec : ThetaFourCore.aPOut bits (3 + x) = 1 := by
      apply BitVec.eq_of_toNat_eq
      simpa [hb1] using hbEq
    simp [hBVec]
  by_cases hb2 : b = 2
  · have hBVec : ThetaFourCore.aPOut bits (3 + x) = 2 := by
      apply BitVec.eq_of_toNat_eq
      simpa [hb2] using hbEq
    have hrLe : (ThetaFourCore.count 4 (fun target =>
        decide (target ≠ x) && ThetaFourCore.xReach bits x target)).toNat ≤ 3 := by
      rw [hrEq]
      exact hrLeThree
    simp [hBVec, hCountForm, BitVec.ule_eq_decide, hrLe]
  by_cases hb3 : b = 3
  · have hBVec : ThetaFourCore.aPOut bits (3 + x) = 3 := by
      apply BitVec.eq_of_toNat_eq
      simpa [hb3] using hbEq
    have hrLe : (ThetaFourCore.count 4 (fun target =>
        decide (target ≠ x) && ThetaFourCore.xReach bits x target)).toNat ≤ 2 := by
      rw [hrEq]
      exact hScalarTwo (by omega)
    simp [hBVec, hCountForm, BitVec.ule_eq_decide, hrLe]
  have hb4 : 4 ≤ b := by omega
  have hBGe : (4 : BitVec 8).ule (ThetaFourCore.aPOut bits (3 + x)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hbEq]
    exact hb4
  have hrLe : (ThetaFourCore.count 4 (fun target =>
      decide (target ≠ x) && ThetaFourCore.xReach bits x target)).ule 1 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hrEq]
    exact hScalarOne hb4
  have hrLeNot : (ThetaFourCore.count 4 (fun target =>
      !decide (target = x) && ThetaFourCore.xReach bits x target)).ule 1 = true := by
    rw [hCountForm]
    exact hrLe
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  right
  exact ⟨hBGe, hrLe⟩

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
