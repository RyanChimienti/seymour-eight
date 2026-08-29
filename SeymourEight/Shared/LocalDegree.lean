import SeymourEight.Shared.ArcCounting

set_option linter.style.header false

/-!
# Shared local-degree accounting

Degree decompositions and capacity inequalities for local configurations.
-/

namespace SeymourEight.Shared

open CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- When `P=B`, every outneighbor of a member of `P` is locally accounted for. -/
theorem outgoingCaptured_of_p_eq_B (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (p : V) (hp : p ∈ C.P) :
    G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
  intro v hvOut
  have hpv : G.Adj p v :=
    (Digraph.mem_outNeighborFinset (G := G)).mp hvOut
  simp only [Finset.mem_union, Finset.mem_singleton]
  by_cases hvs : v = C.s
  · exact Or.inl (Or.inl (Or.inr hvs))
  by_cases hvA : v ∈ C.A
  · by_cases hvA1 : v ∈ C.A1
    · exact Or.inl (Or.inr (Finset.mem_union_left C.X hvA1))
    · by_cases hva1 : v = C.a1
      · subst v
        have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hp).2
        exact (hG.2 ha1p hpv).elim
      · have hvX : v ∈ C.X := by
          apply Finset.mem_inter.mpr
          constructor
          · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
            exact ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩
          · apply Finset.mem_sdiff.mpr
            exact ⟨hvA, by simp [hvA1, hva1]⟩
        exact Or.inl (Or.inr (Finset.mem_union_right C.A1 hvX))
  · by_cases hvB : v ∈ C.B
    · have hvP : v ∈ C.P := by simpa [hPB] using hvB
      exact Or.inr hvP
    · have hvZ : v ∈ C.Z := by
        apply Finset.mem_sdiff.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          exact ⟨p, hp, hpv⟩
        · simp [hvs, hvA, hvB]
      exact Or.inl (Or.inl (Or.inl hvZ))

/-- Exact total-outdegree accounting whenever `P=B`. -/
theorem degreeSum_eq_local_edgeCounts_of_p_eq_B (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) :
    ∑ p ∈ C.P, G.outdegree p =
      edgeCount G C.P C.Z + (∑ p ∈ C.P, epsilonAt G p C.s) +
        edgeCount G C.P C.H + edgeCount G C.P C.P := by
  have hPointwise : ∀ p ∈ C.P,
      G.outdegree p = directCount G (C.Z ∪ {C.s} ∪ C.H ∪ C.P) p := by
    intro p hp
    unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
    apply congrArg Finset.card
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hpv
      have hvCaptured := outgoingCaptured_of_p_eq_B (G := G) C hG hPB p hp
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
      exact ⟨by simpa only [Finset.mem_union, Finset.mem_singleton] using hvCaptured,
        hpv⟩
    · exact fun hv ↦ hv.2
  have hZs : Disjoint C.Z {C.s} := by
    rw [Finset.disjoint_left]
    intro v hvZ hvs
    exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C
      (Finset.mem_singleton.mp hvs ▸ hvZ)
  have hZsH : Disjoint (C.Z ∪ {C.s}) C.H := by
    rw [Finset.disjoint_left]
    intro v hvZs hvH
    rcases Finset.mem_union.mp hvZs with hvZ | hvs
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
    · have hvs' : v = C.s := Finset.mem_singleton.mp hvs
      subst v
      exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1 hvH
  have hAllP : Disjoint (C.Z ∪ {C.s} ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvP
    rcases Finset.mem_union.mp hvLeft with hvZs | hvH
    · rcases Finset.mem_union.mp hvZs with hvZ | hvs
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
      · have hvs' : v = C.s := Finset.mem_singleton.mp hvs
        subst v
        exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  calc
    (∑ p ∈ C.P, G.outdegree p) =
        edgeCount G C.P (C.Z ∪ {C.s} ∪ C.H ∪ C.P) := by
      unfold edgeCount
      apply Finset.sum_congr rfl
      intro p hp
      exact hPointwise p hp
    _ = edgeCount G C.P (C.Z ∪ {C.s} ∪ C.H) +
        edgeCount G C.P C.P :=
      edgeCount_union_of_disjoint G C.P _ _ hAllP
    _ = (edgeCount G C.P (C.Z ∪ {C.s}) + edgeCount G C.P C.H) +
        edgeCount G C.P C.P := by
      rw [edgeCount_union_of_disjoint G C.P _ _ hZsH]
    _ = ((edgeCount G C.P C.Z + edgeCount G C.P {C.s}) +
        edgeCount G C.P C.H) + edgeCount G C.P C.P := by
      rw [edgeCount_union_of_disjoint G C.P _ _ hZs]
    _ = edgeCount G C.P C.Z + (∑ p ∈ C.P, epsilonAt G p C.s) +
        edgeCount G C.P C.H + edgeCount G C.P C.P := by
      rw [edgeCount_singleton (G := G)]

/-- Arc counting against the optional-root target agrees with the split count. -/
theorem edgeCount_externalTargets (C : G.LocalConfiguration) :
    edgeCount G C.P (externalTargets G C) =
      edgeCount G C.P C.Z + ∑ p ∈ C.P, epsilonAt G p C.s := by
  by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
  · have hDisjoint : Disjoint C.Z {C.s} := by
      rw [Finset.disjoint_left]
      intro v hvZ hvs
      exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C
        (Finset.mem_singleton.mp hvs ▸ hvZ)
    rw [externalTargets, rootSecondFinset, if_pos hReach,
      edgeCount_union_of_disjoint G C.P C.Z {C.s} hDisjoint,
      edgeCount_singleton]
  · have hNoArc : ∀ p ∈ C.P, ¬G.Adj p C.s := by
      intro p hp hps
      exact hReach ⟨p, hp, hps⟩
    have hSumZero : ∑ p ∈ C.P, epsilonAt G p C.s = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [epsilonAt, hNoArc p hp]
    rw [externalTargets, rootSecondFinset, if_neg hReach, Finset.union_empty,
      hSumZero, Nat.add_zero]

/-- If `P=B`, every outgoing arc of an `H`-vertex lands in `A∪P`. -/
theorem H_outgoingCaptured (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPB : C.P = C.B) (u : V) (huH : u ∈ C.H) :
    G.outNeighborFinset u ⊆ C.A ∪ C.P := by
  intro v huvOut
  have huv : G.Adj u v :=
    (Digraph.mem_outNeighborFinset (G := G)).mp huvOut
  by_cases hvA : v ∈ C.A
  · exact Finset.mem_union_left C.P hvA
  · have hsu : G.Adj C.s u :=
      (Digraph.mem_outNeighborFinset (G := G)).mp
        (Digraph.LocalConfiguration.H_subset_A (G := G) C huH)
    have hvs : v ≠ C.s := by
      intro h
      subst v
      exact hG.2 hsu huv
    have hvB : v ∈ C.B := by
      change v ∈ G.secondOutNeighborFinset C.s
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨u, hsu, huv⟩,
        fun hsv ↦ hvA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv),
        hvs⟩
    exact Finset.mem_union_right C.A (by simpa [hPB] using hvB)

/-- The total degree of `H` splits exactly into arcs toward `A` and `P`. -/
theorem degreeSum_H_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) :
    ∑ u ∈ C.H, G.outdegree u = edgeCount G C.H C.A + edgeCount G C.H C.P := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hPointwise : ∀ u ∈ C.H,
      G.outdegree u = directCount G C.A u + directCount G C.P u := by
    intro u hu
    have hEq : G.outNeighborFinset u =
        (C.A ∪ C.P).filter fun v ↦ G.Adj u v := by
      ext v
      simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
        Finset.mem_union]
      constructor
      · intro huv
        have hvCaptured := H_outgoingCaptured G C hG hPB u hu
          ((Digraph.mem_outNeighborFinset (G := G)).mpr huv)
        exact ⟨by simpa only [Finset.mem_union] using hvCaptured, huv⟩
      · exact fun hv ↦ hv.2
    unfold Digraph.outdegree
    rw [hEq]
    simpa [directCount, CertificateBridge.internalFirstNeighbors,
      Finset.filter_union] using
        Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter (p := fun v ↦ G.Adj u v)
            (q := fun v ↦ G.Adj u v) hAP)
  calc
    (∑ u ∈ C.H, G.outdegree u) =
        ∑ u ∈ C.H, (directCount G C.A u + directCount G C.P u) := by
      apply Finset.sum_congr rfl
      exact hPointwise
    _ = edgeCount G C.H C.A + edgeCount G C.H C.P := by
      unfold edgeCount
      rw [Finset.sum_add_distrib]

/-- Only vertices in `X` can send an arc from `H` back to `a1`. -/
theorem H_to_a1_le_x (C : G.LocalConfiguration) (hG : G.IsOriented) :
    edgeCount G C.H {C.a1} ≤ C.x := by
  have hSubset : C.H.filter (fun u ↦ G.Adj u C.a1) ⊆ C.X := by
    intro u hu
    rcases Finset.mem_filter.mp hu with ⟨huH, hua1⟩
    rcases Finset.mem_union.mp huH with huA1 | huX
    · exact (hG.2 (Finset.mem_filter.mp huA1).2 hua1).elim
    · exact huX
  rw [edgeCount_eq_sum_incoming G C.H {C.a1}]
  simp only [Finset.sum_singleton, internalInDegree]
  exact Finset.card_le_card hSubset

/-- Only vertices in `X` can send arcs from `H` into `R`. -/
theorem H_to_R_le_x_mul_card_R (C : G.LocalConfiguration) :
    edgeCount G C.H C.R ≤ C.x * C.R.card := by
  have hIncoming : ∀ r ∈ C.R, internalInDegree G C.H r ≤ C.x := by
    intro r hr
    apply Finset.card_le_card
    intro u hu
    rcases Finset.mem_filter.mp hu with ⟨huH, hur⟩
    rcases Finset.mem_union.mp huH with huA1 | huX
    · have hrX : r ∈ C.X := by
        apply Finset.mem_inter.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          exact ⟨u, Finset.mem_union_left C.P huA1, hur⟩
        · apply Finset.mem_sdiff.mpr
          have hrParts := (Finset.mem_sdiff.mp hr).2
          refine ⟨(Digraph.LocalConfiguration.R_subset_A (G := G) C hr), ?_⟩
          intro hrA1a1
          apply hrParts
          rcases Finset.mem_union.mp hrA1a1 with hrA1 | hra1
          · exact Finset.mem_union_left {C.a1}
              (Finset.mem_union_left C.X hrA1)
          · exact Finset.mem_union_right (C.A1 ∪ C.X) hra1
      exact ((Finset.mem_sdiff.mp hr).2
        (Finset.mem_union_left {C.a1}
          (Finset.mem_union_right C.A1 hrX))).elim
    · exact huX
  rw [edgeCount_eq_sum_incoming G C.H C.R]
  calc
    (∑ r ∈ C.R, internalInDegree G C.H r) ≤
        ∑ _r ∈ C.R, C.x := by
      apply Finset.sum_le_sum
      exact hIncoming
    _ = C.x * C.R.card := by simp [Nat.mul_comm]

/-- The possible arcs from `H` into `A` satisfy the local capacity bound. -/
theorem H_to_A_le_internal_add_x_add_xR (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    edgeCount G C.H C.A ≤
      C.H.card.choose 2 + C.x + C.x * C.R.card := by
  have hHa1 : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hva1
    have hv : v = C.a1 := Finset.mem_singleton.mp hva1
    subst v
    rcases Finset.mem_union.mp hvH with ha1A1 | ha1X
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 ha1A1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C ha1X
  have hPartsR : Disjoint (C.H ∪ {C.a1}) C.R := by
    simpa [Digraph.LocalConfiguration.H] using
      Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hA : C.H ∪ {C.a1} ∪ C.R = C.A := by
    simpa [Digraph.LocalConfiguration.H] using
      Digraph.LocalConfiguration.local_parts_union_R (G := G) C
  rw [← hA,
    edgeCount_union_of_disjoint G C.H (C.H ∪ {C.a1}) C.R hPartsR,
    edgeCount_union_of_disjoint G C.H C.H {C.a1} hHa1]
  have hInternal := internal_edgeCount_le_choose_two G C.H hG
  have hBack := H_to_a1_le_x G C hG
  have hR := H_to_R_le_x_mul_card_R G C
  omega

/-- Generic form of the retained-set degree-capacity inequality. -/
theorem equationFive (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B) :
    8 * C.H.card ≤ edgeCount G C.H C.P +
      C.H.card.choose 2 + C.x + C.x * C.R.card := by
  have hDegreeLower : 8 * C.H.card ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      8 * C.H.card = ∑ _u ∈ C.H, 8 := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ C.H, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hDegreeSplit := degreeSum_H_eq_A_add_P G C hG hPB
  have hA := H_to_A_le_internal_add_x_add_xR G C hG
  omega

end SeymourEight.Shared
