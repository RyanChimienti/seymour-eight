import SeymourEight.LocalConfiguration

set_option linter.style.header false

/-!
# Shared local-neighborhood infrastructure

This module contains the local graph identities used by more than one case.
-/

namespace SeymourEight.Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every outneighbor of `a1` lies in `A1` or `P`, and conversely. -/
theorem outNeighborFinset_a1_eq_A1_union_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    G.outNeighborFinset C.a1 = C.A1 ∪ C.P := by
  ext v
  simp only [Digraph.mem_outNeighborFinset, Finset.mem_union,
    Digraph.LocalConfiguration.A1, Digraph.LocalConfiguration.P,
    Finset.mem_filter]
  constructor
  · intro ha1v
    by_cases hvA : v ∈ C.A
    · exact Or.inl ⟨hvA, ha1v⟩
    · right
      refine ⟨?_, ha1v⟩
      change v ∈ G.secondOutNeighborFinset C.s
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      have hsa1 : G.Adj C.s C.a1 :=
        (Digraph.mem_outNeighborFinset (G := G)).mp
          C.a1_mem_root_outNeighbors
      refine ⟨⟨C.a1, hsa1, ha1v⟩, ?_, ?_⟩
      · intro hsv
        apply hvA
        exact (Digraph.mem_outNeighborFinset (G := G)).mpr hsv
      · intro hvs
        subst v
        exact hG.2 hsa1 ha1v
  · rintro (⟨_vA, ha1v⟩ | ⟨_vB, ha1v⟩) <;> exact ha1v

/-- The sets `A1` and `P` are disjoint. -/
theorem disjoint_A1_P (C : G.LocalConfiguration) : Disjoint C.A1 C.P := by
  rw [Finset.disjoint_left]
  intro v hvA1 hvP
  exact (Finset.disjoint_left.mp
    (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
      (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA1)
      (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)

/-- The pivot's complete outdegree is `k+r`. -/
theorem outdegree_a1_eq_k_add_r (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    G.outdegree C.a1 = C.k + C.r := by
  unfold Digraph.outdegree
  rw [outNeighborFinset_a1_eq_A1_union_P G C hG,
    Finset.card_union_of_disjoint (disjoint_A1_P (G := G) C)]
  rfl

/-- The possible root contribution to the strict second neighborhood of `a1`. -/
def rootSecondFinset (C : G.LocalConfiguration) : Finset V :=
  if ∃ p ∈ C.P, G.Adj p C.s then {C.s} else ∅

/-- `epsilon_s` is one precisely when some member of `P` sends an arc to `s`. -/
def epsilonS (C : G.LocalConfiguration) : Nat :=
  (rootSecondFinset G C).card

@[simp]
theorem epsilonS_eq_ite (C : G.LocalConfiguration) :
    epsilonS G C = if ∃ p ∈ C.P, G.Adj p C.s then 1 else 0 := by
  by_cases h : ∃ p ∈ C.P, G.Adj p C.s <;>
    simp [epsilonS, rootSecondFinset, h]

/-- The root contribution `epsilon_s` is always zero or one. -/
theorem epsilonS_eq_zero_or_one (C : G.LocalConfiguration) :
    epsilonS G C = 0 ∨ epsilonS G C = 1 := by
  rw [epsilonS_eq_ite]
  split <;> simp

/--
Once `P=B`, the strict second neighbors of `a1` are exactly `X`, `Z`, and the
optional root `s`.
-/
theorem secondOutNeighborFinset_a1_eq (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) :
    G.secondOutNeighborFinset C.a1 = C.X ∪ C.Z ∪ rootSecondFinset G C := by
  classical
  ext v
  simp only [Finset.mem_union]
  constructor
  · intro hvSecond
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet] at hvSecond
    rcases hvSecond with ⟨⟨u, ha1u, huv⟩, hNotDirect, hva1⟩
    have huParts : u ∈ C.A1 ∪ C.P := by
      rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
      exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1u
    have hsa1 : G.Adj C.s C.a1 :=
      (Digraph.mem_outNeighborFinset (G := G)).mp
        C.a1_mem_root_outNeighbors
    by_cases hvs : v = C.s
    · subst v
      have huP : u ∈ C.P := by
        rcases Finset.mem_union.mp huParts with huA1 | huP
        · have hsu : G.Adj C.s u :=
            (Digraph.mem_outNeighborFinset (G := G)).mp
              (Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1)
          exact (hG.2 hsu huv).elim
        · exact huP
      apply Or.inr
      simp [rootSecondFinset, show ∃ p ∈ C.P, G.Adj p C.s from
        ⟨u, huP, huv⟩]
    by_cases hvA : v ∈ C.A
    · apply Or.inl; apply Or.inl
      apply Finset.mem_inter.mpr
      constructor
      · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        exact ⟨u, huParts, huv⟩
      · apply Finset.mem_sdiff.mpr
        refine ⟨hvA, ?_⟩
        intro hvParts
        rcases Finset.mem_union.mp hvParts with hvA1 | hva1'
        · exact hNotDirect (Finset.mem_filter.mp hvA1).2
        · exact hva1 (Finset.mem_singleton.mp hva1')
    · by_cases hvB : v ∈ C.B
      · have hvP : v ∈ C.P := by simpa [hPB] using hvB
        exact (hNotDirect (Finset.mem_filter.mp hvP).2).elim
      · apply Or.inl; apply Or.inr
        apply Finset.mem_sdiff.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          rcases Finset.mem_union.mp huParts with huA1 | huP
          · have hsu : G.Adj C.s u :=
              (Digraph.mem_outNeighborFinset (G := G)).mp
                (Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1)
            have hvSecondRoot : v ∈ G.secondOutNeighborFinset C.s := by
              rw [Digraph.mem_secondOutNeighborFinset,
                Digraph.mem_secondOutNeighborSet]
              exact ⟨⟨u, hsu, huv⟩,
                fun hsv ↦ hvA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv),
                hvs⟩
            exact (hvB hvSecondRoot).elim
          · exact ⟨u, huP, huv⟩
        · simp [hvs, hvA, hvB]
  · intro hvLocal
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    rcases hvLocal with (hvX | hvZ) | hvRoot
    · rcases Finset.mem_inter.mp hvX with ⟨hvReached, hvOutside⟩
      rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached with
        ⟨u, huParts, huv⟩
      have ha1u : G.Adj C.a1 u := by
        rcases Finset.mem_union.mp huParts with huA1 | huP
        · exact (Finset.mem_filter.mp huA1).2
        · exact (Finset.mem_filter.mp huP).2
      have hvNotParts := (Finset.mem_sdiff.mp hvOutside).2
      have hvNotA1 : v ∉ C.A1 := by
        intro hvA1
        exact hvNotParts (Finset.mem_union_left _ hvA1)
      have hva1 : v ≠ C.a1 := by
        intro h
        exact hvNotParts (Finset.mem_union_right _ (by simp [h]))
      exact ⟨⟨u, ha1u, huv⟩,
        fun ha1v ↦ hvNotA1 (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp hvOutside).1, ha1v⟩), hva1⟩
    · rcases Finset.mem_sdiff.mp hvZ with ⟨hvReached, hvUnknown⟩
      rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached with
        ⟨p, hpP, hpv⟩
      have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hpP).2
      have hvNotDirect : ¬G.Adj C.a1 v := by
        intro ha1v
        have hvParts : v ∈ C.A1 ∪ C.P := by
          rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
          exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1v
        rcases Finset.mem_union.mp hvParts with hvA1 | hvP
        · apply hvUnknown
          exact Finset.mem_union_left C.B <|
            Finset.mem_union_right {C.s} <|
              Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA1
        · apply hvUnknown
          exact Finset.mem_union_right ({C.s} ∪ C.A) <|
            Digraph.LocalConfiguration.P_subset_B (G := G) C hvP
      have hva1 : v ≠ C.a1 := by
        intro h
        subst v
        apply hvUnknown
        exact Finset.mem_union_left C.B <|
          Finset.mem_union_right {C.s} C.a1_mem_root_outNeighbors
      exact ⟨⟨p, ha1p, hpv⟩, hvNotDirect, hva1⟩
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : v = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        subst v
        obtain ⟨p, hpP, hps⟩ := hReach
        have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hpP).2
        have hsa1 : G.Adj C.s C.a1 :=
          (Digraph.mem_outNeighborFinset (G := G)).mp
            C.a1_mem_root_outNeighbors
        exact ⟨⟨p, ha1p, hps⟩, hG.2 hsa1,
          fun h ↦ hG.1 C.s (h ▸ hsa1)⟩
      · simp [rootSecondFinset, hReach] at hvRoot

/-- The three pieces in the second-neighborhood decomposition are disjoint. -/
theorem disjoint_X_union_Z_rootSecond (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    Disjoint (C.X ∪ C.Z) (rootSecondFinset G C) := by
  rw [Finset.disjoint_left]
  intro v hvXZ hvRoot
  by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
  · have hvs : v = C.s := by
      simpa [rootSecondFinset, hReach] using hvRoot
    subst v
    rcases Finset.mem_union.mp hvXZ with hsX | hsZ
    · exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
        (Digraph.LocalConfiguration.X_subset_A (G := G) C hsX)
    · exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hsZ
  · simp [rootSecondFinset, hReach] at hvRoot

/-- Cardinal form of the exact second-neighborhood decomposition. -/
theorem secondOutdegree_a1_eq_x_add_z_add_epsilonS
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B) :
    G.secondOutdegree C.a1 = C.x + C.z + epsilonS G C := by
  have hXZ : Disjoint C.X C.Z :=
    Finset.disjoint_left.mpr (by
      intro v hvX hvZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
          (Finset.mem_union_right C.A1 hvX))
  unfold Digraph.secondOutdegree Digraph.LocalConfiguration.x
    Digraph.LocalConfiguration.z epsilonS
  rw [secondOutNeighborFinset_a1_eq G C hG hPB,
    Finset.card_union_of_disjoint (disjoint_X_union_Z_rootSecond G C hG),
    Finset.card_union_of_disjoint hXZ]

/-- The external targets `Z` together with the optional reached root. -/
def externalTargets (C : G.LocalConfiguration) : Finset V :=
  C.Z ∪ rootSecondFinset G C

/-- `Z` and the optional root contribution are disjoint. -/
theorem disjoint_Z_rootSecond (C : G.LocalConfiguration) :
    Disjoint C.Z (rootSecondFinset G C) := by
  rw [Finset.disjoint_left]
  intro v hvZ hvRoot
  by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
  · have hvs : v = C.s := by
      simpa [rootSecondFinset, hReach] using hvRoot
    subst v
    exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hvZ
  · simp [rootSecondFinset, hReach] at hvRoot

/-- The external target capacity is exactly `z+epsilon_s`. -/
theorem card_externalTargets (C : G.LocalConfiguration) :
    (externalTargets G C).card = C.z + epsilonS G C := by
  unfold externalTargets Digraph.LocalConfiguration.z epsilonS
  rw [Finset.card_union_of_disjoint (disjoint_Z_rootSecond G C)]

end SeymourEight.Shared
