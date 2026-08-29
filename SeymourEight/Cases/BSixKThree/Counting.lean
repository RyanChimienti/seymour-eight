import SeymourEight.Cases.BSixKThree.Basic
import SeymourEight.Shared.LocalDegree

/-!
# Counting reduction for the `(6,3)` case

The set `Y` consists of the vertices of `Q` reached in two steps from the
pivot.  It is needed only when `|P|=5`; when `|P|=6`, `Q` is empty and the
existing shared `P=B` accounting applies directly.
-/

namespace SeymourEight.BSixKThree

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The part of `Q` reached from the first neighborhood of `a₁`. -/
def Y (C : G.LocalConfiguration) : Finset V :=
  C.Q ∩ G.outNeighborFinsetOf (C.A1 ∪ C.P)

def y (C : G.LocalConfiguration) : Nat := (Y G C).card

theorem Y_subset_Q (C : G.LocalConfiguration) : Y G C ⊆ C.Q :=
  Finset.inter_subset_left

/-- `X` is represented among the strict second neighbors of `a₁`. -/
theorem X_subset_second_a1 (C : G.LocalConfiguration) (_hG : G.IsOriented) :
    C.X ⊆ G.secondOutNeighborFinset C.a1 := by
  intro v hvX
  rcases Finset.mem_inter.mp hvX with ⟨hvReached, hvOutside⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached with
    ⟨u, hu, huv⟩
  have ha1u : G.Adj C.a1 u := by
    rcases Finset.mem_union.mp hu with huA1 | huP
    · exact (Finset.mem_filter.mp huA1).2
    · exact (Finset.mem_filter.mp huP).2
  have hvNotParts := (Finset.mem_sdiff.mp hvOutside).2
  have hvNotDirect : ¬G.Adj C.a1 v := by
    intro ha1v
    exact hvNotParts (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hvOutside).1, ha1v⟩))
  have hva1 : v ≠ C.a1 := by
    intro h
    exact hvNotParts (Finset.mem_union_right _ (by simp [h]))
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨u, ha1u, huv⟩, hvNotDirect, hva1⟩

/-- The reached part of `Q` is represented among the strict second neighbors. -/
theorem Y_subset_second_a1 (C : G.LocalConfiguration) (_hG : G.IsOriented) :
    Y G C ⊆ G.secondOutNeighborFinset C.a1 := by
  intro v hvY
  rcases Finset.mem_inter.mp hvY with ⟨hvQ, hvReached⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached with
    ⟨u, hu, huv⟩
  have ha1u : G.Adj C.a1 u := by
    rcases Finset.mem_union.mp hu with huA1 | huP
    · exact (Finset.mem_filter.mp huA1).2
    · exact (Finset.mem_filter.mp huP).2
  have hvNotDirect : ¬G.Adj C.a1 v := by
    intro ha1v
    have hvP : v ∈ C.P := Finset.mem_filter.mpr
      ⟨Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ, ha1v⟩
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hvQ
  have hva1 : v ≠ C.a1 := by
    intro h
    subst v
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
        C.a1_mem_root_outNeighbors
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨u, ha1u, huv⟩, hvNotDirect, hva1⟩

/-- Every external target is a strict second neighbor of `a₁`. -/
theorem externalTargets_subset_second_a1 (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    externalTargets G C ⊆ G.secondOutNeighborFinset C.a1 := by
  intro v hvW
  rcases Finset.mem_union.mp hvW with hvZ | hvRoot
  · rcases Finset.mem_sdiff.mp hvZ with ⟨hvReached, hvUnknown⟩
    rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached with
      ⟨p, hp, hpv⟩
    have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hp).2
    have hvNotDirect : ¬G.Adj C.a1 v := by
      intro ha1v
      have hvParts : v ∈ C.A1 ∪ C.P := by
        rw [← Shared.outNeighborFinset_a1_eq_A1_union_P G C hG]
        exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1v
      rcases Finset.mem_union.mp hvParts with hvA | hvP
      · exact hvUnknown (Finset.mem_union_left C.B
          (Finset.mem_union_right {C.s}
            (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA)))
      · exact hvUnknown (Finset.mem_union_right ({C.s} ∪ C.A)
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP))
    have hva1 : v ≠ C.a1 := by
      intro h
      subst v
      exact hvUnknown (Finset.mem_union_left C.B
        (Finset.mem_union_right {C.s} C.a1_mem_root_outNeighbors))
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨p, ha1p, hpv⟩, hvNotDirect, hva1⟩
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by
        simpa [externalTargets, rootSecondFinset, hReach] using hvRoot
      subst v
      obtain ⟨p, hp, hps⟩ := hReach
      have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hp).2
      have hsa1 : G.Adj C.s C.a1 :=
        (Digraph.mem_outNeighborFinset (G := G)).mp
          C.a1_mem_root_outNeighbors
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨p, ha1p, hps⟩, hG.2 hsa1,
        fun h ↦ hG.1 C.s (h ▸ hsa1)⟩
    · simp [rootSecondFinset, hReach] at hvRoot

theorem disjoint_X_Y (C : G.LocalConfiguration) : Disjoint C.X (Y G C) := by
  rw [Finset.disjoint_left]
  intro v hvX hvY
  exact (Finset.disjoint_left.mp
    (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
      (Digraph.LocalConfiguration.X_subset_A (G := G) C hvX)
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (Y_subset_Q G C hvY))

theorem disjoint_X_union_Y_external (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    Disjoint (C.X ∪ Y G C) (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvXY hvW
  rcases Finset.mem_union.mp hvXY with hvX | hvY
  · rcases Finset.mem_union.mp hvW with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
          (Finset.mem_union_right C.A1 hvX)
    · exact (Finset.disjoint_left.mp
        (Shared.disjoint_X_union_Z_rootSecond G C hG))
          (Finset.mem_union_left C.Z hvX) hvRoot
  · rcases Finset.mem_union.mp hvW with hvZ | hvRoot
    · apply (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
      exact Finset.mem_union_right ({C.s} ∪ C.A)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C (Y_subset_Q G C hvY))
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : v = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_B (G := G) C
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C (Y_subset_Q G C hvY))
      · simp [rootSecondFinset, hReach] at hvRoot

/-- The represented target families give a lower bound on the second degree. -/
theorem represented_targets_le_secondOutdegree (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    C.x + y G C + (externalTargets G C).card ≤
      G.secondOutdegree C.a1 := by
  have hSubset : C.X ∪ Y G C ∪ externalTargets G C ⊆
      G.secondOutNeighborFinset C.a1 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvXY | hvW
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact X_subset_second_a1 G C hG hvX
      · exact Y_subset_second_a1 G C hG hvY
    · exact externalTargets_subset_second_a1 G C hG hvW
  have hCard := Finset.card_le_card hSubset
  rw [Finset.card_union_of_disjoint (disjoint_X_union_Y_external G C hG),
    Finset.card_union_of_disjoint (disjoint_X_Y G C)] at hCard
  exact hCard

/-- The no-Seymour condition supplies the basic parameter inequality. -/
theorem represented_targets_lt_degree (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hk : C.k = 3) :
    C.x + y G C + (C.z + epsilonS G C) < 3 + C.r := by
  have hNot : ¬G.IsSeymourVertex C.a1 := by
    intro h
    exact hNoSeymour ⟨C.a1, h⟩
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
  have hRepresented := represented_targets_le_secondOutdegree G C hG
  rw [Shared.card_externalTargets G C] at hRepresented
  have hDegree := outdegree_a1_eq_three_add_r G C hG hk
  omega

/-- If `r=6`, then `P=B`. -/
theorem p_eq_B_of_r_six (C : G.LocalConfiguration)
    (hBCard : C.B.card = 6) (hr : C.r = 6) : C.P = C.B := by
  apply Finset.eq_of_subset_of_card_le
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  rw [show C.P.card = 6 from hr, hBCard]

/-- The `r=6` branch embeds into one of the three maximal certificate rows. -/
theorem r_six_parameter_rows (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3)
    (hr : C.r = 6) :
    (C.x = 2 ∧ C.z + epsilonS G C ≤ 6) ∨
      (C.x = 3 ∧ C.z + epsilonS G C ≤ 5) ∨
      (C.x = 4 ∧ C.z + epsilonS G C ≤ 4) := by
  have hxLower := two_le_x G C hG hPivot hk
  have hxUpper := x_le_four G C hG hRootDegree hk
  have hBasic := represented_targets_lt_degree G C hG hNoSeymour hk
  rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 by omega) with hx | hx | hx
  · exact Or.inl ⟨hx, by omega⟩
  · exact Or.inr (Or.inl ⟨hx, by omega⟩)
  · exact Or.inr (Or.inr ⟨hx, by omega⟩)

omit [Fintype V] in
theorem edgeCount_source_union (S T U : Finset V) (hST : Disjoint S T) :
    edgeCount G (S ∪ T) U = edgeCount G S U + edgeCount G T U := by
  classical
  unfold edgeCount
  rw [Finset.sum_union hST]

omit [Fintype V] [DecidableEq V] in
theorem edgeCount_mono_right (S T U : Finset V)
    (hArcs : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v → v ∈ U) :
    edgeCount G S T ≤ edgeCount G S U := by
  classical
  unfold edgeCount directCount internalFirstNeighbors
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.card_le_card
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvT, huv⟩
  exact Finset.mem_filter.mpr ⟨hArcs u hu v hvT huv, huv⟩

/-- Without assuming `P=B`, an `H`-vertex is still captured by `A∪B`. -/
theorem H_outgoingCaptured_general (C : G.LocalConfiguration)
    (hG : G.IsOriented) (u : V) (huH : u ∈ C.H) :
    G.outNeighborFinset u ⊆ C.A ∪ C.B := by
  intro v huvOut
  have huv : G.Adj u v :=
    (Digraph.mem_outNeighborFinset (G := G)).mp huvOut
  by_cases hvA : v ∈ C.A
  · exact Finset.mem_union_left C.B hvA
  · have hsu : G.Adj C.s u :=
      (Digraph.mem_outNeighborFinset (G := G)).mp
        (Digraph.LocalConfiguration.H_subset_A (G := G) C huH)
    have hvs : v ≠ C.s := fun h ↦ by
      subst v
      exact hG.2 hsu huv
    have hvB : v ∈ C.B := by
      change v ∈ G.secondOutNeighborFinset C.s
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨u, hsu, huv⟩,
        fun hsv ↦ hvA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv), hvs⟩
    exact Finset.mem_union_right C.A hvB

/-- Total `H` degree splits into the `A`, `P`, and `Q` blocks. -/
theorem degreeSum_H_eq_A_add_P_add_Q (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    ∑ u ∈ C.H, G.outdegree u =
      edgeCount G C.H C.A + edgeCount G C.H C.P + edgeCount G C.H C.Q := by
  have hAB : Disjoint C.A C.B :=
    Digraph.LocalConfiguration.disjoint_A_B (G := G) C
  have hPointwise : ∀ u ∈ C.H,
      G.outdegree u = directCount G C.A u + directCount G C.B u := by
    intro u hu
    unfold Digraph.outdegree directCount internalFirstNeighbors
    have hCaptured := H_outgoingCaptured_general G C hG u hu
    have hEq : G.outNeighborFinset u =
        (C.A ∪ C.B).filter fun v ↦ G.Adj u v := by
      ext v
      simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
        Finset.mem_union]
      constructor
      · intro huv
        exact ⟨by simpa only [Finset.mem_union] using
          hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩
      · exact fun hv ↦ hv.2
    rw [hEq, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hAB)]
  calc
    (∑ u ∈ C.H, G.outdegree u) =
        ∑ u ∈ C.H, (directCount G C.A u + directCount G C.B u) := by
      apply Finset.sum_congr rfl
      exact hPointwise
    _ = edgeCount G C.H C.A + edgeCount G C.H C.B := by
      unfold edgeCount
      rw [Finset.sum_add_distrib]
    _ = edgeCount G C.H C.A +
        (edgeCount G C.H C.P + edgeCount G C.H C.Q) := by
      rw [← Shared.edgeCount_union_of_disjoint G C.H C.P C.Q
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C),
        Digraph.LocalConfiguration.P_union_Q (G := G) C]
    _ = _ := by omega

/-- Arcs from `H` into `Q` have capacity `x|Q|+3y`: an `A₁` arc
necessarily makes its target a member of `Y`. -/
theorem H_to_Q_le (C : G.LocalConfiguration) (hk : C.k = 3) :
    edgeCount G C.H C.Q ≤ C.x * C.Q.card + 3 * y G C := by
  have hSplit : edgeCount G C.H C.Q =
      edgeCount G C.A1 C.Q + edgeCount G C.X C.Q := by
    simpa [Digraph.LocalConfiguration.H] using
      edgeCount_source_union G C.A1 C.X C.Q
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hA1Y : edgeCount G C.A1 C.Q ≤ edgeCount G C.A1 (Y G C) := by
    apply edgeCount_mono_right G
    intro u hu v hvQ huv
    apply Finset.mem_inter.mpr
    exact ⟨hvQ, (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      ⟨u, Finset.mem_union_left C.P hu, huv⟩⟩
  have hA1Cap := Shared.edgeCount_le_card_mul_card G C.A1 (Y G C)
  have hXCap := Shared.edgeCount_le_card_mul_card G C.X C.Q
  change C.A1.card = 3 at hk
  rw [hk] at hA1Cap
  change edgeCount G C.H C.Q ≤
    C.X.card * C.Q.card + 3 * (Y G C).card
  omega

/-- Generalized retained-set capacity, valid also in the `r=5` branch. -/
theorem H_degree_capacity_general (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) :
    8 * C.H.card ≤ edgeCount G C.H C.P +
      C.H.card.choose 2 + C.x + C.x * C.R.card +
        C.x * C.Q.card + 3 * y G C := by
  have hLower : 8 * C.H.card ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      8 * C.H.card = ∑ _u ∈ C.H, 8 := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ C.H, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hSplit := degreeSum_H_eq_A_add_P_add_Q G C hG
  have hA := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  have hQ := H_to_Q_le G C hk
  omega

/-- Every outgoing arc of a `P`-vertex is represented by `H`, `P`, `Q`, or
the external target set. -/
theorem P_outgoingCaptured_general (C : G.LocalConfiguration)
    (hG : G.IsOriented) (p : V) (hp : p ∈ C.P) :
    G.outNeighborFinset p ⊆
      C.H ∪ C.P ∪ C.Q ∪ externalTargets G C := by
  intro v hvOut
  have hpv : G.Adj p v :=
    (Digraph.mem_outNeighborFinset (G := G)).mp hvOut
  by_cases hvs : v = C.s
  · subst v
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    simp [rootSecondFinset, show ∃ q ∈ C.P, G.Adj q C.s from
      ⟨p, hp, hpv⟩]
  by_cases hvA : v ∈ C.A
  · have hvH : v ∈ C.H := by
      by_cases hvA1 : v ∈ C.A1
      · exact Finset.mem_union_left C.X hvA1
      · have hva1 : v ≠ C.a1 := by
          intro h
          subst v
          exact hG.2 (Finset.mem_filter.mp hp).2 hpv
        apply Finset.mem_union_right
        apply Finset.mem_inter.mpr
        exact ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩,
          Finset.mem_sdiff.mpr ⟨hvA, by simp [hvA1, hva1]⟩⟩
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hvH))
  by_cases hvB : v ∈ C.B
  · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hvB
    rcases Finset.mem_union.mp hvB with hvP | hvQ
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ hvP))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvQ)
  · have hvZ : v ∈ C.Z := Finset.mem_sdiff.mpr ⟨
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr ⟨p, hp, hpv⟩,
      by simp [hvs, hvA, hvB]⟩
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hvZ)

theorem disjoint_H_externalTargets (C : G.LocalConfiguration)
    (hG : G.IsOriented) : Disjoint C.H (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvH hvW
  rcases Finset.mem_union.mp hvW with hvZ | hvRoot
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1 hvH
    · simp [rootSecondFinset, hReach] at hvRoot

theorem disjoint_B_externalTargets (C : G.LocalConfiguration) :
    Disjoint C.B (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvB hvW
  rcases Finset.mem_union.mp hvW with hvZ | hvRoot
  · apply (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
    exact Finset.mem_union_right ({C.s} ∪ C.A) hvB
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_B (G := G) C hvB
    · simp [rootSecondFinset, hReach] at hvRoot

/-- Exact `P`-degree accounting in the four represented target blocks. -/
theorem degreeSum_P_eq_blocks (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    ∑ p ∈ C.P, G.outdegree p =
      edgeCount G C.P C.H + edgeCount G C.P C.P +
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
  let W := externalTargets G C
  have hHP : Disjoint C.H C.P :=
    Digraph.LocalConfiguration.disjoint_H_P (G := G) C
  have hHQ : Disjoint C.H C.Q := by
    rw [Finset.disjoint_left]
    intro v hvH hvQ
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
        (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
  have hHPQ : Disjoint (C.H ∪ C.P) C.Q := by
    rw [Finset.disjoint_left]
    intro v hv hvQ
    rcases Finset.mem_union.mp hv with hvH | hvP
    · exact (Finset.disjoint_left.mp hHQ) hvH hvQ
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hvQ
  have hAllW : Disjoint (C.H ∪ C.P ∪ C.Q) W := by
    rw [Finset.disjoint_left]
    intro v hv hvW
    rcases Finset.mem_union.mp hv with hvHP | hvQ
    · rcases Finset.mem_union.mp hvHP with hvH | hvP
      · exact (Finset.disjoint_left.mp (disjoint_H_externalTargets G C hG)) hvH hvW
      · exact (Finset.disjoint_left.mp (disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvW
    · exact (Finset.disjoint_left.mp (disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvW
  have hPointwise : ∀ p ∈ C.P, G.outdegree p =
      directCount G C.H p + directCount G C.P p + directCount G C.Q p +
        directCount G W p := by
    intro p hp
    have hCaptured := P_outgoingCaptured_general G C hG p hp
    have hEq : G.outNeighborFinset p =
        (C.H ∪ C.P ∪ C.Q ∪ W).filter fun v ↦ G.Adj p v := by
      ext v
      simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
        Finset.mem_union]
      constructor
      · intro hpv
        exact ⟨by simpa only [Finset.mem_union] using
          hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv), hpv⟩
      · exact fun hv ↦ hv.2
    unfold Digraph.outdegree
    rw [hEq]
    change directCount G (C.H ∪ C.P ∪ C.Q ∪ W) p = _
    rw [Shared.directCount_union_of_disjoint G (C.H ∪ C.P ∪ C.Q) W p hAllW,
      Shared.directCount_union_of_disjoint G (C.H ∪ C.P) C.Q p hHPQ,
      Shared.directCount_union_of_disjoint G C.H C.P p hHP]
  calc
    (∑ p ∈ C.P, G.outdegree p) = ∑ p ∈ C.P,
        (directCount G C.H p + directCount G C.P p + directCount G C.Q p +
          directCount G W p) := by
      apply Finset.sum_congr rfl
      exact hPointwise
    _ = _ := by
      unfold edgeCount W
      simp only [Finset.sum_add_distrib]

/-- The `P` degree lower bound after orientation and internal capacities. -/
theorem P_degree_capacity_general (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hr : C.r = 5) :
    40 + edgeCount G C.H C.P ≤
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) +
        5 * C.H.card + 10 := by
  have hPCard : C.P.card = 5 := hr
  have hLower : 40 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      40 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_P_eq_blocks G C hG
  have hCross := Shared.cross_edgeCount_add_reverse_le G C.H C.P hG
  have hInternal := Shared.internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hCross hInternal
  simp [Nat.choose] at hInternal
  omega

/-- All `P→Q` arcs land in `Y`; together with the external rectangle this
gives the upper bound used by the arithmetic reduction. -/
theorem P_to_Q_external_le (C : G.LocalConfiguration) (hr : C.r = 5) :
    edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) ≤
      5 * (y G C + (C.z + epsilonS G C)) := by
  have hPY : edgeCount G C.P C.Q ≤ edgeCount G C.P (Y G C) := by
    apply edgeCount_mono_right G
    intro p hp v hvQ hpv
    exact Finset.mem_inter.mpr ⟨hvQ,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩⟩
  have hYCap := Shared.edgeCount_le_card_mul_card G C.P (Y G C)
  have hWCap := Shared.edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hPCard : C.P.card = 5 := hr
  rw [hPCard] at hYCap hWCap
  rw [Shared.card_externalTargets G C] at hWCap
  unfold y
  omega

/-- The exceptional `r=5` branch has only the maximal `(5,2,4)` core. -/
theorem r_five_parameter_row (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 6) (hk : C.k = 3) (hr : C.r = 5) :
    C.x = 2 ∧ y G C = 1 ∧ C.z + epsilonS G C ≤ 4 := by
  have hxLower := two_le_x G C hG hPivot hk
  have hxUpper := x_le_four G C hG hRootDegree hk
  have hHCard := H_card_eq_three_add_x G C hk
  have hRCard := card_R_eq_four_sub_x G C hG hRootDegree hk
  have hQCard := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
  rw [hBCard, hr] at hQCard
  have hQCardEq : C.Q.card = 1 := by omega
  have hyLe : y G C ≤ 1 := by
    exact (Finset.card_le_card (Y_subset_Q G C)).trans_eq hQCardEq
  have hBasic := represented_targets_lt_degree G C hG hNoSeymour hk
  have hH := H_degree_capacity_general G C hG hMin hk
  have hP := P_degree_capacity_general G C hG hMin hr
  have hUpper := P_to_Q_external_le G C hr
  rw [hHCard, hRCard, hQCardEq] at hH
  rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 by omega) with hx | hx | hx
  · simp only [hx, Nat.choose] at hH
    constructor
    · exact hx
    constructor <;> omega
  · simp only [hx, Nat.choose] at hH
    omega
  · simp only [hx, Nat.choose] at hH
    omega

theorem parameterRows (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 6) (hk : C.k = 3) :
    (C.r = 5 ∧ C.x = 2 ∧ C.z + epsilonS G C ≤ 4) ∨
      (C.r = 6 ∧ C.x = 2 ∧ C.z + epsilonS G C ≤ 6) ∨
      (C.r = 6 ∧ C.x = 3 ∧ C.z + epsilonS G C ≤ 5) ∨
      (C.r = 6 ∧ C.x = 4 ∧ C.z + epsilonS G C ≤ 4) := by
  rcases r_eq_five_or_six G C hG hMin hBCard hk with hr | hr
  · have hRow := r_five_parameter_row G C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hr
    exact Or.inl ⟨hr, hRow.1, hRow.2.2⟩
  · rcases r_six_parameter_rows G C hG hNoSeymour hRootDegree hPivot hk hr with
      hx | hx | hx
    · exact Or.inr (Or.inl ⟨hr, hx⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hr, hx⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hr, hx⟩))

/-- In the largest row, the external block is necessarily full and the two
aggregate edge bounds used by the strengthened finite certificate hold. -/
theorem x_four_aggregate_bounds (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 6) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 4)
    (hExternalCard : C.z + epsilonS G C ≤ 4) :
    (externalTargets G C).card = 4 ∧
      31 ≤ edgeCount G C.H C.P ∧
      22 ≤ edgeCount G C.P (externalTargets G C) := by
  have hPB := p_eq_B_of_r_six G C hBCard hr
  have hPCard : C.P.card = 6 := hr
  have hHCard := H_card_eq_three_add_x G C hk
  have hRCard : C.R.card = 0 := by
    have hR := card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHBound := Shared.equationFive G C hG hMin hPB
  rw [hHCard, hx, hRCard] at hHBound
  simp only [Nat.choose] at hHBound
  have hHP : 31 ≤ edgeCount G C.H C.P := by omega
  have hQCard : C.Q.card = 0 := by
    have hQ := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hPQ : edgeCount G C.P C.Q = 0 := by
    have hCap := Shared.edgeCount_le_card_mul_card G C.P C.Q
    rw [hQCard] at hCap
    omega
  have hLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_P_eq_blocks G C hG
  have hCross := Shared.cross_edgeCount_add_reverse_le G C.H C.P hG
  have hInternal := Shared.internal_edgeCount_le_choose_two G C.P hG
  rw [hHCard, hx, hPCard] at hCross
  rw [hPCard] at hInternal
  simp only [Nat.choose] at hInternal
  have hPW : 22 ≤ edgeCount G C.P (externalTargets G C) := by omega
  have hWCap := Shared.edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, Shared.card_externalTargets G C] at hWCap
  have hWCard : (externalTargets G C).card = 4 := by
    rw [Shared.card_externalTargets G C]
    omega
  exact ⟨hWCard, hHP, hPW⟩

end SeymourEight.BSixKThree
