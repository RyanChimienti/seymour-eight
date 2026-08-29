import SeymourEight.CaseFramework
import SeymourEight.DegreeEight
import SeymourEight.Shared.ArcCounting

/-!
# The `(|B|, k) = (6, 3)` case

Elementary cardinal reductions for this local leaf.
-/

namespace SeymourEight.BSixKThree

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimum degree leaves only `|P|=5` or `|P|=6`. -/
theorem r_eq_five_or_six (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 6) (hk : C.k = 3) :
    C.r = 5 ∨ C.r = 6 := by
  have hDegree := hMin C.a1
  rw [Shared.outdegree_a1_eq_k_add_r G C hG, hk] at hDegree
  have hrLe : C.r ≤ 6 := by
    calc
      C.r = C.P.card := rfl
      _ ≤ C.B.card := Finset.card_le_card
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
      _ = 6 := hBCard
  omega

/-- The pivot has degree eight or nine according as `|P|=5` or six. -/
theorem outdegree_a1_eq_three_add_r (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hk : C.k = 3) :
    G.outdegree C.a1 = 3 + C.r := by
  rw [Shared.outdegree_a1_eq_k_add_r G C hG, hk]

/-- The retained `A`-set has cardinality `3+x`. -/
theorem H_card_eq_three_add_x (C : G.LocalConfiguration) (hk : C.k = 3) :
    C.H.card = 3 + C.x := by
  change C.h = 3 + C.x
  rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk]

/-- The discarded set has cardinality `4-x`. -/
theorem card_R_eq_four_sub_x (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 3) :
    C.R.card = 4 - C.x := by
  have h := Digraph.LocalConfiguration.k_add_x_add_card_R_eq_seven
    (G := G) C hG.1 hRootDegree
  omega

/-- In particular, `x≤4`. -/
theorem x_le_four (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 3) : C.x ≤ 4 := by
  have h := Digraph.LocalConfiguration.k_add_x_add_card_R_eq_seven
    (G := G) C hG.1 hRootDegree
  omega

/-- An arc from `A₁` into `A` can only land in `A₁∪X`. -/
theorem A1_A_neighbors_subset_H (C : G.LocalConfiguration)
    (hG : G.IsOriented) (u : V) (hu : u ∈ C.A1) :
    internalFirstNeighbors G C.A u ⊆ internalFirstNeighbors G C.H u := by
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvA, huv⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, huv⟩
  by_cases hvA1 : v ∈ C.A1
  · exact Finset.mem_union_left C.X hvA1
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨u, Finset.mem_union_left C.P hu, huv⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨hvA, ?_⟩
      intro hvOld
      rcases Finset.mem_union.mp hvOld with hvA1' | hva1
      · exact hvA1 hvA1'
      · have hvEq : v = C.a1 := Finset.mem_singleton.mp hva1
        subst v
        exact hG.2 (Finset.mem_filter.mp hu).2 huv

/-- Pivot minimality and orientation force at least two vertices into `X`.
The aggregate argument is essential: the three `A₁` rows need nine outgoing
arcs in `A`, while at most three can remain internal to `A₁`. -/
theorem two_le_x (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 3) :
    2 ≤ C.x := by
  change 2 ≤ C.X.card
  have hA1Card : C.A1.card = 3 := hk
  have hLower : 9 ≤ edgeCount G C.A1 C.A := by
    calc
      9 = ∑ _u ∈ C.A1, 3 := by simp [hA1Card]
      _ ≤ ∑ u ∈ C.A1, directCount G C.A u := by
        apply Finset.sum_le_sum
        intro u hu
        simpa [directCount, internalFirstNeighbors, hk] using
          (hPivot u
            (Digraph.LocalConfiguration.A1_subset_A (G := G) C hu)).1
      _ = edgeCount G C.A1 C.A := rfl
  have hToH : edgeCount G C.A1 C.A ≤ edgeCount G C.A1 C.H := by
    unfold edgeCount directCount
    apply Finset.sum_le_sum
    intro u hu
    exact Finset.card_le_card (A1_A_neighbors_subset_H G C hG u hu)
  have hSplit : edgeCount G C.A1 C.H =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X := by
    exact Shared.edgeCount_union_of_disjoint G C.A1 C.A1 C.X
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hInternal := Shared.internal_edgeCount_le_choose_two G C.A1 hG
  have hCross := Shared.edgeCount_le_card_mul_card G C.A1 C.X
  rw [hA1Card] at hInternal hCross
  simp [Nat.choose] at hInternal
  omega

end SeymourEight.BSixKThree
