import SeymourEight.DegreeEight
import SeymourEight.Shared.Neighborhood

/-!
# The `(|B|, k) = (6, 2)` case

The common set identities come from the top-level shared layer.  Here we
specialize them to the forced data `P=B`, `|P|=6`, and `d⁺(a₁)=8`.
-/

namespace SeymourEight.BSixKTwo

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the `(6,2)` row, minimum degree forces all six vertices of `B` into `P`. -/
theorem r_eq_six (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 6) (hk : C.k = 2) :
    C.r = 6 := by
  have hDegree := hMin C.a1
  rw [outdegree_a1_eq_k_add_r G C hG, hk] at hDegree
  have hrLe : C.r ≤ 6 := by
    calc
      C.r = C.P.card := rfl
      _ ≤ C.B.card := Finset.card_le_card
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
      _ = 6 := hBCard
  omega

/-- Consequently `P=B`. -/
theorem p_eq_B (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 6) (hk : C.k = 2) :
    C.P = C.B := by
  apply Finset.eq_of_subset_of_card_le
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  rw [show C.P.card = 6 from r_eq_six G C hG hMin hBCard hk, hBCard]

/-- The pivot has exact outdegree eight. -/
theorem outdegree_a1_eq_eight (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 6) (hk : C.k = 2) :
    G.outdegree C.a1 = 8 := by
  rw [outdegree_a1_eq_k_add_r G C hG, hk,
    r_eq_six G C hG hMin hBCard hk]

/-- At `k=2`, the retained set `H=A₁∪X` has size `x+2`. -/
theorem h_card_eq_x_add_two (C : G.LocalConfiguration) (hk : C.k = 2) :
    C.H.card = C.x + 2 := by
  change C.h = C.x + 2
  rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk]
  omega

/-- At a degree-eight root, `X` and `R` have total size five. -/
theorem x_add_card_R_eq_five (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 2) :
    C.x + C.R.card = 5 := by
  have h := Digraph.LocalConfiguration.k_add_x_add_card_R_eq_seven
    (G := G) C hG.1 hRootDegree
  omega

/-- A counterexample satisfies `x+z+epsilon_s≤7` at the pivot. -/
theorem x_add_z_add_epsilonS_le_seven (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hBCard : C.B.card = 6) (hk : C.k = 2) :
    C.x + C.z + epsilonS G C ≤ 7 := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hSecond := secondOutdegree_a1_eq_x_add_z_add_epsilonS G C hG hPB
  have hDegree := outdegree_a1_eq_eight G C hG hMin hBCard hk
  have hNotA1 : ¬G.IsSeymourVertex C.a1 := by
    intro hSeymour
    exact hNoSeymour ⟨C.a1, hSeymour⟩
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNotA1
  omega

end SeymourEight.BSixKTwo
