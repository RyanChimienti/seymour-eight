import SeymourEight.Cases.BSevenKTwo.Basic
import SeymourEight.Cases.BSixKThree.Counting

set_option linter.style.header false

/-!
# Counting reduction for the `(|B|, k) = (7, 2)` case

The graph-level inequalities in this file reduce a counterexample to 32
explicit parameter rows, grouped into fourteen families by `(r,x)` and root
status.
-/

namespace SeymourEight.BSevenKTwo

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimality forces at least two vertices into `X`. -/
theorem two_le_x (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) :
    2 ≤ C.x := by
  change 2 ≤ C.X.card
  have hA1Card : C.A1.card = 2 := hk
  have hLower : 4 ≤ edgeCount G C.A1 C.A := by
    calc
      4 = ∑ _u ∈ C.A1, 2 := by simp [hA1Card]
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
    exact Finset.card_le_card
      (BSixKThree.A1_A_neighbors_subset_H G C hG u hu)
  have hSplit : edgeCount G C.A1 C.H =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X := by
    exact edgeCount_union_of_disjoint G C.A1 C.A1 C.X
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hInternal := internal_edgeCount_le_choose_two G C.A1 hG
  have hCross := edgeCount_le_card_mul_card G C.A1 C.X
  rw [hA1Card] at hInternal hCross
  simp [Nat.choose] at hInternal
  omega

/-- At `k=2`, the retained set `H=A₁∪X` has cardinality `x+2`. -/
theorem H_card_eq_x_add_two (C : G.LocalConfiguration) (hk : C.k = 2) :
    C.H.card = C.x + 2 := by
  change C.h = C.x + 2
  rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk]
  omega

/-- At a degree-eight root and `k=2`, the sets `X` and `R` have total size five. -/
theorem x_add_card_R_eq_five (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 2) :
    C.x + C.R.card = 5 := by
  have h := Digraph.LocalConfiguration.k_add_x_add_card_R_eq_seven
    (G := G) C hG.1 hRootDegree
  omega

/-- The reached part of `Q` has cardinality at most `|Q|`. -/
theorem y_le_card_Q (C : G.LocalConfiguration) : y G C ≤ C.Q.card := by
  exact Finset.card_le_card Finset.inter_subset_left

/-- The represented targets fit strictly below the pivot degree. -/
theorem represented_targets_lt_degree (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hk : C.k = 2) :
    C.x + y G C + (C.z + epsilonS G C) < 2 + C.r := by
  have hRepresented :=
    BSixKThree.represented_targets_le_secondOutdegree G C hG
  have hNot : ¬G.IsSeymourVertex C.a1 := by
    intro h
    exact hNoSeymour ⟨C.a1, h⟩
  have hStrict :=
    Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
  have hDegree := Shared.outdegree_a1_eq_k_add_r G C hG
  rw [hk] at hDegree
  have hRepresented' : C.x + y G C + (C.z + epsilonS G C) ≤
      G.secondOutdegree C.a1 := by
    simpa [y, reachedQ, BSixKThree.y, BSixKThree.Y,
      Shared.card_externalTargets] using hRepresented
  omega

/-- Arcs from `H` into `Q` have capacity `x|Q|+2y`. -/
theorem H_to_Q_le (C : G.LocalConfiguration) (hk : C.k = 2) :
    edgeCount G C.H C.Q ≤ C.x * C.Q.card + 2 * y G C := by
  have hSplit : edgeCount G C.H C.Q =
      edgeCount G C.A1 C.Q + edgeCount G C.X C.Q := by
    simpa [Digraph.LocalConfiguration.H] using
      BSixKThree.edgeCount_source_union G C.A1 C.X C.Q
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hA1Reached : edgeCount G C.A1 C.Q ≤
      edgeCount G C.A1 (reachedQ G C) := by
    apply BSixKThree.edgeCount_mono_right G
    intro u hu v hvQ huv
    exact Finset.mem_inter.mpr ⟨hvQ,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨u, Finset.mem_union_left C.P hu, huv⟩⟩
  have hA1Cap := edgeCount_le_card_mul_card G C.A1 (reachedQ G C)
  have hXCap := edgeCount_le_card_mul_card G C.X C.Q
  change C.A1.card = 2 at hk
  rw [hk] at hA1Cap
  change edgeCount G C.H C.Q ≤
    C.X.card * C.Q.card + 2 * (reachedQ G C).card
  omega

/-- The lower bound on arcs entering `P`, before substituting the cardinalities
of `H`, `R`, and `Q`. -/
theorem H_degree_capacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 2) :
    8 * C.H.card ≤ edgeCount G C.H C.P +
      C.H.card.choose 2 + C.x + C.x * C.R.card +
        C.x * C.Q.card + 2 * y G C := by
  have hLower : 8 * C.H.card ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      8 * C.H.card = ∑ _u ∈ C.H, 8 := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ C.H, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hSplit := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
  have hA := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  have hQ := H_to_Q_le G C hk
  omega

/-- The outgoing-arc capacity inequality in the `r=6` branch. -/
theorem P_degree_capacity_r_six (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hr : C.r = 6) :
    48 + edgeCount G C.H C.P ≤
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) +
        6 * C.H.card + 15 := by
  have hPCard : C.P.card = 6 := hr
  have hLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  have hInternal := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hCross hInternal
  simp [Nat.choose] at hInternal
  omega

/-- The outgoing-arc capacity inequality in the `r=7` branch. -/
theorem P_degree_capacity_r_seven (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hr : C.r = 7) :
    56 + edgeCount G C.H C.P ≤
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) +
        7 * C.H.card + 21 := by
  have hPCard : C.P.card = 7 := hr
  have hLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  have hInternal := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hCross hInternal
  simp [Nat.choose] at hInternal
  omega

/-- The external-target capacity inequality for a six-vertex `P`. -/
theorem P_to_Q_external_le_r_six (C : G.LocalConfiguration)
    (hr : C.r = 6) :
    edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) ≤
      6 * (y G C + (C.z + epsilonS G C)) := by
  have hPReached : edgeCount G C.P C.Q ≤
      edgeCount G C.P (reachedQ G C) := by
    apply BSixKThree.edgeCount_mono_right G
    intro p hp v hvQ hpv
    exact Finset.mem_inter.mpr ⟨hvQ,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩⟩
  have hYCap := edgeCount_le_card_mul_card G C.P (reachedQ G C)
  have hWCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hPCard : C.P.card = 6 := hr
  rw [hPCard] at hYCap hWCap
  rw [card_externalTargets G C] at hWCap
  unfold y
  omega

/-- The external-target capacity inequality for a seven-vertex `P`. -/
theorem P_to_Q_external_le_r_seven (C : G.LocalConfiguration)
    (hr : C.r = 7) :
    edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) ≤
      7 * (y G C + (C.z + epsilonS G C)) := by
  have hPReached : edgeCount G C.P C.Q ≤
      edgeCount G C.P (reachedQ G C) := by
    apply BSixKThree.edgeCount_mono_right G
    intro p hp v hvQ hpv
    exact Finset.mem_inter.mpr ⟨hvQ,
      (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩⟩
  have hYCap := edgeCount_le_card_mul_card G C.P (reachedQ G C)
  have hWCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hPCard : C.P.card = 7 := hr
  rw [hPCard] at hYCap hWCap
  rw [card_externalTargets G C] at hWCap
  unfold y
  omega

/-- The fourteen families containing all 32 feasible parameter rows. -/
inductive ParameterFamily (C : G.LocalConfiguration) : Prop where
  | rSixXTwoRoot
      (hr : C.r = 6) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ C.z = 4) ∨
        (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3)))
  | rSixXTwoNoRoot
      (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ C.z = 5) ∨
        (y G C = 1 ∧ (C.z = 3 ∨ C.z = 4)))
  | rSixXThreeRoot
      (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2))
  | rSixXThreeNoRoot
      (hr : C.r = 6) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ C.z = 4) ∨ (y G C = 1 ∧ C.z = 3))
  | rSixXFourRoot
      (hr : C.r = 6) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ C.z = 2) ∨ (y G C = 1 ∧ C.z = 1))
  | rSixXFourNoRoot
      (hr : C.r = 6) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2))
  | rSevenXTwoRoot
      (hr : C.r = 7) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5))
  | rSevenXTwoNoRoot
      (hr : C.r = 7) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧ (C.z = 4 ∨ C.z = 5 ∨ C.z = 6))
  | rSevenXThreeRoot
      (hr : C.r = 7) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4))
  | rSevenXThreeNoRoot
      (hr : C.r = 7) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5))
  | rSevenXFourRoot
      (hr : C.r = 7) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧ (C.z = 2 ∨ C.z = 3))
  | rSevenXFourNoRoot
      (hr : C.r = 7) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4))
  | rSevenXFiveRoot
      (hr : C.r = 7) (hx : C.x = 5) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧ C.z = 2)
  | rSevenXFiveNoRoot
      (hr : C.r = 7) (hx : C.x = 5) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧ C.z = 3)

/-- Counting reduction from a graph-level counterexample to the 32 exact rows. -/
theorem parameterFamily
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) : ParameterFamily G C := by
  have hrLower : 6 ≤ C.r := by
    have hDegree := hMin C.a1
    rw [Shared.outdegree_a1_eq_k_add_r G C hG, hk] at hDegree
    omega
  have hrUpper : C.r ≤ 7 := by
    calc
      C.r = C.P.card := rfl
      _ ≤ C.B.card := Finset.card_le_card
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
      _ = 7 := hBCard
  have hxLower := two_le_x G C hG hPivot hk
  have hXR := x_add_card_R_eq_five G C hG hRootDegree hk
  have hxUpper : C.x ≤ 5 := by omega
  have hBasic := represented_targets_lt_degree G C hG hNoSeymour hk
  have hH := H_degree_capacity G C hG hMin hk
  have hHCard := H_card_eq_x_add_two G C hk
  have hQCard := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
  have hyLe := y_le_card_Q G C
  have hEpsilon := epsilonS_eq_zero_or_one G C
  rcases (show C.r = 6 ∨ C.r = 7 by omega) with hr | hr
  · have hQ : C.Q.card = 1 := by omega
    have hP := P_degree_capacity_r_six G C hG hMin hr
    have hUpper := P_to_Q_external_le_r_six G C hr
    rw [hHCard] at hH hP
    rw [hQ] at hH hyLe
    rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 ∨ C.x = 5 by omega) with
        hx | hx | hx | hx
    · have hR : C.R.card = 3 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSixXTwoNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSixXTwoRoot hr hx hRoot
        omega
    · have hR : C.R.card = 2 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSixXThreeNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSixXThreeRoot hr hx hRoot
        omega
    · have hR : C.R.card = 1 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSixXFourNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSixXFourRoot hr hx hRoot
        omega
    · have hR : C.R.card = 0 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      omega
  · have hQ : C.Q.card = 0 := by omega
    have hP := P_degree_capacity_r_seven G C hG hMin hr
    have hUpper := P_to_Q_external_le_r_seven G C hr
    rw [hHCard] at hH hP
    rw [hQ] at hH hyLe
    have hyZero : y G C = 0 := by omega
    rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 ∨ C.x = 5 by omega) with
        hx | hx | hx | hx
    · have hR : C.R.card = 3 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXTwoNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXTwoRoot hr hx hRoot
        omega
    · have hR : C.R.card = 2 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXThreeNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXThreeRoot hr hx hRoot
        omega
    · have hR : C.R.card = 1 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXFourNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXFourRoot hr hx hRoot
        omega
    · have hR : C.R.card = 0 := by omega
      rw [hx, hR] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXFiveNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXFiveRoot hr hx hRoot
        omega

end SeymourEight.BSevenKTwo
