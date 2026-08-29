import SeymourEight.Cases.BSevenKThree.Basic
import SeymourEight.Cases.BSevenKTwo.Counting

set_option linter.style.header false

/-!
# Counting reduction for the `(|B|, k) = (7, 3)` case

The graph-level inequalities in this file reduce a counterexample to 68
explicit parameter rows, grouped into eighteen families by `(r,x)` and root
status.
-/

namespace SeymourEight.BSevenKThree

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem y_eq_bSixKThreeY (C : G.LocalConfiguration) :
    y G C = BSixKThree.y G C := by
  rfl

private theorem y_eq_bSevenKTwoY (C : G.LocalConfiguration) :
    y G C = BSevenKTwo.y G C := by
  rfl

/-- The represented targets fit strictly below the pivot degree. -/
private theorem representedTargetsLtDegree
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (hk : C.k = 3) :
    C.x + y G C + (C.z + epsilonS G C) < 3 + C.r := by
  simpa [y_eq_bSixKThreeY G C] using
    BSixKThree.represented_targets_lt_degree G C hG hNoSeymour hk

/-- The lower bound on arcs entering `P` from the retained set. -/
private theorem HDegreeCapacity
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hk : C.k = 3) :
    8 * C.H.card ≤ edgeCount G C.H C.P +
      C.H.card.choose 2 + C.x + C.x * C.R.card +
        C.x * C.Q.card + 3 * y G C := by
  simpa [y_eq_bSixKThreeY G C] using
    BSixKThree.H_degree_capacity_general G C hG hMin hk

/-- The outgoing-arc capacity inequality in the `r=5` branch. -/
private theorem PDegreeCapacityRFive
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 5) :
    40 + edgeCount G C.H C.P ≤
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) +
        5 * C.H.card + 10 :=
  BSixKThree.P_degree_capacity_general G C hG hMin hr

/-- The outgoing-arc capacity inequality in the `r=6` branch. -/
private theorem PDegreeCapacityRSix
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 6) :
    48 + edgeCount G C.H C.P ≤
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) +
        6 * C.H.card + 15 :=
  BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr

/-- The outgoing-arc capacity inequality in the `r=7` branch. -/
private theorem PDegreeCapacityRSeven
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 7) :
    56 + edgeCount G C.H C.P ≤
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) +
        7 * C.H.card + 21 :=
  BSevenKTwo.P_degree_capacity_r_seven G C hG hMin hr

/-- The external-target capacity inequality in the `r=5` branch. -/
private theorem PToTargetsLeRFive (C : G.LocalConfiguration)
    (hr : C.r = 5) :
    edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) ≤
      5 * (y G C + (C.z + epsilonS G C)) := by
  simpa [y_eq_bSixKThreeY G C] using
    BSixKThree.P_to_Q_external_le G C hr

/-- The external-target capacity inequality in the `r=6` branch. -/
private theorem PToTargetsLeRSix (C : G.LocalConfiguration)
    (hr : C.r = 6) :
    edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) ≤
      6 * (y G C + (C.z + epsilonS G C)) := by
  simpa [y_eq_bSevenKTwoY G C] using
    BSevenKTwo.P_to_Q_external_le_r_six G C hr

/-- The external-target capacity inequality in the `r=7` branch. -/
private theorem PToTargetsLeRSeven (C : G.LocalConfiguration)
    (hr : C.r = 7) :
    edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) ≤
      7 * (y G C + (C.z + epsilonS G C)) := by
  simpa [y_eq_bSevenKTwoY G C] using
    BSevenKTwo.P_to_Q_external_le_r_seven G C hr

/-- The eighteen families containing all 68 feasible parameter rows. -/
inductive ParameterFamily (C : G.LocalConfiguration) : Prop where
  | rFiveXTwoRoot
      (hr : C.r = 5) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ C.z = 4) ∨ (y G C = 1 ∧ C.z = 3) ∨
        (y G C = 2 ∧ (C.z = 1 ∨ C.z = 2)))
  | rFiveXTwoNoRoot
      (hr : C.r = 5) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ C.z = 5) ∨ (y G C = 1 ∧ C.z = 4) ∨
        (y G C = 2 ∧ (C.z = 2 ∨ C.z = 3)))
  | rFiveXThreeRoot
      (hr : C.r = 5) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 1 ∧ C.z = 2) ∨
        (y G C = 2 ∧ (C.z = 0 ∨ C.z = 1)))
  | rFiveXThreeNoRoot
      (hr : C.r = 5) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 1 ∧ C.z = 3) ∨
        (y G C = 2 ∧ (C.z = 1 ∨ C.z = 2)))
  | rFiveXFourRoot
      (hr : C.r = 5) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 1 ∧ C.z = 1) ∨ (y G C = 2 ∧ C.z = 0))
  | rFiveXFourNoRoot
      (hr : C.r = 5) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 1 ∧ C.z = 2) ∨ (y G C = 2 ∧ C.z = 1))
  | rSixXTwoRoot
      (hr : C.r = 6) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
        (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4)))
  | rSixXTwoNoRoot
      (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ (C.z = 5 ∨ C.z = 6)) ∨
        (y G C = 1 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5)))
  | rSixXThreeRoot
      (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
        (y G C = 1 ∧ (C.z = 1 ∨ C.z = 2 ∨ C.z = 3)))
  | rSixXThreeNoRoot
      (hr : C.r = 6) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
        (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4)))
  | rSixXFourRoot
      (hr : C.r = 6) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
      (hyz : (y G C = 0 ∧ (C.z = 2 ∨ C.z = 3)) ∨
        (y G C = 1 ∧ (C.z = 1 ∨ C.z = 2)))
  | rSixXFourNoRoot
      (hr : C.r = 6) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
      (hyz : (y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
        (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3)))
  | rSevenXTwoRoot
      (hr : C.r = 7) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧
        (C.z = 3 ∨ C.z = 4 ∨ C.z = 5 ∨ C.z = 6))
  | rSevenXTwoNoRoot
      (hr : C.r = 7) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧
        (C.z = 4 ∨ C.z = 5 ∨ C.z = 6 ∨ C.z = 7))
  | rSevenXThreeRoot
      (hr : C.r = 7) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧
        (C.z = 2 ∨ C.z = 3 ∨ C.z = 4 ∨ C.z = 5))
  | rSevenXThreeNoRoot
      (hr : C.r = 7) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧
        (C.z = 3 ∨ C.z = 4 ∨ C.z = 5 ∨ C.z = 6))
  | rSevenXFourRoot
      (hr : C.r = 7) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
      (hyz : y G C = 0 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4))
  | rSevenXFourNoRoot
      (hr : C.r = 7) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
      (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5))

/-- Counting reduction from a graph-level counterexample to the 68 exact rows. -/
theorem parameterFamily
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) : ParameterFamily G C := by
  have hrLower : 5 ≤ C.r := by
    have hDegree := hMin C.a1
    rw [Shared.outdegree_a1_eq_k_add_r G C hG, hk] at hDegree
    omega
  have hrUpper : C.r ≤ 7 := by
    calc
      C.r = C.P.card := rfl
      _ ≤ C.B.card := Finset.card_le_card
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
      _ = 7 := hBCard
  have hxLower := BSixKThree.two_le_x G C hG hPivot hk
  have hxUpper := BSixKThree.x_le_four G C hG hRootDegree hk
  have hBasic := representedTargetsLtDegree G C hG hNoSeymour hk
  have hH := HDegreeCapacity G C hG hMin hk
  have hHCard := BSixKThree.H_card_eq_three_add_x G C hk
  have hRCard := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
  have hQCard := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
  have hyLe : y G C ≤ C.Q.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hEpsilon := epsilonS_eq_zero_or_one G C
  rcases (show C.r = 5 ∨ C.r = 6 ∨ C.r = 7 by omega) with hr | hr | hr
  · have hQ : C.Q.card = 2 := by omega
    have hP := PDegreeCapacityRFive G C hG hMin hr
    have hUpper := PToTargetsLeRFive G C hr
    rw [hHCard, hRCard, hQ] at hH
    rw [hHCard] at hP
    rw [hQ] at hyLe
    rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 by omega) with hx | hx | hx
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rFiveXTwoNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rFiveXTwoRoot hr hx hRoot
        omega
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rFiveXThreeNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rFiveXThreeRoot hr hx hRoot
        omega
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rFiveXFourNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rFiveXFourRoot hr hx hRoot
        omega
  · have hQ : C.Q.card = 1 := by omega
    have hP := PDegreeCapacityRSix G C hG hMin hr
    have hUpper := PToTargetsLeRSix G C hr
    rw [hHCard, hRCard, hQ] at hH
    rw [hHCard] at hP
    rw [hQ] at hyLe
    rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 by omega) with hx | hx | hx
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSixXTwoNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSixXTwoRoot hr hx hRoot
        omega
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSixXThreeNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSixXThreeRoot hr hx hRoot
        omega
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSixXFourNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSixXFourRoot hr hx hRoot
        omega
  · have hQ : C.Q.card = 0 := by omega
    have hP := PDegreeCapacityRSeven G C hG hMin hr
    have hUpper := PToTargetsLeRSeven G C hr
    rw [hHCard, hRCard, hQ] at hH
    rw [hHCard] at hP
    rw [hQ] at hyLe
    rcases (show C.x = 2 ∨ C.x = 3 ∨ C.x = 4 by omega) with hx | hx | hx
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXTwoNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXTwoRoot hr hx hRoot
        omega
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXThreeNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXThreeRoot hr hx hRoot
        omega
    · rw [hx] at hH
      simp only [Nat.choose] at hH
      rcases hEpsilon with hNoRoot | hRoot
      · apply ParameterFamily.rSevenXFourNoRoot hr hx hNoRoot
        omega
      · apply ParameterFamily.rSevenXFourRoot hr hx hRoot
        omega

end SeymourEight.BSevenKThree
