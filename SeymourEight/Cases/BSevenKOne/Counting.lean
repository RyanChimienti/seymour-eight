import SeymourEight.Cases.BSevenKOne.Basic
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.FinalDefects
import SeymourEight.Shared.LocalDegree

set_option linter.style.header false

/-!
# Counting reductions for the `(|B|,k)=(7,1)` case

This file develops the edge-count inequalities which reduce the graph-level
case to its finite parameter rows.
-/

namespace SeymourEight.BSevenKOneCounting

open BSevenKOne FinalDefects RawFinalBranch Shared TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Members of `Q` reached from `A1 ∪ P`; its cardinality is the parameter `y`. -/
def reachedQ (C : G.LocalConfiguration) : Finset V :=
  C.Q ∩ G.outNeighborFinsetOf (C.A1 ∪ C.P)

def y (C : G.LocalConfiguration) : Nat :=
  (reachedQ G C).card

/-- In the `(7,1)` row, `P=B` makes `Q` empty. -/
theorem q_eq_empty (C : G.LocalConfiguration) (hPB : C.P = C.B) :
    C.Q = ∅ := by
  simp [Digraph.LocalConfiguration.Q, hPB]

/-- Consequently the reached-`Q` parameter `y` is zero. -/
theorem y_eq_zero (C : G.LocalConfiguration) (hPB : C.P = C.B) :
    y G C = 0 := by
  simp [y, reachedQ, q_eq_empty G C hPB]

/-- At `k=1`, the retained `A`-set `H=A1∪X` has cardinality `x+1`. -/
theorem h_eq_x_add_one (C : G.LocalConfiguration) (hk : C.k = 1) :
    C.h = C.x + 1 := by
  rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk]
  omega

/-- At a degree-eight root with `k=1`, `X` and `R` have total cardinality six. -/
theorem x_add_card_R_eq_six (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) :
    C.x + C.R.card = 6 := by
  exact Digraph.LocalConfiguration.x_add_card_R_eq_six_of_k_eq_one
    (G := G) C hG.1 hRootDegree hk

/--
In the `(7,1)` row, arcs from `P` to `Z` and the reached root are bounded by
the `7(z+epsilon_s)` available pairs.
-/
theorem external_edgeCount_le (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) :
    edgeCount G C.P (externalTargets G C) ≤ 7 * (C.z + epsilonS G C) := by
  calc
    edgeCount G C.P (externalTargets G C) ≤
        C.P.card * (externalTargets G C).card :=
      edgeCount_le_card_mul_card G C.P (externalTargets G C)
    _ = 7 * (C.z + epsilonS G C) := by
      rw [hPCard, card_externalTargets]

omit [Fintype V] [DecidableEq V] in
/-- An oriented graph has at most 21 internal arcs on a seven-element set. -/
theorem internal_edgeCount_le_twentyOne (S : Finset V)
    (hG : G.IsOriented) (hSCard : S.card = 7) :
    edgeCount G S S ≤ 21 := by
  classical
  have hIncident : ∀ v ∈ S,
      directCount G S v + internalInDegree G S v ≤ 6 := by
    intro v hv
    have hDisjoint := disjoint_internal_out_in G S v hG
    have hSubset := internal_incident_subset_erase G S v hG
    calc
      directCount G S v + internalInDegree G S v =
          (CertificateBridge.internalFirstNeighbors G S v ∪
            (S.filter fun u ↦ G.Adj u v)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
        rfl
      _ ≤ (S.erase v).card := Finset.card_le_card hSubset
      _ = 6 := by rw [Finset.card_erase_of_mem hv, hSCard]
  have hSumLe :
      ∑ v ∈ S, (directCount G S v + internalInDegree G S v) ≤ 42 := by
    calc
      (∑ v ∈ S, (directCount G S v + internalInDegree G S v)) ≤
          ∑ _v ∈ S, 6 := by
        apply Finset.sum_le_sum
        exact hIncident
      _ = 42 := by simp [hSCard]
  rw [Finset.sum_add_distrib, ← edgeCount,
    ← edgeCount_eq_sum_internalInDegree (G := G)] at hSumLe
  omega

/-- The lower bound on `e(H,P)` after substituting `|H|=x+1` and `x+|R|=6`. -/
theorem eight_add_choose_x_succ_le_H_to_P
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) :
    8 + (C.x + 1).choose 2 ≤ edgeCount G C.H C.P := by
  have hFive := equationFive G C hG hMin hPB
  have hHCard : C.H.card = C.x + 1 := by
    change C.h = C.x + 1
    exact h_eq_x_add_one G C hk
  have hXR := x_add_card_R_eq_six G C hG hRootDegree hk
  have hxLe : C.x ≤ 6 := by omega
  rw [hHCard] at hFive
  have hxCases : C.x = 0 ∨ C.x = 1 ∨ C.x = 2 ∨ C.x = 3 ∨
      C.x = 4 ∨ C.x = 5 ∨ C.x = 6 := by omega
  rcases hxCases with hx | hx | hx | hx | hx | hx | hx <;>
    simp [hx, Nat.choose] at hFive ⊢ <;> omega

/--
The outgoing-arc capacity inequality, written without natural-number subtraction:
`35 + e(H,P) ≤ e(P,Z∪{s}) + 7|H|`.
-/
theorem thirtyFive_add_H_to_P_le_external_add_seven_mul_h
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    35 + edgeCount G C.H C.P ≤
      edgeCount G C.P (externalTargets G C) + 7 * C.H.card := by
  have hPCard : C.P.card = 7 := BSevenKOne.r_eq_seven G C hG hMin hBCard hk
  have hDegreeSumLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_eq_local_edgeCounts G C hG hPCard hBCard
  have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  have hInternal := internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hExternal := edgeCount_externalTargets G C
  rw [hPCard] at hCross
  omega

/-- The outgoing-arc capacity inequality with `|H|=x+1` substituted. -/
theorem twentyEight_add_H_to_P_le_external_add_seven_mul_x
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    28 + edgeCount G C.H C.P ≤
      edgeCount G C.P (externalTargets G C) + 7 * C.x := by
  have hSix := thirtyFive_add_H_to_P_le_external_add_seven_mul_h
    G C hG hMin hBCard hk
  have hHCard : C.H.card = C.x + 1 := by
    change C.h = C.x + 1
    exact h_eq_x_add_one G C hk
  omega

/--
The combined lower bound, without truncated subtraction:
`36 + choose(x+1,2) ≤ e(P,Z∪{s}) + 7x`.
-/
theorem equationTwentyLower (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    36 + (C.x + 1).choose 2 ≤
      edgeCount G C.P (externalTargets G C) + 7 * C.x := by
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hFive := eight_add_choose_x_succ_le_H_to_P
    G C hG hMin hPB hRootDegree hk
  have hSix := twentyEight_add_H_to_P_le_external_add_seven_mul_x
    G C hG hMin hBCard hk
  omega

/-- The three preceding bounds combine into the main numerical capacity. -/
theorem equationTwentyCapacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    36 + (C.x + 1).choose 2 ≤
      7 * (C.x + C.z + epsilonS G C) := by
  have hLower := equationTwentyLower G C hG hMin hRootDegree hBCard hk
  have hPCard : C.P.card = 7 := BSevenKOne.r_eq_seven G C hG hMin hBCard hk
  have hUpper := external_edgeCount_le G C hPCard
  omega

/--
The represented-target and numerical-capacity bounds, together with
minimality of the pivot, leave exactly seven `(x,w)` rows, where
`w=z+epsilon_s`.
-/
theorem parameterRows (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    (C.x = 1 ∧ (C.z + epsilonS G C = 5 ∨ C.z + epsilonS G C = 6)) ∨
    (C.x = 2 ∧ (C.z + epsilonS G C = 4 ∨ C.z + epsilonS G C = 5)) ∨
    (C.x = 3 ∧ (C.z + epsilonS G C = 3 ∨ C.z + epsilonS G C = 4)) ∨
    (C.x = 4 ∧ C.z + epsilonS G C = 3) := by
  have hxOne := BSevenKOne.one_le_x G C hG hPivot hk
  have hBasic := BSevenKOne.x_add_z_add_epsilonS_le_seven
    G C hG hMin hNoSeymour hBCard hk
  have hCapacity := equationTwentyCapacity
    G C hG hMin hRootDegree hBCard hk
  have hxCases : C.x = 1 ∨ C.x = 2 ∨ C.x = 3 ∨ C.x = 4 ∨
      C.x = 5 ∨ C.x = 6 ∨ C.x = 7 := by omega
  rcases hxCases with hx | hx | hx | hx | hx | hx | hx
  · left
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hCapacity
    omega
  · right; left
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hCapacity
    omega
  · right; right; left
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hCapacity
    omega
  · right; right; right
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hCapacity
    omega
  · simp only [hx, Nat.choose] at hCapacity
    omega
  · simp only [hx, Nat.choose] at hCapacity
    omega
  · simp only [hx, Nat.choose] at hCapacity
    omega

/--
The seven `(x,w)` rows refined by the two possible values of `epsilon_s` give
the fourteen concrete `(x,z,epsilon_s)` rows used by the final case dispatch.
-/
theorem concreteParameterRows (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    (C.x = 1 ∧
      ((epsilonS G C = 0 ∧ (C.z = 5 ∨ C.z = 6)) ∨
        (epsilonS G C = 1 ∧ (C.z = 4 ∨ C.z = 5)))) ∨
    (C.x = 2 ∧
      ((epsilonS G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
        (epsilonS G C = 1 ∧ (C.z = 3 ∨ C.z = 4)))) ∨
    (C.x = 3 ∧
      ((epsilonS G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
        (epsilonS G C = 1 ∧ (C.z = 2 ∨ C.z = 3)))) ∨
    (C.x = 4 ∧
      ((epsilonS G C = 0 ∧ C.z = 3) ∨
        (epsilonS G C = 1 ∧ C.z = 2))) := by
  have hRows := parameterRows G C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk
  have hEpsilon := Shared.epsilonS_eq_zero_or_one G C
  rcases hRows with h1 | h2 | h3 | h4 <;>
    rcases hEpsilon with hZero | hOne <;> omega

end SeymourEight.BSevenKOneCounting
