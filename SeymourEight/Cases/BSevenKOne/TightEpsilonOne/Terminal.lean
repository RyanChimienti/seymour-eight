import SeymourEight.Cases.BSevenKOne.Counting

set_option linter.style.header false

/-!
# Graph-level terminal row of the `(|B|,k)=(7,1)` case

This file connects the defect parameters of the tight `(x,z,epsilon_s)=(4,2,1)`
row to the already verified terminal contradiction.
-/

namespace SeymourEight.BSevenKOneTerminal

open BSevenKOne BSevenKOneCounting FinalDefects RawFinalBranch Shared
  TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Missing capacity among the 21 possible arcs from `P` to `Z∪{s}`. -/
def mDefect (C : G.LocalConfiguration) : Nat :=
  21 - edgeCount G C.P (externalTargets G C)

/-- Missing capacity among the 17 possible arcs from `P` to `H`. -/
def alphaDefect (C : G.LocalConfiguration) : Nat :=
  17 - edgeCount G C.P C.H

/-- Missing pairs among the 21 possible oriented pairs inside `P`. -/
def betaDefect (C : G.LocalConfiguration) : Nat :=
  21 - edgeCount G C.P C.P

/-- In the tight `(4,2,1)` row, the external arc count is at most 21. -/
theorem external_edgeCount_le_twentyOne (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    edgeCount G C.P (externalTargets G C) ≤ 21 := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hUpper := external_edgeCount_le G C hPCard
  omega

/-- The retained-set degree bound gives `e(H,P)≥18` when `x=4`. -/
theorem eighteen_le_H_to_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1) (hx : C.x = 4) :
    18 ≤ edgeCount G C.H C.P := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hFive := eight_add_choose_x_succ_le_H_to_P
    G C hG hMin hPB hRootDegree hk
  simpa only [hx, Nat.choose] using hFive

/-- Hence the reverse capacity satisfies `e(P,H)≤17`. -/
theorem P_to_H_le_seventeen (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1) (hx : C.x = 4) :
    edgeCount G C.P C.H ≤ 17 := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  have hLower := eighteen_le_H_to_P G C hG hMin hRootDegree hBCard hk hx
  rw [hPCard, hHCard] at hCross
  omega

/-- The external defect definition is additive rather than truncated in this row. -/
theorem external_add_mDefect_eq_twentyOne (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    edgeCount G C.P (externalTargets G C) + mDefect G C = 21 := by
  have hLe := external_edgeCount_le_twentyOne
    G C hG hMin hBCard hk hz hEpsilon
  unfold mDefect
  omega

/-- The `alpha` defect definition is additive in the tight `x=4` row. -/
theorem P_to_H_add_alphaDefect_eq_seventeen (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1) (hx : C.x = 4) :
    edgeCount G C.P C.H + alphaDefect G C = 17 := by
  have hLe := P_to_H_le_seventeen G C hG hMin hRootDegree hBCard hk hx
  unfold alphaDefect
  omega

/-- The `beta` defect definition is additive on the seven-element set `P`. -/
theorem P_internal_add_betaDefect_eq_twentyOne (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    edgeCount G C.P C.P + betaDefect G C = 21 := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hLe := internal_edgeCount_le_twentyOne G C.P hG hPCard
  unfold betaDefect
  omega

/--
The degree-excess identity holds throughout the tight
`(x,z,epsilon_s)=(4,2,1)` row; full `P→Z` capacity is not needed.
-/
theorem degreeExcessEquation (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    (∑ p ∈ C.P, (G.outdegree p - 8)) + mDefect G C +
      alphaDefect G C + betaDefect G C = 3 := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hAccounting := FinalDefects.degreeSum_eq_local_edgeCounts
    G C hG hPCard hBCard
  have hExternalSplit := edgeCount_externalTargets G C
  have hMissing := external_add_mDefect_eq_twentyOne
    G C hG hMin hBCard hk hz hEpsilon
  have hAlpha := P_to_H_add_alphaDefect_eq_seventeen
    G C hG hMin hRootDegree hBCard hk hx
  have hBeta := P_internal_add_betaDefect_eq_twentyOne
    G C hG hMin hBCard hk
  have hDegreeSplit :
      ∑ p ∈ C.P, G.outdegree p =
        56 + ∑ p ∈ C.P, (G.outdegree p - 8) := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpMin := hMin p
        omega
      _ = 56 + ∑ p ∈ C.P, (G.outdegree p - 8) := by
        rw [Finset.sum_add_distrib]
        simp [hPCard]
  omega

/-- The external defect in the tight `(4,2,1)` row is at most three. -/
theorem mDefect_le_three (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    mDefect G C ≤ 3 := by
  have hEquation := degreeExcessEquation G C hG hMin hRootDegree
    hBCard hk hx hz hEpsilon
  omega

/-- Exhaustive external-defect split for the tight `(4,2,1)` row. -/
theorem mDefect_cases (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    mDefect G C = 0 ∨ mDefect G C = 1 ∨
      mDefect G C = 2 ∨ mDefect G C = 3 := by
  have hLe := mDefect_le_three G C hG hMin hRootDegree
    hBCard hk hx hz hEpsilon
  omega

/--
The degree-excess identity forces at least `4+m` members of `P` to have exact
outdegree eight.  This is the degree-eight tail used by the deletion
certificates.
-/
theorem four_add_mDefect_le_degreeEight_card (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    4 + mDefect G C ≤
      (C.P.filter fun p ↦ G.outdegree p = 8).card := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hEquation := degreeExcessEquation G C hG hMin hRootDegree
    hBCard hk hx hz hEpsilon
  have hBadLeExcess :
      (C.P.filter fun p ↦ G.outdegree p ≠ 8).card ≤
        ∑ p ∈ C.P, (G.outdegree p - 8) := by
    calc
      (C.P.filter fun p ↦ G.outdegree p ≠ 8).card =
          ∑ _p ∈ C.P.filter (fun p ↦ G.outdegree p ≠ 8), 1 := by simp
      _ ≤ ∑ p ∈ C.P.filter (fun p ↦ G.outdegree p ≠ 8),
          (G.outdegree p - 8) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpNe := (Finset.mem_filter.mp hp).2
        have hpMin := hMin p
        omega
      _ ≤ ∑ p ∈ C.P, (G.outdegree p - 8) := by
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hPartition :
      (C.P.filter fun p ↦ G.outdegree p = 8).card +
        (C.P.filter fun p ↦ G.outdegree p ≠ 8).card = 7 := by
    simpa [hPCard] using Finset.card_filter_add_card_filter_not
      (s := C.P) (fun p ↦ G.outdegree p = 8)
  omega

/-- Choose an explicit `4+m`-element exact-degree-eight tail inside `P`. -/
theorem exists_degreeEightTail (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    ∃ T : Finset V, T ⊆ C.P ∧ T.card = 4 + mDefect G C ∧
      ∀ p ∈ T, G.outdegree p = 8 := by
  have hCard := four_add_mDefect_le_degreeEight_card G C hG hMin
    hRootDegree hBCard hk hx hz hEpsilon
  obtain ⟨T, hTExact, hTCard⟩ := Finset.exists_subset_card_eq hCard
  refine ⟨T, hTExact.trans (Finset.filter_subset _ _), hTCard, ?_⟩
  intro p hp
  exact (Finset.mem_filter.mp (hTExact hp)).2

/--
Package the degree-eight tail together with every one-arc deletion expansion
that follows from the assumed degree-seven theorem.
-/
theorem exists_degreeEightDeletionTail
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) :
    ∃ T : Finset V, T ⊆ C.P ∧ T.card = 4 + mDefect G C ∧
      (∀ p ∈ T, G.outdegree p = 8) ∧
      ∀ p ∈ T, ∀ u, G.Adj p u →
        7 ≤ (G.outNeighborFinsetOf (G.outNeighborFinset p |>.erase u) \
          ((G.outNeighborFinset p |>.erase u) ∪ {p})).card := by
  obtain ⟨T, hTP, hTCard, hTDegree⟩ :=
    exists_degreeEightTail G C hG hMin hRootDegree hBCard hk hx hz hEpsilon
  refine ⟨T, hTP, hTCard, hTDegree, ?_⟩
  intro p hp u hpu
  exact Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour
    (hTDegree p hp) hpu

/--
When the external defect is one, either the unique missing arc targets the
root, or it targets one of the two vertices of `Z`.
-/
theorem one_defect_target_split (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hz : C.z = 2) (hEpsilon : epsilonS G C = 1)
    (hm : mDefect G C = 1) :
    (edgeCount G C.P C.Z = 14 ∧
      ∑ p ∈ C.P, epsilonAt G p C.s = 6) ∨
    (edgeCount G C.P C.Z = 13 ∧
      ∑ p ∈ C.P, epsilonAt G p C.s = 7) := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hExternalSplit := edgeCount_externalTargets G C
  have hMissing := external_add_mDefect_eq_twentyOne
    G C hG hMin hBCard hk hz hEpsilon
  have hZUpper := edgeCount_le_card_mul_card G C.P C.Z
  have hRootUpper := edgeCount_le_card_mul_card G C.P {C.s}
  have hRootCount := Shared.edgeCount_singleton G C.P C.s
  change C.Z.card = 2 at hz
  rw [hPCard, hz] at hZUpper
  simp only [Finset.card_singleton, hPCard, Nat.mul_one] at hRootUpper
  rw [hRootCount] at hRootUpper
  have hZCases : edgeCount G C.P C.Z = 13 ∨
      edgeCount G C.P C.Z = 14 := by
    omega
  rcases hZCases with hThirteen | hFourteen
  · right
    constructor <;> omega
  · left
    constructor <;> omega

/--
The graph-level tight row constructs the abstract defect package used by the
terminal certificate layer, provided the full `P→Z` capacity is present.
-/
theorem toFinalTightDefects (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14) :
    FinalTightDefects G C (mDefect G C) (alphaDefect G C) (betaDefect G C) := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hExternalSplit := edgeCount_externalTargets G C
  have hMissing := external_add_mDefect_eq_twentyOne
    G C hG hMin hBCard hk hz hEpsilon
  refine {
    oriented := hG
    minOutDegreeEight := hMin
    noSeymour := fun v hv ↦ hNoSeymour ⟨v, hv⟩
    bCard := hBCard
    pCard := hPCard
    zCard := hz
    pToZCount := hPToZ
    missingEquation := ?_
    alphaEquation := P_to_H_add_alphaDefect_eq_seventeen
      G C hG hMin hRootDegree hBCard hk hx
    betaEquation := P_internal_add_betaDefect_eq_twentyOne
      G C hG hMin hBCard hk
  }
  omega

/--
Visible graph-level closure of the hand/certificate-checked terminal row:
`(x,z,epsilon_s,m,alpha,beta)=(4,2,1,1,2,0)` is impossible.
-/
theorem terminal_one_two_zero_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : mDefect G C = 1) (hAlpha : alphaDefect G C = 2)
    (hBeta : betaDefect G C = 0) : False := by
  let D := toFinalTightDefects G C hG hMin hNoSeymour hRootDegree
    hBCard hk hx hz hEpsilon hPToZ
  exact FinalTightDefects.impossible_of_one_two_zero (G := G) D hm hAlpha hBeta

end SeymourEight.BSevenKOneTerminal
