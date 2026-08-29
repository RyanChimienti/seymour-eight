import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RawFinalBranch
import SeymourEight.Shared.LocalDegree

set_option linter.style.header false

/-!
# Defect arithmetic for the final tight row

This file derives the degree-excess identity from the local set definitions
and specializes it at `(m, alpha, beta) = (1, 2, 0)`.
-/

namespace SeymourEight.FinalDefects

open FinalBranch RawFinalBranch Shared TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Equal seven-element sets are equal when `P ⊆ B`. -/
theorem p_eq_B_of_cards (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hBCard : C.B.card = 7) :
    C.P = C.B := by
  apply Finset.eq_of_subset_of_card_le
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  omega

/-- Exact accounting specialized to the equal seven-element row. -/
theorem degreeSum_eq_local_edgeCounts (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 7) (hBCard : C.B.card = 7) :
    ∑ p ∈ C.P, G.outdegree p =
      edgeCount G C.P C.Z + (∑ p ∈ C.P, epsilonAt G p C.s) +
        edgeCount G C.P C.H + edgeCount G C.P C.P := by
  exact Shared.degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG
    (p_eq_B_of_cards (G := G) C hPCard hBCard)

/--
The additive defect data after the computational reduction to
`(x,z)=(4,2)` and a full `P → Z` row.  Writing the definitions additively
avoids truncated natural-number subtraction.
-/
structure FinalTightDefects (C : G.LocalConfiguration)
    (m alpha beta : Nat) : Prop where
  oriented : G.IsOriented
  minOutDegreeEight : ∀ v, 8 ≤ G.outdegree v
  noSeymour : ∀ v, ¬G.IsSeymourVertex v
  bCard : C.B.card = 7
  pCard : C.P.card = 7
  zCard : C.Z.card = 2
  pToZCount : edgeCount G C.P C.Z = 14
  missingEquation :
    edgeCount G C.P C.Z + (∑ p ∈ C.P, epsilonAt G p C.s) + m = 21
  alphaEquation : edgeCount G C.P C.H + alpha = 17
  betaEquation : edgeCount G C.P C.P + beta = 21

namespace FinalTightDefects

variable {C : G.LocalConfiguration} {m alpha beta : Nat}
    (D : FinalTightDefects G C m alpha beta)

include D in
/-- The degree-excess identity for the `(x,z)=(4,2)` row. -/
theorem degreeExcessEquation :
    (∑ p ∈ C.P, (G.outdegree p - 8)) + m + alpha + beta = 3 := by
  have hAccounting := degreeSum_eq_local_edgeCounts G C D.oriented D.pCard D.bCard
  have hMissing := D.missingEquation
  have hAlpha := D.alphaEquation
  have hBeta := D.betaEquation
  have hDegreeSplit :
      ∑ p ∈ C.P, G.outdegree p =
        56 + ∑ p ∈ C.P, (G.outdegree p - 8) := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpMin := D.minOutDegreeEight p
        omega
      _ = 56 + ∑ p ∈ C.P, (G.outdegree p - 8) := by
        rw [Finset.sum_add_distrib]
        simp [D.pCard]
  omega

include D in
/-- The terminal parameter values recover the raw edge-count package. -/
theorem toRawFinalBranch
    (hm : m = 1) (hAlpha : alpha = 2) (hBeta : beta = 0) :
    AlphaBetaTwoZeroCounts G C := by
  have hExcess := degreeExcessEquation (G := G) D
  have hPZ := D.pToZCount
  have hMissing := D.missingEquation
  have hAlphaEq := D.alphaEquation
  have hBetaEq := D.betaEquation
  have hRoot : ∑ p ∈ C.P, epsilonAt G p C.s = 6 := by omega
  have hPH : edgeCount G C.P C.H = 15 := by omega
  have hPP : edgeCount G C.P C.P = 21 := by omega
  refine {
    oriented := D.oriented
    minOutDegreeEight := D.minOutDegreeEight
    noSeymour := D.noSeymour
    pCard := D.pCard
    zCard := D.zCard
    pToZCount := D.pToZCount
    rootArcCount := hRoot
    pToHCount := hPH
    pInternalCount := hPP
    pDegreeExcess := ?_
  }
  omega

include D in
/-- The terminal defect row `(m, alpha, beta)=(1,2,0)` is impossible. -/
theorem impossible_of_one_two_zero
    (hm : m = 1) (hAlpha : alpha = 2) (hBeta : beta = 0) : False :=
  AlphaBetaTwoZeroCounts.impossible (G := G)
    (toRawFinalBranch (G := G) D hm hAlpha hBeta)

end FinalTightDefects

end SeymourEight.FinalDefects
