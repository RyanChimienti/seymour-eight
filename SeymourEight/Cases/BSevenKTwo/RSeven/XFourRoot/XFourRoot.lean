import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.BroadFourLowAssembly
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.ZThreeMthreeAssembly

set_option linter.style.header false

/-!
# The rooted `r = 7`, `x = 4` family

The reached root is combined with `Z` into `externalTargets`.  The two rooted
rows therefore have the same external widths as the no-root `z = 3` and
`z = 4` rows and reuse their finite certificates.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot

open Shared
open XFourNoRoot.RepeatedSharedOmissionBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem zThree_defect_le_three
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 2) :
    21 - edgeCount G C.P (externalTargets G C) ≤ 3 := by
  have hPB : C.P = C.B := p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : (externalTargets G C).card = 3 := by
    rw [card_externalTargets G C, hz, hRoot]
  have hHP : 25 ≤ edgeCount G C.H C.P :=
    BroadFourBridge.twentyFive_le_H_to_P G C hG hMin hRootDegree hk hx hy hPB
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHLe : edgeCount G C.P C.H ≤ 17 := by omega
  have hPPLe : edgeCount G C.P C.P ≤ 21 := by
    have hInternal := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at hInternal
    norm_num [Nat.choose] at hInternal
    exact hInternal
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternal := edgeCount_externalTargets G C
  rw [← hExternal] at hAccounting
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hPZLe : edgeCount G C.P (externalTargets G C) ≤ 21 := by
    exact (edgeCount_le_card_mul_card G C.P (externalTargets G C)).trans_eq (by
      rw [hPCard, hZCard])
  omega

theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : BSevenKTwo.y G C = 0 ∧ (C.z = 2 ∨ C.z = 3)) : False := by
  rcases hyz with ⟨hy, hz | hz⟩
  · have hDefectLe := zThree_defect_le_three G C hG hMin hRootDegree
      hBCard hk hr hx hRoot hy hz
    by_cases hLow : 21 - edgeCount G C.P (externalTargets G C) ≤ 1
    · exact ZThreeLowBridge.zThree_lowDefect_impossible G C hG hMin
        hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hy hz hLow
    by_cases hTwo : 21 - edgeCount G C.P (externalTargets G C) = 2
    · exact ZThreeMtwoBridge.zThree_defectTwo_impossible G C hG hMin
        hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hy hz hTwo
    · have hThree : 21 - edgeCount G C.P (externalTargets G C) = 3 := by omega
      exact ZThreeMthreeBridge.zThree_defectThree_impossible G hBound C hG hMin
        hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hy hz hThree
  · exact BroadFourLowBridge.zFour_impossible G C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hy hz

end SeymourEight.BSevenKTwo.RSeven.XFourRoot
