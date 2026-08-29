import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.CaseBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ProbeEasyFour
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ProbeReachedTwo
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.BroadRigidXAlphaZero
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.SatCOne
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ReducedPositiveDelta
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.NoEligibleModes
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.PositiveAlphaRange
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CompactActualC6
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.D501Positive

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CertifiedBridge

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradictionExternal
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 4)
    (hyz : (BSevenKThree.y G C = 0 ∧
        ((externalTargets G C).card = 3 ∨ (externalTargets G C).card = 4)) ∨
      (BSevenKThree.y G C = 1 ∧
        ((externalTargets G C).card = 2 ∨ (externalTargets G C).card = 3))) : False := by
  apply CaseBridge.contradiction G
  · exact Core.probeEasyFour
  · exact Core.reachedTwoDirectCore_false
  · exact ⟨Rigid.broadRigidXAlphaZero_false,
      StrongDual.reducedPositiveDelta_false,
      StrongDual.noEligibleModes_false,
      StrongDual.aRigidPositiveAlphaRange_false⟩
  · exact SatTail.satCOne_false
  · exact CompactActualTail.compactActualC6_false
  · exact D501Positive.d501Positive_false
  · exact hBound
  · exact hG
  · exact hMin
  · exact hNoSeymour
  · exact hRootDegree
  · exact hPivot
  · exact hBCard
  · exact hk
  · exact hr
  · exact hx
  · exact hyz

theorem contradiction
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : (BSevenKThree.y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
      (BSevenKThree.y G C = 1 ∧ (C.z = 2 ∨ C.z = 3))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz⟩
  · exact Or.inl ⟨hy, Or.inl (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inl ⟨hy, Or.inr (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (by rw [card_externalTargets, hz, hNoRoot])⟩

theorem contradictionRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : (BSevenKThree.y G C = 0 ∧ (C.z = 2 ∨ C.z = 3)) ∨
      (BSevenKThree.y G C = 1 ∧ (C.z = 1 ∨ C.z = 2))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz⟩
  · exact Or.inl ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inl ⟨hy, Or.inr (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (by rw [card_externalTargets, hz, hRoot])⟩

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CertifiedBridge
