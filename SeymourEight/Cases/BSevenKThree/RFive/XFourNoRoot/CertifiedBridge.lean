import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.CaseBridge
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.ProbeOne
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.AnonCut

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.CertifiedBridge

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradictionExternal
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 4)
    (hyz : (BSevenKThree.y G C = 1 ∧ (externalTargets G C).card = 2) ∨
      (BSevenKThree.y G C = 2 ∧ (externalTargets G C).card = 1)) : False := by
  exact CaseBridge.contradiction G Core.perfectDirectCore_false Core.anonCutCounterexample_false
    hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hyz

theorem contradiction
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : (BSevenKThree.y G C = 1 ∧ C.z = 2) ∨
      (BSevenKThree.y G C = 2 ∧ C.z = 1)) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · exact Or.inl ⟨hy, by rw [card_externalTargets, hz, hNoRoot]⟩
  · exact Or.inr ⟨hy, by rw [card_externalTargets, hz, hNoRoot]⟩

theorem contradictionRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : (BSevenKThree.y G C = 1 ∧ C.z = 1) ∨
      (BSevenKThree.y G C = 2 ∧ C.z = 0)) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · exact Or.inl ⟨hy, by rw [card_externalTargets, hz, hRoot]⟩
  · exact Or.inr ⟨hy, by rw [card_externalTargets, hz, hRoot]⟩

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.CertifiedBridge
