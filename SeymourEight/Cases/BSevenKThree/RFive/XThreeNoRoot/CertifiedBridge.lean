import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.CommonBridge
import SeymourEight.Certificates.BSevenKThree.RFive.XThree.AllCases

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.CertifiedBridge

open Shared Labels Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradictionAt {yValue zCount : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hr : C.r = 5)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 2) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hyValue : BSevenKThree.y G C = yValue)
    (hyz : (yValue = 1 ∧ zCount = 3) ∨
      (yValue = 2 ∧ (zCount = 1 ∨ zCount = 2)))
    (hUnsat : ∀ bits : Encoding, core yValue zCount bits = false) : False := by
  let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
    hA1Card hXCard hRCard
  have hPOrder := canonicalLabels_p_order G zCount C hPCard hACard hQCard
    hZCard hA1Card hXCard hRCard
  have hAOrder := canonicalLabels_aOne_order G zCount C hPCard hACard hQCard
    hZCard hA1Card hXCard hRCard
  have hXOrder := canonicalLabels_x_order G zCount C hPCard hACard hQCard
    hZCard hA1Card hXCard hRCard
  have hQOrder := canonicalLabels_q_order G zCount C hPCard hACard hQCard
    hZCard hA1Card hXCard hRCard
  have hZOrder := canonicalLabels_z_order G zCount C hPCard hACard hQCard
    hZCard hA1Card hXCard hRCard
  have hCore := CommonBridge.core_true G hBound C L hG hMin hNoSeymour hPivot
    hHCard hA1Card hXCard hk hr hyValue hyz hPOrder hAOrder hXOrder hQOrder
    hZOrder
  have hCore' : core yValue zCount (GraphFacts.graphBits G L) = true := by
    simpa [core] using hCore
  rw [hUnsat (GraphFacts.graphBits G L)] at hCore'
  exact Bool.false_ne_true hCore'

theorem contradictionExternal
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 3)
    (hyz : (BSevenKThree.y G C = 1 ∧ (externalTargets G C).card = 3) ∨
      (BSevenKThree.y G C = 2 ∧
        ((externalTargets G C).card = 1 ∨
          (externalTargets G C).card = 2))) : False := by
  have hPCard : C.P.card = 5 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hQCard : C.Q.card = 2 := by
    have hBQ := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hA1Card : C.A1.card = 3 := hk
  have hXCard : C.X.card = 3 := hx
  have hRCard : C.R.card = 1 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 6 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz | hz⟩
  · exact contradictionAt G hBound C hG hMin hNoSeymour hPivot hk hr hPCard
      hACard hQCard hz hA1Card hXCard hRCard hHCard hy (Or.inl ⟨rfl, rfl⟩)
      Core.one_three_unsat
  · exact contradictionAt G hBound C hG hMin hNoSeymour hPivot hk hr hPCard
      hACard hQCard hz hA1Card hXCard hRCard hHCard hy
      (Or.inr ⟨rfl, Or.inl rfl⟩) Core.two_one_unsat
  · exact contradictionAt G hBound C hG hMin hNoSeymour hPivot hk hr hPCard
      hACard hQCard hz hA1Card hXCard hRCard hHCard hy
      (Or.inr ⟨rfl, Or.inr rfl⟩) Core.two_two_unsat

theorem contradiction
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : (BSevenKThree.y G C = 1 ∧ C.z = 3) ∨
      (BSevenKThree.y G C = 2 ∧ (C.z = 1 ∨ C.z = 2))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz | hz⟩
  · exact Or.inl ⟨hy, by rw [card_externalTargets, hz, hNoRoot]⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (by rw [card_externalTargets, hz, hNoRoot])⟩

theorem contradictionRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : (BSevenKThree.y G C = 1 ∧ C.z = 2) ∨
      (BSevenKThree.y G C = 2 ∧ (C.z = 0 ∨ C.z = 1))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz | hz⟩
  · exact Or.inl ⟨hy, by rw [card_externalTargets, hz, hRoot]⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (by rw [card_externalTargets, hz, hRoot])⟩

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.CertifiedBridge
