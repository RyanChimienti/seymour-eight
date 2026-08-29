import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.ReachedBridge
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.UnreachedBridge

set_option linter.style.header false
set_option maxRecDepth 100000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.CertifiedBridge

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradictionExternal
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3)
    (hyz : (BSevenKThree.y G C = 0 ∧
        ((externalTargets G C).card = 4 ∨ (externalTargets G C).card = 5)) ∨
      (BSevenKThree.y G C = 1 ∧
        ((externalTargets G C).card = 2 ∨ (externalTargets G C).card = 3 ∨
          (externalTargets G C).card = 4))) : False := by
  have hPCard : C.P.card = 6 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hAOneCard : C.A1.card = 3 := hk
  have hXCard : C.X.card = 3 := hx
  have hRCard : C.R.card = 1 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 6 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz | hz⟩
  · exact UnreachedBridge.contradiction G C hG hMin hNoSeymour hRootDegree
      hPivot hPCard hACard hQCard hz hAOneCard hXCard hRCard hHCard
      hk hr hx hy (Or.inl rfl)
  · exact UnreachedBridge.contradiction G C hG hMin hNoSeymour hRootDegree
      hPivot hPCard hACard hQCard hz hAOneCard hXCard hRCard hHCard
      hk hr hx hy (Or.inr rfl)
  · exact ReachedBridge.contradictionTwo G C hG hMin hNoSeymour hRootDegree
      hPivot hPCard hACard hQCard hz hAOneCard hXCard hRCard hHCard
      hk hr hx hy
  · exact ReachedBridge.contradictionThreeFour G C hG hMin hNoSeymour
      hRootDegree hPivot hPCard hACard hQCard hz hAOneCard hXCard hRCard
      hHCard hk hr hx hy (Or.inl rfl)
  · exact ReachedBridge.contradictionThreeFour G C hG hMin hNoSeymour
      hRootDegree hPivot hPCard hACard hQCard hz hAOneCard hXCard hRCard
      hHCard hk hr hx hy (Or.inr rfl)

theorem contradiction
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : (BSevenKThree.y G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
      (BSevenKThree.y G C = 1 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz | hz⟩
  · exact Or.inl ⟨hy, Or.inl (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inl ⟨hy, Or.inr (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hNoRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (Or.inl (by rw [card_externalTargets, hz, hNoRoot]))⟩
  · exact Or.inr ⟨hy, Or.inr (Or.inr (by rw [card_externalTargets, hz, hNoRoot]))⟩

theorem contradictionRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : (BSevenKThree.y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
      (BSevenKThree.y G C = 1 ∧ (C.z = 1 ∨ C.z = 2 ∨ C.z = 3))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz | hz⟩
  · exact Or.inl ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inl ⟨hy, Or.inr (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (Or.inl (by rw [card_externalTargets, hz, hRoot]))⟩
  · exact Or.inr ⟨hy, Or.inr (Or.inr (by rw [card_externalTargets, hz, hRoot]))⟩

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.CertifiedBridge
