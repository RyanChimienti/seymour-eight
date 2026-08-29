import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.HardBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.Three
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.Four
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.FiveUnreached
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.Six

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.CertifiedBridge

open Shared Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradictionExternal
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 2)
    (hyz : (BSevenKThree.y G C = 0 ∧
        ((externalTargets G C).card = 5 ∨ (externalTargets G C).card = 6)) ∨
      (BSevenKThree.y G C = 1 ∧
        ((externalTargets G C).card = 3 ∨ (externalTargets G C).card = 4 ∨
          (externalTargets G C).card = 5))) : False := by
  have hPCard : C.P.card = 6 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hAOneCard : C.A1.card = 3 := hk
  have hXCard : C.X.card = 2 := hx
  have hRCard : C.R.card = 2 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz | hz⟩
  · let L := labels G 5 C hPCard hACard hQCard hz hAOneCard hXCard hRCard
    exact EasyBridge.contradiction G false Core.five_unreached_unsat C L hG hMin
      hNoSeymour hPivot hk hr (by omega) (by omega) (by simpa using hy)
  · let L := labels G 6 C hPCard hACard hQCard hz hAOneCard hXCard hRCard
    exact EasyBridge.contradiction G false Core.six_unsat C L hG hMin hNoSeymour
      hPivot hk hr (by omega) (by omega)
      (by simpa using hy)
  · let L := labels G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard
    exact EasyBridge.contradiction G true Core.three_unsat C L hG hMin hNoSeymour
      hPivot hk hr (by omega) (by omega)
      (by simpa using hy)
  · let L := labels G 4 C hPCard hACard hQCard hz hAOneCard hXCard hRCard
    exact EasyBridge.contradiction G true Core.four_unsat C L hG hMin hNoSeymour
      hPivot hk hr (by omega) (by omega)
      (by simpa using hy)
  · let L := labels G 5 C hPCard hACard hQCard hz hAOneCard hXCard hRCard
    exact HardBridge.contradiction G C L hG hMin hNoSeymour hPivot hk hr hx hy

theorem contradiction
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hyz : (BSevenKThree.y G C = 0 ∧ (C.z = 5 ∨ C.z = 6)) ∨
      (BSevenKThree.y G C = 1 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5))) : False := by
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
    (hr : C.r = 6) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : (BSevenKThree.y G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
      (BSevenKThree.y G C = 1 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4))) : False := by
  apply contradictionExternal G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz | hz⟩
  · exact Or.inl ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inl ⟨hy, Or.inr (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inl (by rw [card_externalTargets, hz, hRoot])⟩
  · exact Or.inr ⟨hy, Or.inr (Or.inl (by rw [card_externalTargets, hz, hRoot]))⟩
  · exact Or.inr ⟨hy, Or.inr (Or.inr (by rw [card_externalTargets, hz, hRoot]))⟩

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.CertifiedBridge
