import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.UnreachedHand

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoRoot

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem unreached_impossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (_hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 4) : False := by
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  obtain ⟨q, hqQ⟩ := Finset.card_pos.mp (by omega : 0 < C.Q.card)
  have hQ : C.Q = {q} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hQCard
    have hqw : q = w := by simpa [hw] using hqQ
    simpa [hqw] using hw
  have hExternalCard : (externalTargets G C).card = 5 := by
    rw [card_externalTargets G C, hz, hRoot]
  have hDist := XTwoNoRoot.GraphBridge.exists_distinguished_aOne
    G C hG hPivot hk hx
  exact Hand.unreached_false_of_distinguished G C q hqQ hQ hG hMin
    hNoSeymour hPivot hk hr hx hy hExternalCard hDist

end SeymourEight.BSevenKTwo.RSix.XTwoRoot
