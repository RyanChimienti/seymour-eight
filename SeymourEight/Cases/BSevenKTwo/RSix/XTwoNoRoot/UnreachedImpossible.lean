import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.GraphBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.UnreachedHand

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The no-root, unreached row `(r,x,y,z)=(6,2,0,5)` is impossible by a
direct second-neighborhood count at a distinguished `A₁` vertex. -/
theorem unreached_impossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (_hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 5) : False := by
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  obtain ⟨q, hqQ⟩ := Finset.card_pos.mp (by omega : 0 < C.Q.card)
  have hQ : C.Q = {q} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hQCard
    have hqw : q = w := by simpa [hw] using hqQ
    simpa [hqw] using hw
  have hDist := GraphBridge.exists_distinguished_aOne G C hG hPivot hk hx
  exact HandScratch.unreached_five_false_of_distinguished G C q hqQ hQ hG
    hMin hNoSeymour hPivot hk hr hx hy hNoRoot hz hDist

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot
