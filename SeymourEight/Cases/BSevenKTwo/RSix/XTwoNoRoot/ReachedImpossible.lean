import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.ReachedAssembly
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalHighPH
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroH

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem reached_three_impossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 1) (hz : C.z = 3) : False := by
  have hPCard : C.P.card = 6 := hr
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hReachedCard : (reachedQ G C).card = 1 := hy
  obtain ⟨q, hqReached⟩ :=
    Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
  have hqQ : q ∈ C.Q := (Finset.mem_inter.mp hqReached).1
  have hQ : C.Q = {q} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hQCard
    have hqw : q = w := by simpa [hw] using hqQ
    simpa [hqw] using hw
  have hAOneCard : C.A1.card = 2 := hk
  have hXCard : C.X.card = 2 := hx
  have hHCard : C.H.card = 4 := by
    rw [BSevenKTwo.H_card_eq_x_add_two G C hk, hx]
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 3 := by omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hZCard : C.Z.card = 3 := hz
  exact ReachedAssembly.reachedFour_impossible G C q hqQ hQ hG hMin
    hNoSeymour hNoRoot hPivot hk hr hx hPCard hACard hRCard hHCard hy hZCard

theorem reached_four_impossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 1) (hz : C.z = 4) : False := by
  have hPCard : C.P.card = 6 := hr
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hReachedCard : (reachedQ G C).card = 1 := hy
  obtain ⟨q, hqReached⟩ :=
    Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
  have hqQ : q ∈ C.Q := (Finset.mem_inter.mp hqReached).1
  have hQ : C.Q = {q} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hQCard
    have hqw : q = w := by simpa [hw] using hqQ
    simpa [hqw] using hw
  have hHCard : C.H.card = 4 := by
    rw [BSevenKTwo.H_card_eq_x_add_two G C hk, hx]
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 3 := by omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hZCard : C.Z.card = 4 := hz
  exact ReachedAssembly.reachedFive_impossible_of_certificates G
    Core.microCZeroNonHard_unsat Core.microCOneHighPH_unsat
    Core.microCTwoHighPH_unsat Core.microHEffectiveLowPH_zero_m0_unsat
    Core.microHEffectiveLowPH_one_range_unsat
    Core.microHEffectiveLowPH_two_range_unsat C q hqQ hQ hG hMin hNoSeymour
    hNoRoot hPivot hk hr hx hPCard hACard hRCard hHCard hy hZCard

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot
