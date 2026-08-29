import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.CommonBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.SelectedAnonBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.PerfectCountsBridge

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.CaseBridge

open Shared Labels Encoding Core CommonBridge SelectedAnonBridge Assembly
  PerfectCountsBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option linter.flexible false in
theorem contradiction
    (hOne : ∀ arc pToZ : Nat → Nat → Bool,
      perfectDirectCore arc pToZ = false)
    (hCut : ∀ arc pToZ : Nat → Nat → Bool,
      anonCutCounterexample arc pToZ = false)
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 5)
    (hx : C.x = 4)
    (hyz : (BSevenKThree.y G C = 1 ∧ (externalTargets G C).card = 2) ∨
      (BSevenKThree.y G C = 2 ∧ (externalTargets G C).card = 1)) : False := by
  have hPCard : C.P.card = 5 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hQCard : C.Q.card = 2 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hA1Card : C.A1.card = 3 := hk
  have hXCard : C.X.card = 4 := hx
  have hRCard : C.R.card = 0 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 7 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · let L := canonicalLabels G 2 C hPCard hACard hQCard hz hA1Card
      hXCard hRCard
    have hCommon := commonCore_true G hBound C L hG hMin hNoSeymour hPivot
      hHCard hA1Card hXCard hRCard hk hr (Or.inl rfl) hy (by omega) (by omega)
      (canonicalLabels_p_order G 2 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_aOne_order G 2 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_x_order G 2 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_q_order G 2 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_z_order G 2 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
    have hCounts := perfect_counts G C L hG hMin hHCard hXCard hRCard
      hk hr hy
    have hDirect : perfectDirectCore (graphArc G L) (graphPToZ G L) = true := by
      simp only [commonCore, perfectDirectCore, Bool.and_eq_true] at hCommon ⊢
      aesop
    rw [hOne (graphArc G L) (graphPToZ G L)] at hDirect
    contradiction
  · let L := canonicalLabels G 1 C hPCard hACard hQCard hz hA1Card
      hXCard hRCard
    have hResidual := selectedResidualCore_true G C L hG hMin hNoSeymour
      hPivot hHCard hA1Card hXCard hk hr hy
      (canonicalLabels_p_order G 1 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_aOne_order G 1 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_x_order G 1 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
      (canonicalLabels_q_order G 1 C hPCard hACard hQCard hz hA1Card hXCard hRCard)
    have hLowerBool :
        (4 : BitVec 8).ule
          (etaH (graphArc G L) +
            externalMissing 1 (graphArc G L) (graphPToZ G L) +
            hQDefect 2 (graphArc G L)) = true := by
      have hNoCounter := hCut (graphArc G L) (graphPToZ G L)
      simp [anonCutCounterexample, hResidual] at hNoCounter
      exact hNoCounter
    have hLower : 4 ≤
        (etaH (graphArc G L) +
          externalMissing 1 (graphArc G L) (graphPToZ G L) +
          hQDefect 2 (graphArc G L)).toNat := by
      have hFour : (4 : BitVec 8).toNat = 4 := by decide
      simpa only [BitVec.ule_eq_decide, decide_eq_true_eq, hFour] using hLowerBool
    have hUpper := selected_aggregate_upper G C L hG hMin hHCard hx
      hRCard hy
    omega

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.CaseBridge
