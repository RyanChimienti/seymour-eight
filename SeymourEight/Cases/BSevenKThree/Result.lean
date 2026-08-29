import SeymourEight.Cases.BSevenKThree.Counting
import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.ThreeBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.FourBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.FiveBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.ThreeBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.FourBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.FiveBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.SixBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.FourBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.FiveBridge
import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.HighBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.CertifiedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.CertifiedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.CertifiedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XTwoNoRoot.CertifiedBridge
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.CertifiedBridge
import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.CertifiedBridge

set_option linter.style.header false

/-!
# Assembly of the `(|B|, k) = (7, 3)` case

The graph-level counting reduction in `Counting` produces 68 exact parameter
rows.  They are grouped here into eighteen families by `(r,x)` and root status
and discharged by certified graph arguments.
-/

namespace SeymourEight.BSevenKThree

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! The following eighteen declarations state the exhaustive graph families. -/

/-- The four rooted `r=5`, `x=2` rows. -/
theorem rFiveXTwoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 5) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 4) ∨ (y G C = 1 ∧ C.z = 3) ∨
      (y G C = 2 ∧ (C.z = 1 ∨ C.z = 2))) : False := by
  exact RFive.XTwoNoRoot.CertifiedBridge.contradictionRoot G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hyz

/-- The four no-root `r=5`, `x=2` rows. -/
theorem rFiveXTwoNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 5) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ C.z = 5) ∨ (y G C = 1 ∧ C.z = 4) ∨
      (y G C = 2 ∧ (C.z = 2 ∨ C.z = 3))) : False := by
  exact RFive.XTwoNoRoot.CertifiedBridge.contradiction G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hyz

/-- The three rooted `r=5`, `x=3` rows. -/
theorem rFiveXThreeRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 5) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 1 ∧ C.z = 2) ∨
      (y G C = 2 ∧ (C.z = 0 ∨ C.z = 1))) : False := by
  exact RFive.XThreeNoRoot.CertifiedBridge.contradictionRoot G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hyz

/-- The three no-root `r=5`, `x=3` rows. -/
theorem rFiveXThreeNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 5) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 1 ∧ C.z = 3) ∨
      (y G C = 2 ∧ (C.z = 1 ∨ C.z = 2))) : False := by
  exact RFive.XThreeNoRoot.CertifiedBridge.contradiction G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hyz

/-- The two rooted `r=5`, `x=4` rows. -/
theorem rFiveXFourRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 5) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 1 ∧ C.z = 1) ∨ (y G C = 2 ∧ C.z = 0)) : False := by
  exact RFive.XFourNoRoot.CertifiedBridge.contradictionRoot G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hyz

/-- The two no-root `r=5`, `x=4` rows. -/
theorem rFiveXFourNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 5) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 1 ∧ C.z = 2) ∨ (y G C = 2 ∧ C.z = 1)) : False := by
  exact RFive.XFourNoRoot.CertifiedBridge.contradiction G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hyz

/-- The five rooted `r=6`, `x=2` rows. -/
theorem rSixXTwoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
      (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4))) : False := by
  exact RSix.XTwoNoRoot.CertifiedBridge.contradictionRoot G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hyz

/-- The five no-root `r=6`, `x=2` rows. -/
theorem rSixXTwoNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ (C.z = 5 ∨ C.z = 6)) ∨
      (y G C = 1 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5))) : False := by
  exact RSix.XTwoNoRoot.CertifiedBridge.contradiction G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hyz

/-- The five rooted `r=6`, `x=3` rows. -/
theorem rSixXThreeRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
      (y G C = 1 ∧ (C.z = 1 ∨ C.z = 2 ∨ C.z = 3))) : False := by
  exact RSix.XThreeNoRoot.CertifiedBridge.contradictionRoot G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hyz

/-- The five no-root `r=6`, `x=3` rows. -/
theorem rSixXThreeNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ (C.z = 4 ∨ C.z = 5)) ∨
      (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4))) : False := by
  exact RSix.XThreeNoRoot.CertifiedBridge.contradiction G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hyz

/-- The four rooted `r=6`, `x=4` rows. -/
theorem rSixXFourRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ (C.z = 2 ∨ C.z = 3)) ∨
      (y G C = 1 ∧ (C.z = 1 ∨ C.z = 2))) : False := by
  exact RSix.XFourNoRoot.CertifiedBridge.contradictionRoot G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hyz

/-- The four no-root `r=6`, `x=4` rows. -/
theorem rSixXFourNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 6) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) ∨
      (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3))) : False := by
  exact RSix.XFourNoRoot.CertifiedBridge.contradiction G hBound C hG hMin
    hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hyz

/-- The four rooted `r=7`, `x=2` rows. -/
theorem rSevenXTwoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧
      (C.z = 3 ∨ C.z = 4 ∨ C.z = 5 ∨ C.z = 6)) : False := by
  have hPB : C.P = C.B :=
    RSeven.XTwoNoRoot.Structure.p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 3 := hk
  have hXCard : C.X.card = 2 := hx
  have hRCard : C.R.card = 2 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 5 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  rcases hyz.2 with hz | hz | hz | hz
  · have hExternal : (externalTargets G C).card = 4 := by
      rw [card_externalTargets G C, hz, hRoot]
    exact RSeven.XTwoNoRoot.FourBridge.contradiction G hBound C hG hPivot hPB
      hBCard hk hr hx hExternal hNoSeymour
  · have hExternal : (externalTargets G C).card = 5 := by
      rw [card_externalTargets G C, hz, hRoot]
    let L := RSeven.XTwoNoRoot.Labels.arbitraryLabels G 5 C hPCard hACard
      hA1Card hXCard hRCard hExternal
    exact RSeven.XTwoNoRoot.FiveBridge.contradiction G hBound C L hG hPB
      hPivot hMin hk hHCard hA1Card hNoSeymour
  · have hExternal : (externalTargets G C).card = 6 := by
      rw [card_externalTargets G C, hz, hRoot]
    let L := RSeven.XTwoNoRoot.Labels.arbitraryLabels G 6 C hPCard hACard
      hA1Card hXCard hRCard hExternal
    exact RSeven.XTwoNoRoot.HighBridge.contradiction G (by omega) C L hG
      hPivot hBCard hk hr hx hPB hNoSeymour
  · have hExternal : (externalTargets G C).card = 7 := by
      rw [card_externalTargets G C, hz, hRoot]
    let L := RSeven.XTwoNoRoot.Labels.arbitraryLabels G 7 C hPCard hACard
      hA1Card hXCard hRCard hExternal
    exact RSeven.XTwoNoRoot.HighBridge.contradiction G (by omega) C L hG
      hPivot hBCard hk hr hx hPB hNoSeymour

/-- The four no-root `r=7`, `x=2` rows. -/
theorem rSevenXTwoNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧
      (C.z = 4 ∨ C.z = 5 ∨ C.z = 6 ∨ C.z = 7)) : False := by
  have hPB : C.P = C.B :=
    RSeven.XTwoNoRoot.Structure.p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 3 := hk
  have hXCard : C.X.card = 2 := hx
  have hRCard : C.R.card = 2 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 5 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  rcases hyz.2 with hz | hz | hz | hz
  · have hExternal : (externalTargets G C).card = 4 := by
      rw [card_externalTargets G C, hz, hNoRoot]
    exact RSeven.XTwoNoRoot.FourBridge.contradiction G hBound C hG hPivot hPB
      hBCard hk hr hx hExternal hNoSeymour
  · have hExternal : (externalTargets G C).card = 5 := by
      rw [card_externalTargets G C, hz, hNoRoot]
    let L := RSeven.XTwoNoRoot.Labels.arbitraryLabels G 5 C hPCard hACard
      hA1Card hXCard hRCard hExternal
    exact RSeven.XTwoNoRoot.FiveBridge.contradiction G hBound C L hG hPB
      hPivot hMin hk hHCard hA1Card hNoSeymour
  · have hExternal : (externalTargets G C).card = 6 := by
      rw [card_externalTargets G C, hz, hNoRoot]
    let L := RSeven.XTwoNoRoot.Labels.arbitraryLabels G 6 C hPCard hACard
      hA1Card hXCard hRCard hExternal
    exact RSeven.XTwoNoRoot.HighBridge.contradiction G (by omega) C L hG
      hPivot hBCard hk hr hx hPB hNoSeymour
  · have hExternal : (externalTargets G C).card = 7 := by
      rw [card_externalTargets G C, hz, hNoRoot]
    let L := RSeven.XTwoNoRoot.Labels.arbitraryLabels G 7 C hPCard hACard
      hA1Card hXCard hRCard hExternal
    exact RSeven.XTwoNoRoot.HighBridge.contradiction G (by omega) C L hG
      hPivot hBCard hk hr hx hPB hNoSeymour

/-- The four rooted `r=7`, `x=3` rows. -/
theorem rSevenXThreeRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧
      (C.z = 2 ∨ C.z = 3 ∨ C.z = 4 ∨ C.z = 5)) : False := by
  rcases hyz.2 with hz | hz | hz | hz
  · exact RSeven.XThreeNoRoot.ThreeBridge.impossibleRoot G C hG hMin
      hRootDegree hPivot hBCard hk hr hx hRoot hz
  · exact RSeven.XThreeNoRoot.FourBridge.impossibleRoot G hBound C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hz
  · exact RSeven.XThreeNoRoot.FiveBridge.impossibleRoot G C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hz
  · exact RSeven.XThreeNoRoot.SixBridge.impossibleRoot G hBound C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hr hx hRoot hz

/-- The four no-root `r=7`, `x=3` rows. -/
theorem rSevenXThreeNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧
      (C.z = 3 ∨ C.z = 4 ∨ C.z = 5 ∨ C.z = 6)) : False := by
  rcases hyz.2 with hz | hz | hz | hz
  · exact RSeven.XThreeNoRoot.ThreeBridge.impossible G C hG hMin hRootDegree
      hPivot hBCard hk hr hx hNoRoot hz
  · exact RSeven.XThreeNoRoot.FourBridge.impossible G hBound C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hz
  · exact RSeven.XThreeNoRoot.FiveBridge.impossible G C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hr hx hNoRoot hz
  · exact RSeven.XThreeNoRoot.SixBridge.impossible G hBound C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hr hx hNoRoot hz

/-- The three rooted `r=7`, `x=4` rows, including the capacity-twelve row. -/
theorem rSevenXFourRoot
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4)) : False := by
  rcases hyz.2 with hz | hz | hz
  · exact RSeven.XFourNoRoot.ThreeBridge.impossibleRoot G C hG hMin
      hRootDegree hPivot hBCard hk hr hx hRoot hz
  · exact RSeven.XFourNoRoot.FourBridge.impossibleRoot G C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hr hx hRoot hz
  · exact RSeven.XFourNoRoot.FiveBridge.impossibleRoot G C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hr hx hRoot hz

/-- The three no-root `r=7`, `x=4` rows, using exact internal-defect intervals
for the two largest external-defect families. -/
theorem rSevenXFourNoRoot
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5)) : False := by
  rcases hyz.2 with hz | hz | hz
  · exact RSeven.XFourNoRoot.ThreeBridge.impossible G C hG hMin hRootDegree
      hPivot hBCard hk hr hx hNoRoot hz
  · exact RSeven.XFourNoRoot.FourBridge.impossible G C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hr hx hNoRoot hz
  · exact RSeven.XFourNoRoot.FiveBridge.impossible G C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hr hx hNoRoot hz

/-- The `(7,3)` statement, dispatching the parameter reduction to its eighteen
certified graph families. -/
theorem bSevenKThreeCase : SeymourEight.BSevenKThreeCase := by
  intro V _ _ hBound G _ C hG hMin hRootDegree hPivot hBCard hk
  by_contra hNoSeymour
  have hFamily := parameterFamily G C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk
  cases hFamily with
  | rFiveXTwoRoot hr hx hRoot hyz =>
      exact rFiveXTwoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rFiveXTwoNoRoot hr hx hNoRoot hyz =>
      exact rFiveXTwoNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rFiveXThreeRoot hr hx hRoot hyz =>
      exact rFiveXThreeRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rFiveXThreeNoRoot hr hx hNoRoot hyz =>
      exact rFiveXThreeNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rFiveXFourRoot hr hx hRoot hyz =>
      exact rFiveXFourRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rFiveXFourNoRoot hr hx hNoRoot hyz =>
      exact rFiveXFourNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rSixXTwoRoot hr hx hRoot hyz =>
      exact rSixXTwoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSixXTwoNoRoot hr hx hNoRoot hyz =>
      exact rSixXTwoNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rSixXThreeRoot hr hx hRoot hyz =>
      exact rSixXThreeRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSixXThreeNoRoot hr hx hNoRoot hyz =>
      exact rSixXThreeNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rSixXFourRoot hr hx hRoot hyz =>
      exact rSixXFourRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSixXFourNoRoot hr hx hNoRoot hyz =>
      exact rSixXFourNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rSevenXTwoRoot hr hx hRoot hyz =>
      exact rSevenXTwoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSevenXTwoNoRoot hr hx hNoRoot hyz =>
      exact rSevenXTwoNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rSevenXThreeRoot hr hx hRoot hyz =>
      exact rSevenXThreeRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSevenXThreeNoRoot hr hx hNoRoot hyz =>
      exact rSevenXThreeNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz
  | rSevenXFourRoot hr hx hRoot hyz =>
      exact rSevenXFourRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSevenXFourNoRoot hr hx hNoRoot hyz =>
      exact rSevenXFourNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz

end SeymourEight.BSevenKThree
