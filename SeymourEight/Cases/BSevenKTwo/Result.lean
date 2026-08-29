import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.XFourNoRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.XFourRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XFiveNoRoot.XFiveNoRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XFiveRoot.XFiveRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoNoRoot.XTwoNoRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoRoot.XTwoRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XThreeNoRoot.XThreeNoRoot
import SeymourEight.Cases.BSevenKTwo.RSeven.XThreeRoot.XThreeRoot
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Impossible
import SeymourEight.Cases.BSevenKTwo.RSix.XFourRoot.Impossible
import SeymourEight.Cases.BSevenKTwo.RSix.XThreeNoRoot.Impossible
import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.Impossible
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.Impossible
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.Impossible
import SeymourEight.Cases.BSevenKTwo.Counting

set_option linter.style.header false

/-!
# Assembly of the `(|B|, k) = (7, 2)` case

The graph-level counting reduction in `Counting` produces 32 exact parameter
rows.  They are grouped here into fourteen families by `(r,x)` and root
status.  The `r=7`, `x=4` developments close both root statuses using a shared
collection of finite certificates.
-/

namespace SeymourEight.BSevenKTwo

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The three rooted `r=6`, `x=2` rows, using the shared certificates through
the combined external-target set. -/
theorem rSixXTwoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 4) ∨
      (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3))) : False :=
  RSix.XTwoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The three no-root `r=6`, `x=2` rows, closed by a direct argument in the
unreached row and finite local certificates in the two reached rows. -/
theorem rSixXTwoNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ C.z = 5) ∨
      (y G C = 1 ∧ (C.z = 3 ∨ C.z = 4))) : False :=
  RSix.XTwoNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The two rooted `r=6`, `x=3` rows. -/
theorem rSixXThreeRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2)) : False :=
  RSix.XThreeRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The two no-root `r=6`, `x=3` rows. -/
theorem rSixXThreeNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ C.z = 4) ∨ (y G C = 1 ∧ C.z = 3)) : False :=
  RSix.XThreeNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The two rooted `r=6`, `x=4` rows, obtained by transporting the no-root
auxiliary-column argument and strengthening its defect-two row condition. -/
theorem rSixXFourRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 2) ∨ (y G C = 1 ∧ C.z = 1)) : False :=
  RSix.XFourRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The two no-root `r=6`, `x=4` rows. -/
theorem rSixXFourNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2)) : False :=
  RSix.XFourNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The three rooted `r=7`, `x=2` rows.  Combining the reached root with `Z`
as the external-target set allows all three rows to reuse the no-root
certificates. -/
theorem rSevenXTwoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5)) : False :=
  RSeven.XTwoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The three no-root `r=7`, `x=2` rows.  A common finite core combines the
sharpened `H→P` bound, individual effective-capacity bounds, and the
seven-vertex one-tail reduction. -/
theorem rSevenXTwoNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 2) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧ (C.z = 4 ∨ C.z = 5 ∨ C.z = 6)) : False :=
  RSeven.XTwoNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The three rooted `r=7`, `x=3` rows.  Combining the reached root with `Z`
as the external-target set allows all three rows to reuse the no-root
certificates. -/
theorem rSevenXThreeRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧ (C.z = 2 ∨ C.z = 3 ∨ C.z = 4)) : False :=
  RSeven.XThreeRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The three no-root `r=7`, `x=3` rows.  Canonical relabeling and the
shared effective-capacity bounds reduce them to three isolated certificates. -/
theorem rSevenXThreeNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5)) : False :=
  RSeven.XThreeNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The two rooted `r=7`, `x=4` rows. Combining the reached root with `Z` as
the external-target set puts both rows within the shared certificate family. -/
theorem rSevenXFourRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧ (C.z = 2 ∨ C.z = 3)) : False :=
  RSeven.XFourRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The two no-root `r=7`, `x=4` rows.  Vertex relabeling and graph-level
capacity equalities reduce their finite tails to the isolated certificates
assembled by `RSeven.XFourNoRoot`. -/
theorem rSevenXFourNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧ (C.z = 3 ∨ C.z = 4)) : False :=
  RSeven.XFourNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The rooted `r=7`, `x=5`, `(y,z)=(0,2)` row, split by external/internal
defect and `theta`, with the one-high-excess case removed by hand. -/
theorem rSevenXFiveRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 5) (hRoot : epsilonS G C = 1)
    (hyz : y G C = 0 ∧ C.z = 2) : False :=
  RSeven.XFiveRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hRoot hyz

/-- The no-root `r=7`, `x=5`, `(y,z)=(0,3)` row.  Canonical relabeling and
graph-level defect bounds reduce its finite tail to the isolated certificates
assembled by `RSeven.XFiveNoRoot`. -/
theorem rSevenXFiveNoRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 5) (hNoRoot : epsilonS G C = 0)
    (hyz : y G C = 0 ∧ C.z = 3) : False :=
  RSeven.XFiveNoRoot.impossible G hBound C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk hr hx hNoRoot hyz

/-- The `(7,2)` statement, dispatching the parameter reduction to its fourteen
certified graph families. -/
theorem bSevenKTwoCase : SeymourEight.BSevenKTwoCase := by
  intro V _ _ hBound G _ C hG hMin hRootDegree hPivot hBCard hk
  by_contra hNoSeymour
  have hFamily := parameterFamily G C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk
  cases hFamily with
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
  | rSevenXFiveRoot hr hx hRoot hyz =>
      exact rSevenXFiveRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hRoot hyz
  | rSevenXFiveNoRoot hr hx hNoRoot hyz =>
      exact rSevenXFiveNoRoot G hBound C hG hMin hNoSeymour hRootDegree hPivot
        hBCard hk hr hx hNoRoot hyz

end SeymourEight.BSevenKTwo
