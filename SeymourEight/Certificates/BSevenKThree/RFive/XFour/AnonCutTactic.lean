import SeymourEight.Certificates.BSevenKThree.RFive.XFour.AnonCutDefs
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.Tactic

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

open Lean Parser Tactic

macro "r5x4_anon_cut_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [anonCutCounterexample, selectedResidualCore, aNonSeymourSelectedAnon, selectedAnonLower,
        qIndividualAnonymousLower, qAnonymousSharpLower] <;>
    r5x4_no_root_decide)

macro "r5x4_anon_upper_cut_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [anonUpperCutCounterexample] <;>
    r5x4_no_root_decide)

macro "r5x4_selected_residual_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [selectedResidualCore, aNonSeymourSelectedAnon, selectedAnonLower,
        qIndividualAnonymousLower, qAnonymousSharpLower] <;>
    r5x4_no_root_decide)

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
