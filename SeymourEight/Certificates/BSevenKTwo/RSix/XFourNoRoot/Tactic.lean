import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core

open Lean Parser Tactic

macro "solve_r_six_x_four_no_root" : tactic =>
  `(tactic|
    simp only [coreCase, coreAt] <;>
    unfold orientedBasic <;>
    simp (config := { maxSteps := 1000000000 }) only
      [core, orderedZ, ePIn, orderedH, hPOut, orderedP, pRowKey,
      pConditions, auxiliaryContribution,
      totalPP, totalPH, totalPE, totalHP, pSecondCount, pSecond, pReached,
      pEOut, pHOut, pOut, hToP, pToH, pArc, directedIndex,
      Shared.FiniteCore.count, Shared.FiniteCore.all, Shared.FiniteCore.any,
      Shared.FiniteCore.bitCount] <;>
    simp (config := { maxSteps := 1000000000 }) only [pToE] <;>
    bv_decide (config := { timeout := 1200, acNf := true }))

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core
