import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.CoreDefs

namespace SeymourEight.ThreeZHighDefect

open FiveZExactRisk

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
theorem pComplete_of_capacity (bits : BitVec 218)
    (hor : orientedP bits = true)
    (hc : totalPOut bits = 21) : pComplete bits = true := by
  simp (config := { maxSteps := 1000000 }) only [orientedP, totalPOut,
    pComplete, pArc, orientedSquare, all, count, bitCount] at hor hc ⊢
  bv_decide (config := { timeout := 300, acNf := true })

set_option maxHeartbeats 8000000 in
theorem pOneComplete_of_capacity (bits : BitVec 218)
    (hor : orientedP bits = true)
    (hc : totalPOut bits = 20) : pOneComplete bits = true := by
  simp (config := { maxSteps := 1000000 }) only [orientedP, totalPOut,
    pOneComplete, pMissingIndex, firstTrueBV, upperPairI, upperPairJ, pArc,
    orientedSquare, all, count, bitCount] at hor hc ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.ThreeZHighDefect
