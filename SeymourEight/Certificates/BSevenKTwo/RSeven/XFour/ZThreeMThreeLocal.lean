import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeMThreeLocalDefs
import Mathlib.Tactic.IntervalCases

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeLocalCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem unsat (bits : Encoding) : core bits = false := by
  simp (config := { maxSteps := 1000000000 }) only [core, xDeletionExpands,
    retainedAfterAOneDeletion, pNonSeymour,
    aNonSeymour, totalPToZ, pDegreeEight, hDegreeEight,
    hTournament, fixedA, orientedA, localSecondCount,
    strictSecondLocal, reachesLocal, pZOut, pHOut, pOut,
    directCount, coreArc, pToA, aToP, rToP, pToZ, hToP, pToH, pArc,
    upperIndex, aArc, all, any, count, bitCount]
  bv_decide

set_option maxRecDepth 100000 in
theorem pDegree_eq_direct (bits : Encoding) (p : Nat) (hp : p < 7) :
    pOut bits p + pHOut bits p + pZOut bits p = directCount bits (8 + p) := by
  interval_cases p <;>
    simp only [pZOut, pHOut, pOut, directCount, coreArc, pToA, aToP,
      pToZ, pToH, pArc, upperIndex, count, bitCount] <;>
    bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeLocalCore
