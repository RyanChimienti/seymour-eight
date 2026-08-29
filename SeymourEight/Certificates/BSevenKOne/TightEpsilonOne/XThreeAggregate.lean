import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.XThreeAggregateCoreDefs

namespace SeymourEight.EpsilonOneXThreeReducedCore

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem aggregateCore_unsat (bits : Encoding) : aggregateCore bits = false := by
  simp (config := { maxSteps := 10000000 }) only [aggregateCore, aggregateTail,
    aggregateOrderedP, hNonSeymour, covered, fixedStructure, oriented,
    protectedRedundancy, alternateProtected, protectedA, rootEquation, secondP,
    reachedP, pDegree, pEOut, pHOut, pPOut, aSecond, secondFromA, reached,
    aDegree, aPOut, aOut, arc, pToA, aToP, zp, aa, rp, pe, hp, ph, pp, all,
    any, sumCount, count, bitCount]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.EpsilonOneXThreeReducedCore
