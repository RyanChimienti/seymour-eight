import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.ExpansionDefs

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore

open Lean Parser Tactic
open Core Shared.FiniteCore

macro "solve_expansion_core" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [core, structuralCore, pUnionExpansion, pUnionTarget,
      pMinimumDegree, aMinimumAndDegree, allZReached, rUnreached,
      everyXReached, orientedPH, orientedP, orientedA, aNonSeymour,
      localSecondCount, strictSecondLocal, reachesLocal, pZOut, hPOut,
      pHOut, pOut, aPOut, aOut, directCount, coreArc, pToA, aToP,
      pToZ, hToP, pToH, pArc, pDirectedIndex, aArc, hDirectedIndex,
      any, all, sumCount, count, bitCount] <;>
    bv_decide (config := { timeout := 3600, acNf := true }))

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore
