import SeymourEight.Certificates.BSevenKThree.RSeven.XTwo.CoreDefs

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Core

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot
open XThreeNoRoot.Core XThreeNoRoot.ExpansionCore

macro "solve_x_two_core" : tactic =>
  `(tactic|
    (simp (config := { maxSteps := 1000000000 }) only
      [core, structuralCore, XThreeNoRoot.ExpansionCore.pUnionExpansion,
        XThreeNoRoot.ExpansionCore.pUnionTarget, everyXReached, rUnreached,
        pMinimumDegree, pHOut, XThreeNoRoot.Core.orientedA,
        XThreeNoRoot.Core.orientedP, XThreeNoRoot.Core.orientedPH,
        XThreeNoRoot.Core.allZReached, XThreeNoRoot.Core.aMinimumAndDegree,
        XThreeNoRoot.Core.aNonSeymour, XThreeNoRoot.Core.pOut,
        XThreeNoRoot.Core.pZOut, XThreeNoRoot.Core.aPOut,
        XThreeNoRoot.Core.localSecondCount, XThreeNoRoot.Core.strictSecondLocal,
        XThreeNoRoot.Core.reachesLocal, XThreeNoRoot.Core.directCount,
        XThreeNoRoot.Core.coreArc, XThreeNoRoot.Core.aOut,
        XThreeNoRoot.Core.aArc, XThreeNoRoot.Core.aToP,
        XThreeNoRoot.Core.pToA, XThreeNoRoot.Core.pArc,
        XThreeNoRoot.Core.pToH, XThreeNoRoot.Core.hToP,
        XThreeNoRoot.Core.pToZ, XThreeNoRoot.Core.hDirectedIndex,
        XThreeNoRoot.Core.pDirectedIndex, all, any, count, bitCount]
     bv_decide (config := { timeout := 600, acNf := true })))

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Core
