import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Lean Parser Tactic

macro "rSixXTwoNoRoot_decide" : tactic =>
  `(tactic|
    (try simp (config := { maxSteps := 1000000000 }) only [reachedFullHybrid,
      reachedEffectiveHybrid,
      reachedProjectedHybrid,
      reachedEffectiveLeaf,
      reachedEffectiveLowPH,
      reachedEffectivePH,
      reachedPOnlyPH,
      reachedEffectiveLowPHDistinguished,
      reachedEffectivePHDistinguished,
      microHEffectiveLowPH, microHEffectiveLowPHMissing, microHCore,
      microFourDistinguished, microUnreachedDistinguished,
      fixedSharpHybridLeaf,
      canonicalHybridLeaf,
      canonicalHybridExactLeaf,
      branchedHybridExactLeaf, orderedLastThreeSignatures,
      branchedHybridHPLeaf,
      singleExternalMissingAt, singleMissingHybridHPLeaf,
      singleMissingArithmeticLeaf,
      distinguishedAOne, hardResidualAOne,
      orderedPTailSignatures, pFullSignatureBit,
      orderedStructuralPairSignatures, hFullSignatureBit,
      reachedEffectiveNoMissing,
      equalityBoundaryLeaf,
      commonBareCore, cZeroHardLeaf, hybridLeaf,
      microCZeroResidual, microCZeroNonHard, microCOneAll, microCOneNonHard,
      microCOneHighPH,
      microCOnePositiveMissing,
      microCOneHighAlpha,
      microCOneLowAlphaHighMissing,
      microCTwoResidual, microLeaf, microCore,
      microCTwoHighPH,
      microFour, microUnreached,
      hSecondZCount, hRestrictedSecondCountFour,
      hRestrictedNonSeymourFour, pMicroNonSeymourFour,
      hDirectUnreached, hRestrictedSecondCountUnreached,
      hRestrictedNonSeymourUnreached, pMicroNonSeymourUnreached,
      hToQCore, hDirectCore, hSecondQCore, hRestrictedSecondCountCore,
      hRestrictedNonSeymourCore, pSecondEMicroCoreCount,
      pMicroNonSeymourCore, microCoreCTwo,
      hArc, xToT, hToQTwo, hDirectTwo, orientedHH,
      aOneSecondH, aOneSecondP, aOneSecondZ, aOneSecondT, hSecondQ,
      aOneRestrictedSecondCount, aOneRestrictedNonSeymour,
      pSecondTCount, pSecondHMicroCount, pSecondEMicroCount, pMicroNonSeymour, universalLeaf,
      canonicalUniversalLeaf, canonicalUniversalCore,
      universalM, universalCore, orderedAllHSignatures, orderedAllExternalSignatures,
      firstFourExternalReached, sharpKingAt, scoreKingAt,
      exactClassKingAt, canonicalP, privateExternalCount,
      externalFirstRowKey, orderedPExternalFirst,
      deletedPReachedRelaxed, pTightPrivate, projectedLeaf,
      projectedCore,
      projectedDefectCore,
      cCore, defectCore,
      core, commonCore,
      vertexCount, directCount, aOut, aPOut, aBOut, pOut,
      pHOut, hPOut, pEOut, reachesLocal, strictSecondLocal,
      localSecondCount, aNonSeymour, pNonSeymour, orientedA, orientedP,
      orientedPH, completeP, completePH, fixedA, everyXReached, qStructure, allExternalReached,
      inactiveEZero, aMinimumAndDegree, pMinimumDegree, totalPToE,
      totalPToH, totalHToP, totalPOut, externalMissing, internalMissing,
      crossMissing, aOneToQ, effectiveAtRowSize,
      individualEffectiveLowerFour, individualEffectiveLowerFive,
      individualEffectiveLower, pSecondPCount, pEffectiveCondition,
      pEffectiveConditionFive,
      pEffectiveConditionFiveAt,
      pSecondECount, pSecondHCount, pRestrictedNonSeymour,
      reachesPH, reachCount, sharpKing, score, scoreKing,
      equalScoreClass, isExact, exactCount, exactInternal, exactOutside,
      exactMissing, exactClassKing, pivotNeighbor, secondTarget, privateTarget,
      deletedReached, tightPrivate, pRowKey, orderedP,
      orderedStructuralClasses, orderedExternal, lexGe, phColumnBit,
      orderedHSignatures, orderedExternalSignatures,
      orderedStructuralFull, orderedExternalFull]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [Shared.FiniteCore.sumCount,
      Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
      Shared.FiniteCore.any, Shared.FiniteCore.all]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [hArc, xToT, hToQTwo, hDirectTwo, orientedHH,
      hToQCore, hDirectCore, hSecondQCore, hRestrictedSecondCountCore,
      hRestrictedNonSeymourCore, pSecondEMicroCoreCount,
      pMicroNonSeymourCore,
      effectiveAtRowSize, individualEffectiveLowerFour,
      individualEffectiveLowerFive, individualEffectiveLower,
      pEffectiveCondition,
      pEffectiveConditionFive,
      pEffectiveConditionFiveAt,
      pFullSignatureBit, hFullSignatureBit, lexGe,
      aOneSecondH, aOneSecondP, aOneSecondZ, aOneSecondT, hSecondQ,
      aOneRestrictedSecondCount, aOneRestrictedNonSeymour,
      pSecondTCount, pSecondHMicroCount, pSecondEMicroCount, pMicroNonSeymour,
      pOut, pHOut, hPOut, pEOut,
      pSecondPCount, pSecondHCount, pSecondECount, reachesPH,
      totalPToH, totalHToP, totalPToE, externalMissing]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [Shared.FiniteCore.sumCount,
      Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
      Shared.FiniteCore.any, Shared.FiniteCore.all]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [hArc, xToT, hToQTwo, hDirectTwo, orientedHH,
      hToQCore, hDirectCore, hSecondQCore, hRestrictedSecondCountCore,
      hRestrictedNonSeymourCore, pSecondEMicroCoreCount,
      pMicroNonSeymourCore,
      effectiveAtRowSize, individualEffectiveLowerFour,
      individualEffectiveLowerFive, individualEffectiveLower,
      pEffectiveCondition,
      pEffectiveConditionFive,
      pEffectiveConditionFiveAt,
      pFullSignatureBit, hFullSignatureBit, lexGe,
      aOneSecondH, aOneSecondP, aOneSecondZ, aOneSecondT, hSecondQ,
      aOneRestrictedSecondCount, aOneRestrictedNonSeymour,
      pSecondTCount, pSecondHMicroCount, pSecondEMicroCount, pMicroNonSeymour,
      pOut, pHOut, hPOut, pEOut,
      pSecondPCount, pSecondHCount, pSecondECount, reachesPH,
      totalPToH, totalHToP, totalPToE, externalMissing]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [Shared.FiniteCore.sumCount,
      Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
      Shared.FiniteCore.any, Shared.FiniteCore.all]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [individualEffectiveLowerFiveAt, effectiveAtRowSize, defectLoss]) <;>
    (try simp (config := { maxSteps := 1000000000 }) only
      [coreArc, aToP, pToA, aToQ, rToP, pToE, hToP, pToH,
      pArc, directedIndex, aArc]) <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
