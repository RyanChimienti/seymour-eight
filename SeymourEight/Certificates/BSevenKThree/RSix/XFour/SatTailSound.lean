import SeymourEight.Certificates.BSevenKThree.RSix.XFour.SatTailTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail

open Shared.FiniteCore Core AuxiliaryCore ActualTail CompressedTail

def actualPathCount5 (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p target : Nat) : BitVec 5 :=
  count5 18 fun middle => namedPath arc pToZ realAuxArc p middle target

def actualOutsideCount5 (arc pToZ outsideArc : Nat → Nat → Bool)
    (p : Nat) : BitVec 5 :=
  count5 7 fun slot => actualSlotReached arc pToZ outsideArc p slot

def actualOutsidePrivateLoss5 (arc pToZ outsideArc : Nat → Nat → Bool)
    (p i : Nat) : BitVec 5 :=
  count5 7 fun slot =>
    actualSlotReached arc pToZ outsideArc p slot &&
      !deletionSlotReached arc pToZ outsideArc p (14 + i) slot

def actualNamedSecondCount5 (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p : Nat) : BitVec 5 :=
  count5 19 fun target =>
    satActualSecondNamed arc pToZ p (actualPathCount5 arc pToZ realAuxArc p)
      target

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem actualTailCore_implies_satTailCore
    (arc pToZ auxArc extraAuxArc outsideArc : Nat → Nat → Bool)
    (hCommon : commonCore 1 3 arc pToZ = true)
    (h : actualTailCore 5 arc pToZ auxArc extraAuxArc outsideArc = true) :
    satTailCore 5 arc pToZ auxArc extraAuxArc
      (actualOutsideCount5 arc pToZ outsideArc 5)
      (actualOutsidePrivateLoss5 arc pToZ outsideArc 5)
      (actualPathCount5 arc pToZ (combinedAuxArc auxArc extraAuxArc) 5)
      (actualNamedSecondCount5 arc pToZ (combinedAuxArc auxArc extraAuxArc) 5) =
        true := by
  have hOriented : orientedP arc = true := by
    unfold commonCore at hCommon
    simp only [Bool.and_eq_true] at hCommon
    tauto
  have hNoAOne : noPToAOne arc = true := by
    unfold commonCore at hCommon
    simp only [Bool.and_eq_true] at hCommon
    tauto
  have hZero : !pDirect arc pToZ 5 0 = true := by
    rw [noPToAOne, all_eq_true_iff] at hNoAOne
    have hp := hNoAOne 5 (by omega)
    simpa [pDirect, coreArc, pToA] using hp
  have hLoop : !pDirect arc pToZ 5 13 = true := by
    rw [orientedP, all_eq_true_iff] at hOriented
    have hp := hOriented 5 (by omega)
    simp only [Bool.and_eq_true] at hp
    simpa [pDirect, coreArc, pArc] using hp.1
  have hDirectDegree :
      pDegree 1 3 arc pToZ 5 = count 17 (fun d => pDirect arc pToZ 5 (1 + d)) := by
    simp only [pDegree, pAuxOut, pZOut, pHOut, pOut,
      pDirect, coreArc, pToQ, pToA, pArc, count, bitCount] at hZero hLoop ⊢
    bv_decide
  clear hCommon hOriented hNoAOne
  simp (config := { maxSteps := 5000000 }) only
    [actualPathCount5, actualOutsideCount5, actualOutsidePrivateLoss5,
      actualNamedSecondCount5,
      satTailCore, satTSevenConditions, satTSixConditions,
      satPrivateNamedCount, satOriginalNamedSecondCount,
      satActualSecondNamed, satPathAgreement, sumCount5, count5, bitCount5,
      namedPath,
      actualTailCore, deletionConditions, deletionSecondCount,
      deletionSlotReached, deletionSecondNamed, ActualTail.deletionReachesNamed,
      actualSecondCount, actualSlotReached, actualSecondNamed,
      actualReachesNamed,
      all, any, count, bitCount] at h hZero hLoop hDirectDegree ⊢
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail
