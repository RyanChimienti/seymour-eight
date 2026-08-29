import SeymourEight.Certificates.BSevenKThree.RSix.XFour.LostTailDefs

/-!
# Saturating path-summary quotient

Deletion uses only whether a named target has zero, one, or at least two
represented paths.  Five-bit counts avoid the much larger eight-bit adder
trees while representing all eighteen possible middles without overflow.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail

open Shared.FiniteCore
open Core AuxiliaryCore ActualTail CompressedTail LostTail

def bitCount5 (b : Bool) : BitVec 5 := if b then 1 else 0

def count5 : Nat → (Nat → Bool) → BitVec 5
  | 0, _ => 0
  | n + 1, f => count5 n f + bitCount5 (f n)

def sumCount5 : Nat → (Nat → BitVec 5) → BitVec 5
  | 0, _ => 0
  | n + 1, f => sumCount5 n f + f n

def satPathAgreement (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p : Nat) (pathCount : Nat → BitVec 5) : Bool :=
  all 19 fun target =>
    pathCount target == count5 18 fun middle =>
      namedPath arc pToZ realAuxArc p middle target

def satActualSecondNamed (arc pToZ : Nat → Nat → Bool)
    (p : Nat) (pathCount : Nat → BitVec 5) (target : Nat) : Bool :=
  decide (target ≠ 8 + p) && !pDirect arc pToZ p target &&
    !(pathCount target == 0)

def satOriginalNamedSecondCount (arc pToZ : Nat → Nat → Bool)
    (p : Nat) (pathCount : Nat → BitVec 5) : BitVec 5 :=
  count5 19 (satActualSecondNamed arc pToZ p pathCount)

def satPrivateNamedCount (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p deleted : Nat) (pathCount : Nat → BitVec 5) : BitVec 5 :=
  count5 19 fun target =>
    satActualSecondNamed arc pToZ p pathCount target && pathCount target == 1 &&
      namedPath arc pToZ realAuxArc p deleted target

def satTSixConditions (arc pToZ : Nat → Nat → Bool)
    (outsidePrivateLoss : Nat → BitVec 5) (p : Nat)
    (pathCount : Nat → BitVec 5) : Bool :=
  (all 19 fun target =>
    !satActualSecondNamed arc pToZ p pathCount target ||
      (2 : BitVec 5).ule (pathCount target)) &&
  (all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted || !(pathCount deleted == 0)) &&
  (all 4 fun i => outsidePrivateLoss i == 0)

def satTSevenConditions (arc pToZ realAuxArc : Nat → Nat → Bool)
    (outsidePrivateLoss : Nat → BitVec 5) (p : Nat)
    (pathCount : Nat → BitVec 5) : Bool :=
  all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted ||
      (satPrivateNamedCount arc pToZ realAuxArc p deleted pathCount +
        (if 14 ≤ deleted && deleted < 18 then
          outsidePrivateLoss (deleted - 14) else 0)).ule
          (bitCount5 (!(pathCount deleted == 0)))

def satC6OutsideNeedCut (auxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5) : Bool :=
  (all 4 fun i =>
    (canonicalOutsideNeed auxArc i).ule (outsideCount.zeroExtend 8)) &&
  (all 16 fun q =>
    let deleted := q / 4
    let retained := q % 4
    decide (deleted = retained) ||
      (canonicalOutsideNeed auxArc retained +
        (outsidePrivateLoss deleted).zeroExtend 8).ule
          (outsideCount.zeroExtend 8))

def satTailCore (p : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5)
    (pathCount : Nat → BitVec 5) (namedSecondCount : BitVec 5) : Bool :=
  let realAuxArc := combinedAuxArc auxArc extraAuxArc
  let totalSecond := namedSecondCount + outsideCount
  canonicalAuxiliaryCore arc pToZ auxArc &&
    pDegree 1 3 arc pToZ p == 8 &&
    actualAuxiliaryOriented arc pToZ realAuxArc &&
    satPathAgreement arc pToZ realAuxArc p pathCount &&
    namedSecondCount == satOriginalNamedSecondCount arc pToZ p pathCount &&
    outsideCount.ule 7 &&
    (all 4 fun i => (outsidePrivateLoss i).ule outsideCount) &&
    (sumCount5 4 outsidePrivateLoss).ule outsideCount &&
    (all 4 fun i => pDirect arc pToZ p (14 + i) ||
      outsidePrivateLoss i == 0) &&
    ((totalSecond == 6 && satTSixConditions arc pToZ outsidePrivateLoss p
        pathCount) ||
      (totalSecond == 7 && satTSevenConditions arc pToZ realAuxArc
        outsidePrivateLoss p pathCount))

def satCapacityRangeLeaf (capacity lower upper : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5)
    (pathCount : Nat → BitVec 5) (namedSecondCount : BitVec 5) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    satTailCore (6 - capacity) arc pToZ auxArc extraAuxArc outsideCount
      outsidePrivateLoss pathCount namedSecondCount &&
    (BitVec.ofNat 8 lower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 upper)

def satC6RangeLeaf (lower upper : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5)
    (pathCount : Nat → BitVec 5) (namedSecondCount : BitVec 5) : Bool :=
  satCapacityRangeLeaf 6 lower upper arc pToZ auxArc extraAuxArc outsideCount
      outsidePrivateLoss pathCount namedSecondCount &&
    c6DegreeCut arc pToZ && c6PivotAuxCut arc pToZ &&
    satC6OutsideNeedCut auxArc outsideCount outsidePrivateLoss

def satC6RangeTotalLeaf (lower upper total : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5)
    (pathCount : Nat → BitVec 5) (namedSecondCount : BitVec 5) : Bool :=
  satC6RangeLeaf lower upper arc pToZ auxArc extraAuxArc outsideCount
      outsidePrivateLoss pathCount namedSecondCount &&
    namedSecondCount + outsideCount == BitVec.ofNat 5 total

def c1PivotAuxCut (arc pToZ : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (count 4 fun i => pDirect arc pToZ 5 (14 + i))

def c1DegreeSumCut (arc pToZ : Nat → Nat → Bool) : Bool :=
  sumCount 6 (pDegree 1 3 arc pToZ) == 53

def satC1OutsideNeedCut (arc pToZ auxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5) : Bool :=
  (all 4 fun i => !pDirect arc pToZ 5 (14 + i) ||
    (canonicalOutsideNeed auxArc i).ule (outsideCount.zeroExtend 8)) &&
  (all 16 fun q =>
    let deleted := q / 4
    let retained := q % 4
    decide (deleted = retained) || !pDirect arc pToZ 5 (14 + deleted) ||
      !pDirect arc pToZ 5 (14 + retained) ||
      (canonicalOutsideNeed auxArc retained +
        (outsidePrivateLoss deleted).zeroExtend 8).ule
          (outsideCount.zeroExtend 8))

def satC1Leaf
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5)
    (pathCount : Nat → BitVec 5) (namedSecondCount : BitVec 5) : Bool :=
  satCapacityRangeLeaf 1 0 1 arc pToZ auxArc extraAuxArc outsideCount
      outsidePrivateLoss pathCount namedSecondCount &&
    aMissing arc == 0 &&
    (alpha 1 arc + internalMissing arc).ule 1 &&
    externalMissing 1 3 arc pToZ + alpha 1 arc + internalMissing arc == 1 &&
    c1PivotAuxCut arc pToZ && c1DegreeSumCut arc pToZ

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail
