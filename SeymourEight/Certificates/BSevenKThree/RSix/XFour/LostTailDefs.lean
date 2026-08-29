import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CompressedTailDefs

/-!
# Lost-target form of the factored deletion inequalities

Deleting one direct target can add only that target to the strict second
neighbourhood.  Every other change is a lost old second neighbour.  Expressing
the deletion condition as `7 + lost ≤ old + gained` exposes this tight
one-target slack directly.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.LostTail

open Shared.FiniteCore
open Core AuxiliaryCore ActualTail ScalarTail CompressedTail

def originalNamedSecondCount (arc pToZ : Nat → Nat → Bool)
    (p : Nat) (namedPathCount : Nat → BitVec 8) : BitVec 8 :=
  count 19 (compressedActualSecondNamed arc pToZ p namedPathCount)

def privateNamedCount (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p deleted : Nat) (namedPathCount : Nat → BitVec 8) : BitVec 8 :=
  count 19 fun target =>
    compressedActualSecondNamed arc pToZ p namedPathCount target &&
      namedPath arc pToZ realAuxArc p deleted target &&
      namedPathCount target == 1

def outsideLoss (outsidePrivateLoss : Nat → BitVec 8)
    (deleted : Nat) : BitVec 8 :=
  if 14 ≤ deleted && deleted < 18 then
    outsidePrivateLoss (deleted - 14)
  else 0

def deletionGain (namedPathCount : Nat → BitVec 8)
    (deleted : Nat) : BitVec 8 :=
  bitCount (!(namedPathCount deleted == 0))

def tSixDeletionConditions (arc pToZ : Nat → Nat → Bool)
    (outsidePrivateLoss : Nat → BitVec 8)
    (p : Nat) (namedPathCount : Nat → BitVec 8) : Bool :=
  (all 19 fun target =>
    !compressedActualSecondNamed arc pToZ p namedPathCount target ||
      (2 : BitVec 8).ule (namedPathCount target)) &&
  (all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted || !(namedPathCount deleted == 0)) &&
  (all 4 fun i => outsidePrivateLoss i == 0)

def tSevenDeletionConditions (arc pToZ realAuxArc : Nat → Nat → Bool)
    (outsidePrivateLoss : Nat → BitVec 8)
    (p : Nat) (namedPathCount : Nat → BitVec 8) : Bool :=
  all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted ||
      (privateNamedCount arc pToZ realAuxArc p deleted namedPathCount +
        outsideLoss outsidePrivateLoss deleted).ule
          (deletionGain namedPathCount deleted)

def lostTailCore (p : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsidePrivateLoss : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) (namedSecondCount : BitVec 8) : Bool :=
  let realAuxArc := combinedAuxArc auxArc extraAuxArc
  let totalSecond := namedSecondCount + outsideCount
  canonicalAuxiliaryCore arc pToZ auxArc &&
    pDegree 1 3 arc pToZ p == 8 &&
    actualAuxiliaryOriented arc pToZ realAuxArc &&
    namedPathAgreement arc pToZ realAuxArc p namedPathCount &&
    namedSecondCount == originalNamedSecondCount arc pToZ p namedPathCount &&
    outsideCount.ule 7 &&
    (all 4 fun i => (outsidePrivateLoss i).ule outsideCount) &&
    (sumCount 4 outsidePrivateLoss).ule outsideCount &&
    (all 4 fun i => pDirect arc pToZ p (14 + i) ||
      outsidePrivateLoss i == 0) &&
    ((totalSecond == 6 && tSixDeletionConditions arc pToZ
        outsidePrivateLoss p namedPathCount) ||
      (totalSecond == 7 && tSevenDeletionConditions arc pToZ realAuxArc
        outsidePrivateLoss p namedPathCount))

def lostCapacityLeaf (capacity : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsidePrivateLoss : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) (namedSecondCount : BitVec 8) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    lostTailCore (6 - capacity) arc pToZ auxArc extraAuxArc outsideCount
      outsidePrivateLoss namedPathCount namedSecondCount

def lostCapacityRangeLeaf (capacity lower upper : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsidePrivateLoss : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) (namedSecondCount : BitVec 8) : Bool :=
  lostCapacityLeaf capacity arc pToZ auxArc extraAuxArc outsideCount
      outsidePrivateLoss namedPathCount namedSecondCount &&
    (BitVec.ofNat 8 lower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 upper)

/-! Redundant but propagation-critical exact consequences in capacity six. -/

def c6DegreeCut (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 6 fun p => pDegree 1 3 arc pToZ p == 8

def c6PivotAuxCut (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 4 fun i => pDirect arc pToZ 0 (14 + i)

def c6OutsideNeedCut (auxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsidePrivateLoss : Nat → BitVec 8) : Bool :=
  (all 4 fun i => (canonicalOutsideNeed auxArc i).ule outsideCount) &&
  (all 16 fun q =>
    let deleted := q / 4
    let retained := q % 4
    decide (deleted = retained) ||
      (canonicalOutsideNeed auxArc retained + outsidePrivateLoss deleted).ule
        outsideCount)

def lostC6RangeLeaf (lower upper : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsidePrivateLoss : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) (namedSecondCount : BitVec 8) : Bool :=
  lostCapacityRangeLeaf 6 lower upper arc pToZ auxArc extraAuxArc
      outsideCount outsidePrivateLoss namedPathCount namedSecondCount &&
    c6DegreeCut arc pToZ && c6PivotAuxCut arc pToZ &&
    c6OutsideNeedCut auxArc outsideCount outsidePrivateLoss

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.LostTail
