import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ScalarTailDefs

/-!
# Factored named-path and scalar outside-tail quotient

For each named target, record once the number of represented two-step paths
from the selected pivot.  Deleting one named middle leaves a path precisely
when the total is larger than the zero-or-one contribution of that middle.
This avoids rebuilding the same eighteen path terms in every deletion test.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompressedTail

open Shared.FiniteCore
open Core AuxiliaryCore ActualTail ScalarTail

def namedPath (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p middle target : Nat) : Bool :=
  decide (middle ≠ 8 + p) && decide (middle ≠ target) &&
    pDirect arc pToZ p middle && actualNamedArc arc pToZ realAuxArc middle target

def namedPathAgreement (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p : Nat) (namedPathCount : Nat → BitVec 8) : Bool :=
  all 19 fun target =>
    namedPathCount target == count 18 fun middle =>
      namedPath arc pToZ realAuxArc p middle target

def compressedActualSecondNamed (arc pToZ : Nat → Nat → Bool)
    (p : Nat) (namedPathCount : Nat → BitVec 8) (target : Nat) : Bool :=
  decide (target ≠ 8 + p) && !pDirect arc pToZ p target &&
    !(namedPathCount target == 0)

def compressedDeletionReaches (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p deleted target : Nat) (namedPathCount : Nat → BitVec 8) : Bool :=
  (bitCount (namedPath arc pToZ realAuxArc p deleted target)).ult
    (namedPathCount target)

def compressedDeletionSecondNamed (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p deleted : Nat) (namedPathCount : Nat → BitVec 8)
    (target : Nat) : Bool :=
  decide (target ≠ 8 + p) &&
    (if target = deleted then
      compressedDeletionReaches arc pToZ realAuxArc p deleted target
        namedPathCount
    else
      !pDirect arc pToZ p target &&
        compressedDeletionReaches arc pToZ realAuxArc p deleted target
          namedPathCount)

def compressedDeletionSecondCount (arc pToZ realAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (p deleted : Nat) (namedPathCount : Nat → BitVec 8) : BitVec 8 :=
  count 19 (compressedDeletionSecondNamed arc pToZ realAuxArc p deleted
      namedPathCount) +
    scalarDeletionOutsideCount outsideCount outsideAfterAuxDeletion deleted

def compressedDeletionConditions (arc pToZ realAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (p : Nat) (namedPathCount : Nat → BitVec 8) : Bool :=
  all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted ||
      (7 : BitVec 8).ule (compressedDeletionSecondCount arc pToZ realAuxArc
        outsideCount outsideAfterAuxDeletion p deleted namedPathCount)

def compressedTailCore (p : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) : Bool :=
  let realAuxArc := combinedAuxArc auxArc extraAuxArc
  canonicalAuxiliaryCore arc pToZ auxArc &&
    pDegree 1 3 arc pToZ p == 8 &&
    actualAuxiliaryOriented arc pToZ realAuxArc &&
    namedPathAgreement arc pToZ realAuxArc p namedPathCount &&
    outsideCount.ule 7 &&
    (all 4 fun i => (outsideAfterAuxDeletion i).ule outsideCount) &&
    (count 19 (compressedActualSecondNamed arc pToZ p namedPathCount) +
      outsideCount).ule 7 &&
    compressedDeletionConditions arc pToZ realAuxArc outsideCount
      outsideAfterAuxDeletion p namedPathCount

def compressedCapacityLeaf (capacity : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    compressedTailCore (6 - capacity) arc pToZ auxArc extraAuxArc
      outsideCount outsideAfterAuxDeletion namedPathCount

def compressedCapacityRangeLeaf (capacity lower upper : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (namedPathCount : Nat → BitVec 8) : Bool :=
  compressedCapacityLeaf capacity arc pToZ auxArc extraAuxArc outsideCount
      outsideAfterAuxDeletion namedPathCount &&
    (BitVec.ofNat 8 lower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 upper)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompressedTail
