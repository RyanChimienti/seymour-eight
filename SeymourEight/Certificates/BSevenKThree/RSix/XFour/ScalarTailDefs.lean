import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ActualTailDefs

/-!
# Scalar outside-tail quotient

For a fixed degree-eight `P` pivot, the anonymous strict second neighbours
outside the named finite core are consumed only through five cardinalities:
their total number, and the number still reached after deleting each of the
four represented auxiliary intermediates.  This quotient keeps those counts
directly instead of representing a padded seven-by-four incidence matrix.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ScalarTail

open Shared.FiniteCore
open Core AuxiliaryCore ActualTail

def scalarDeletionOutsideCount (outsideCount : BitVec 8)
    (outsideAfterAuxDeletion : Nat → BitVec 8) (deleted : Nat) : BitVec 8 :=
  if 14 ≤ deleted && deleted < 18 then
    outsideAfterAuxDeletion (deleted - 14)
  else outsideCount

def scalarDeletionSecondCount (arc pToZ realAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (p deleted : Nat) : BitVec 8 :=
  count 19 (deletionSecondNamed arc pToZ realAuxArc p deleted) +
    scalarDeletionOutsideCount outsideCount outsideAfterAuxDeletion deleted

def scalarDeletionConditions (arc pToZ realAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8) (outsideAfterAuxDeletion : Nat → BitVec 8)
    (p : Nat) : Bool :=
  all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted ||
      (7 : BitVec 8).ule (scalarDeletionSecondCount arc pToZ realAuxArc
        outsideCount outsideAfterAuxDeletion p deleted)

def scalarTailCore (p : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8)
    (outsideAfterAuxDeletion : Nat → BitVec 8) : Bool :=
  canonicalAuxiliaryCore arc pToZ auxArc &&
    pDegree 1 3 arc pToZ p == 8 &&
    actualAuxiliaryOriented arc pToZ (combinedAuxArc auxArc extraAuxArc) &&
    (outsideCount).ule 7 &&
    (all 4 fun i => (outsideAfterAuxDeletion i).ule outsideCount) &&
    (count 19 (actualSecondNamed arc pToZ
      (combinedAuxArc auxArc extraAuxArc) p) + outsideCount).ule 7 &&
    scalarDeletionConditions arc pToZ (combinedAuxArc auxArc extraAuxArc)
      outsideCount outsideAfterAuxDeletion p

def scalarCapacityLeaf (capacity : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8)
    (outsideAfterAuxDeletion : Nat → BitVec 8) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    scalarTailCore (6 - capacity) arc pToZ auxArc extraAuxArc
      outsideCount outsideAfterAuxDeletion

def scalarCapacityRangeLeaf (capacity lower upper : Nat)
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 8)
    (outsideAfterAuxDeletion : Nat → BitVec 8) : Bool :=
  scalarCapacityLeaf capacity arc pToZ auxArc extraAuxArc outsideCount
      outsideAfterAuxDeletion &&
    (BitVec.ofNat 8 lower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 upper)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ScalarTail
