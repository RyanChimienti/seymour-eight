import SeymourEight.Certificates.BSevenKThree.RSix.XFour.AuxiliaryDefs

/-!
# Actual auxiliary tails for one exact degree-eight pivot

The trimmed auxiliary neighborhoods in `AuxiliaryDefs` are sufficient for the
degree and Hall constraints, but not for one-arc deletion: deleting an arc can
destroy a path to a retained target while an unretained target replaces it.
Here `realAuxArc` records the actual arcs from the four auxiliary vertices to
the nineteen named vertices.  Seven padded slots record the complete part of
the chosen pivot's strict second neighborhood outside the named vertices.
Thus the deletion inequalities below are exact for that pivot.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ActualTail

open Shared.FiniteCore
open Core AuxiliaryCore

def canonicalHallCount (arc pToZ auxArc : Nat → Nat → Bool)
    (source : Nat) : BitVec 8 :=
  count 3 (hallZReached arc pToZ auxArc source) +
    if aToQ arc source then canonicalOutsideNeed auxArc 0 else 0

def canonicalHallConditions (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  all 8 fun source => !innerSeymour arc source ||
    (canonicalHallCount arc pToZ auxArc source).ult (aBOut arc source)

def canonicalFullSecondCount (arc pToZ auxArc : Nat → Nat → Bool)
    (source : Nat) : BitVec 8 :=
  count 19 (fullSecondNamed arc pToZ auxArc source) +
    if aToQ arc source then canonicalOutsideNeed auxArc 0 else 0

def canonicalFullNonSeymour (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  all 7 fun h => (canonicalFullSecondCount arc pToZ auxArc (1 + h)).ult
    (aDegree arc (1 + h))

def canonicalAuxiliaryCore (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  auxiliaryOriented arc pToZ auxArc &&
    (all 4 fun i => (auxNamedOut auxArc i).ule 8) &&
    canonicalHallConditions arc pToZ auxArc &&
    canonicalFullNonSeymour arc pToZ auxArc

def combinedAuxArc (auxArc extraAuxArc : Nat → Nat → Bool)
    (i target : Nat) : Bool :=
  auxArc i target || extraAuxArc i target

def actualNamedArc (arc pToZ realAuxArc : Nat → Nat → Bool)
    (middle target : Nat) : Bool :=
  if middle < 14 then
    if target < 18 then coreArc 3 arc pToZ middle target else false
  else if middle < 18 then realAuxArc (middle - 14) target
  else false

def actualReachesNamed (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p target : Nat) : Bool :=
  any 18 fun middle => decide (middle ≠ 8 + p) &&
    decide (middle ≠ target) && pDirect arc pToZ p middle &&
    actualNamedArc arc pToZ realAuxArc middle target

def actualSecondNamed (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p target : Nat) : Bool :=
  decide (target ≠ 8 + p) && !pDirect arc pToZ p target &&
    actualReachesNamed arc pToZ realAuxArc p target

def actualSlotReached (arc pToZ outsideArc : Nat → Nat → Bool)
    (p slot : Nat) : Bool :=
  any 4 fun i => pDirect arc pToZ p (14 + i) && outsideArc i slot

def actualSecondCount (arc pToZ realAuxArc outsideArc : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  count 19 (actualSecondNamed arc pToZ realAuxArc p) +
    count 7 (actualSlotReached arc pToZ outsideArc p)

def deletionReachesNamed (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p deleted target : Nat) : Bool :=
  any 18 fun middle => decide (middle ≠ 8 + p) &&
    decide (middle ≠ deleted) && decide (middle ≠ target) &&
    pDirect arc pToZ p middle &&
    actualNamedArc arc pToZ realAuxArc middle target

def deletionSecondNamed (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p deleted target : Nat) : Bool :=
  decide (target ≠ 8 + p) &&
    (if target = deleted then
      deletionReachesNamed arc pToZ realAuxArc p deleted target
    else
      !pDirect arc pToZ p target &&
        deletionReachesNamed arc pToZ realAuxArc p deleted target)

def deletionSlotReached (arc pToZ outsideArc : Nat → Nat → Bool)
    (p deleted slot : Nat) : Bool :=
  any 4 fun i => decide (14 + i ≠ deleted) &&
    pDirect arc pToZ p (14 + i) && outsideArc i slot

def deletionSecondCount (arc pToZ realAuxArc outsideArc : Nat → Nat → Bool)
    (p deleted : Nat) : BitVec 8 :=
  count 19 (deletionSecondNamed arc pToZ realAuxArc p deleted) +
    count 7 (deletionSlotReached arc pToZ outsideArc p deleted)

def actualAuxiliaryOriented (arc pToZ realAuxArc : Nat → Nat → Bool) : Bool :=
  (all 4 fun i => all 14 fun source =>
    !(incomingToAux arc pToZ source i && realAuxArc i source)) &&
  (all 4 fun i => all 4 fun j =>
    !(realAuxArc i (14 + j) && realAuxArc j (14 + i)))

def reachedSlotPrefix (arc pToZ outsideArc : Nat → Nat → Bool)
    (p : Nat) : Bool :=
  all 6 fun slot => !actualSlotReached arc pToZ outsideArc p (slot + 1) ||
    actualSlotReached arc pToZ outsideArc p slot

def deletionConditions (arc pToZ realAuxArc outsideArc : Nat → Nat → Bool)
    (p : Nat) : Bool :=
  all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted ||
      (7 : BitVec 8).ule
        (deletionSecondCount arc pToZ realAuxArc outsideArc p deleted)

def actualTailCore (p : Nat)
    (arc pToZ auxArc extraAuxArc outsideArc : Nat → Nat → Bool) : Bool :=
  canonicalAuxiliaryCore arc pToZ auxArc &&
    pDegree 1 3 arc pToZ p == 8 &&
    actualAuxiliaryOriented arc pToZ (combinedAuxArc auxArc extraAuxArc) &&
    reachedSlotPrefix arc pToZ outsideArc p &&
    (actualSecondCount arc pToZ (combinedAuxArc auxArc extraAuxArc)
      outsideArc p).ule 7 &&
    deletionConditions arc pToZ (combinedAuxArc auxArc extraAuxArc) outsideArc p

def actualCapacityLeaf (capacity : Nat)
    (arc pToZ auxArc extraAuxArc outsideArc : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    actualTailCore (6 - capacity) arc pToZ auxArc extraAuxArc outsideArc

def actualCapacityRangeLeaf (capacity lower upper : Nat)
    (arc pToZ auxArc extraAuxArc outsideArc : Nat → Nat → Bool) : Bool :=
  actualCapacityLeaf capacity arc pToZ auxArc extraAuxArc outsideArc &&
    (BitVec.ofNat 8 lower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 upper)

abbrev Encoding := Nat → Bool

def encodedArc (bits : Encoding) (i j : Nat) : Bool := bits (15 * i + j)
def encodedPToZ (bits : Encoding) (p z : Nat) : Bool := bits (210 + 4 * p + z)
def encodedAuxArc (bits : Encoding) (i target : Nat) : Bool :=
  bits (234 + 19 * i + target)
def encodedExtraAuxArc (bits : Encoding) (i target : Nat) : Bool :=
  bits (310 + 19 * i + target)
def encodedOutsideArc (bits : Encoding) (i slot : Nat) : Bool :=
  bits (386 + 7 * i + slot)

def encodedCapacityRangeLeaf (capacity lower upper : Nat)
    (bits : Encoding) : Bool :=
  actualCapacityRangeLeaf capacity lower upper (encodedArc bits)
    (encodedPToZ bits) (encodedAuxArc bits) (encodedExtraAuxArc bits)
    (encodedOutsideArc bits)

def actualDefectLeaf (m delta d : Nat)
    (arc pToZ auxArc extraAuxArc outsideArc : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc + internalMissing arc == BitVec.ofNat 8 d &&
    actualTailCore (6 - (m + 2 * delta + d)) arc pToZ auxArc
      extraAuxArc outsideArc

def zeroCapacityLeaf (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && canonicalAuxiliaryCore arc pToZ auxArc &&
    capacityDefect arc pToZ == 0

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ActualTail
