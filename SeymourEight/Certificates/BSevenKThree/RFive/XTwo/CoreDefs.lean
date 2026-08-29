import SeymourEight.Certificates.BSixKThree.CoreDefs

/-!
# Compact core for `r = 5`, `x = 2`

The local vertices are `A = 0..7`, `P = 8..12`, and `Q = 13..14`.
External targets are represented by a separate five-row incidence array.
-/

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core

open SeymourEight.BSixKThreeCore

def localOut (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 15 (arc u)

def internalA (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 8 (arc u)

def outB (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 7 fun j ↦ arc u (8 + j)

def reachedLocal (arc : Nat → Nat → Bool) (u t : Nat) : Bool :=
  anyN 15 fun m ↦ decide (m ≠ u) && decide (m ≠ t) && arc u m && arc m t

def secondLocal (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 15 fun t ↦ decide (t ≠ u) && !arc u t && reachedLocal arc u t

def reachedExternal (arc externalArc : Nat → Nat → Bool)
    (u t : Nat) : Bool :=
  anyN 5 fun i ↦ arc u (8 + i) && externalArc i t

def representedSecondCount (active : Nat)
    (arc externalArc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  secondLocal arc u + sumN active (reachedExternal arc externalArc u)

def reachedExternalStrict (arc externalArc : Nat → Nat → Bool)
    (u t : Nat) : Bool :=
  !externalArc (u - 8) t && reachedExternal arc externalArc u t

def representedPSecondCount (active : Nat)
    (arc externalArc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  secondLocal arc u + sumN active (reachedExternalStrict arc externalArc u)

def innerReaches (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  anyN 8 fun middle ↦ decide (middle ≠ source) && decide (middle ≠ target) &&
    arc source middle && arc middle target

def innerSecond (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target && innerReaches arc source target

def innerSecondCount (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  sumN 8 (innerSecond arc source)

def innerSeymour (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  (internalA arc source).ule (innerSecondCount arc source)

def degreeThree (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  internalA arc source == 3

def degreeThreeInner (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  degreeThree arc source && innerSeymour arc source

def degreeThreeClassification (arc : Nat → Nat → Bool) : Bool :=
  allN 8 fun source ↦ allN 8 fun target ↦ decide (source = target) ||
    !degreeThree arc source || degreeThreeInner arc source ||
    !arc source target || degreeThreeInner arc target

def threeInnerWitnesses (arc : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (sumN 8 (degreeThreeInner arc))

def aPOut (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  sumN 5 fun p ↦ arc source (8 + p)

def hallReached (arc externalArc : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  anyN 5 fun p ↦ arc source (8 + p) && externalArc p target

def hallCount (arc externalArc : Nat → Nat → Bool)
    (source : Nat) : BitVec 8 :=
  sumN 3 (hallReached arc externalArc source)

def qOut (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  sumN 2 fun q ↦ arc source (13 + q)

def hToQ (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCountsN 5 fun h ↦ qOut arc (1 + h)

def pToQ (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCountsN 5 fun p ↦ qOut arc (8 + p)

def qAnonymousDefect (arc : Nat → Nat → Bool) : BitVec 8 :=
  (10 - hToQ arc) + (10 - pToQ arc)

/-- With two reached Q vertices and three named external targets, the two Q
rows have at least `ceil ((3 - defect) / 2)` common anonymous mass. -/
def qAnonymousLower (arc : Nat → Nat → Bool) : BitVec 8 :=
  let d := qAnonymousDefect arc
  if d == 0 then 2 else if d.ule 2 then 1 else 0

def reachesBothQ (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  arc source 13 && arc source 14

def hallCondition (arc externalArc : Nat → Nat → Bool)
    (source : Nat) : Bool :=
  !innerSeymour arc source || qOut arc source == 1 ||
    (hallCount arc externalArc source +
      (if reachesBothQ arc source then qAnonymousLower arc else 0#8)).ult
        (aPOut arc source + qOut arc source)

def augmentedNonSeymour (arc externalArc : Nat → Nat → Bool)
    (source : Nat) : Bool :=
  (representedSecondCount 3 arc externalArc source +
    (if reachesBothQ arc source then qAnonymousLower arc else 0#8)).ult
      (localOut arc source)

def pivotRow (arc : Nat → Nat → Bool) (u : Nat) : Bool :=
  (3 : BitVec 8).ule (internalA arc u) &&
    ((3 : BitVec 8).ult (internalA arc u) ||
      (5 : BitVec 8).ule (outB arc u))

def qReached (arc : Nat → Nat → Bool) (q : Nat) : Bool :=
  anyN 3 (fun i ↦ arc (1 + i) (13 + q)) ||
    anyN 5 (fun i ↦ arc (8 + i) (13 + q))

def core (active y : Nat) (arc externalArc : Nat → Nat → Bool) : Bool :=
  (allN 15 fun i ↦ !arc i i && allN 15 fun j ↦
    decide (i = j) || !(arc i j && arc j i)) &&
  (allN 15 fun j ↦
    arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 13)) &&
  (allN 3 fun i ↦ allN 2 fun j ↦ !arc (1 + i) (6 + j)) &&
  (allN 5 fun i ↦ allN 2 fun j ↦ !arc (8 + i) (6 + j)) &&
  (sumN 2 (qReached arc) == BitVec.ofNat 8 y) &&
  (allN 5 fun h ↦ pivotRow arc (1 + h) &&
    (8 : BitVec 8).ule (localOut arc (1 + h))) &&
  (allN 5 fun p ↦ (8 : BitVec 8).ule
    (localOut arc (8 + p) + sumN active (externalArc p))) &&
  (allN 6 fun i ↦
    (representedSecondCount active arc externalArc i).ult (localOut arc i))

def hardCore (arc externalArc : Nat → Nat → Bool) : Bool :=
  core 3 2 arc externalArc &&
  degreeThreeClassification arc &&
  threeInnerWitnesses arc &&
  (allN 3 fun a ↦ degreeThreeInner arc (1 + a)) &&
  (allN 8 fun source ↦ hallCondition arc externalArc source) &&
  (allN 6 fun source ↦ augmentedNonSeymour arc externalArc source) &&
  (allN 2 fun r ↦
    (representedSecondCount 3 arc externalArc (6 + r)).ult
      (localOut arc (6 + r))) &&
  (allN 5 fun p ↦
    (representedPSecondCount 3 arc externalArc (8 + p)).ult
      (localOut arc (8 + p) + sumN 3 (externalArc p)))

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core
