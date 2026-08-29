import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# One-defect high-defect three-`Z` core

The remaining `m=2`, degree-sum-56 cases have exactly one absent orientation,
either inside `P` or between `P` and `H`.  The exceptional unordered pair is
stored as a small binary index, so all other pairs still require only one
orientation bit.
-/

namespace SeymourEight.ThreeZNearSaturated

open FiveZExactRisk

abbrev Encoding := BitVec 166

def upperIndex (i j : Nat) : Nat :=
  i * (13 - i) / 2 + (j - i - 1)

def pMissingCode (bits : Encoding) : BitVec 5 :=
  bits.extractLsb' 21 5

def phMissingCode (bits : Encoding) : BitVec 6 :=
  bits.extractLsb' 61 6

def pPairMissing (betaOne : Bool) (bits : Encoding) (i j : Nat) : Bool :=
  betaOne && (pMissingCode bits == BitVec.ofNat 5 (upperIndex i j))

def phPairMissing (alphaOne : Bool) (bits : Encoding) (i h : Nat) : Bool :=
  alphaOne && (phMissingCode bits == BitVec.ofNat 6 (i * 5 + h))

def pArc (betaOne : Bool) (bits : Encoding) (i j : Nat) : Bool :=
  if i = j then false
  else if i < j then
    !pPairMissing betaOne bits i j && bits.getLsbD (upperIndex i j)
  else
    !pPairMissing betaOne bits j i && !bits.getLsbD (upperIndex j i)

def pToH (alphaOne : Bool) (bits : Encoding) (i h : Nat) : Bool :=
  !phPairMissing alphaOne bits i h && bits.getLsbD (26 + i * 5 + h)

def hToP (alphaOne : Bool) (bits : Encoding) (h i : Nat) : Bool :=
  !phPairMissing alphaOne bits i h && !bits.getLsbD (26 + i * 5 + h)

def pToZ (bits : Encoding) (i z : Nat) : Bool :=
  bits.getLsbD (67 + i * 3 + z)

def rToP (bits : Encoding) (r i : Nat) : Bool :=
  bits.getLsbD (88 + r * 7 + i)

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (102 + i * 8 + j)

def aToP (alphaOne : Bool) (bits : Encoding) (a i : Nat) : Bool :=
  if a = 0 then true
  else if a < 6 then hToP alphaOne bits (a - 1) i
  else rToP bits (a - 6) i

def pToA (alphaOne : Bool) (bits : Encoding) (i a : Nat) : Bool :=
  if 0 < a && a < 6 then pToH alphaOne bits i (a - 1) else false

def coreArc (alphaOne betaOne : Bool) (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP alphaOne bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA alphaOne bits (u - 8) v
    else if v < 15 then pArc betaOne bits (u - 8) (v - 8)
    else if v < 18 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def coreOutdegree (alphaOne betaOne : Bool) (bits : Encoding)
    (u : Nat) : BitVec 8 :=
  count 18 (coreArc alphaOne betaOne bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def aPOut (alphaOne : Bool) (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 7 (aToP alphaOne bits a)

def totalPToH (alphaOne : Bool) (bits : Encoding) : BitVec 8 :=
  count 35 fun q => pToH alphaOne bits (q / 5) (q % 5)

def totalPOut (betaOne : Bool) (bits : Encoding) : BitVec 8 :=
  count 49 fun q => pArc betaOne bits (q / 7) (q % 7)

def totalMissingPZ (bits : Encoding) : BitVec 8 :=
  count 21 fun q => !pToZ bits (q / 3) (q % 3)

def pDegree (alphaOne betaOne : Bool) (bits : Encoding) (i : Nat) : BitVec 8 :=
  count 3 (pToZ bits i) + count 5 (pToH alphaOne bits i) +
    count 7 (pArc betaOne bits i)

def orderedP (alphaOne betaOne : Bool) (bits : Encoding) : Bool :=
  all 6 fun i =>
    (pDegree alphaOne betaOne bits (i + 1)).ule
        (pDegree alphaOne betaOne bits i) &&
      (!(pDegree alphaOne betaOne bits i ==
          pDegree alphaOne betaOne bits (i + 1)) ||
        (count 5 (pToH alphaOne bits (i + 1))).ule
          (count 5 (pToH alphaOne bits i)))

def zCode (bits : Encoding) (z : Nat) : BitVec 16 :=
  count16 7 fun i => bitCount16 (pToZ bits i z) <<< i

def orderedZ (bits : Encoding) : Bool :=
  all 2 fun z => (zCode bits (z + 1)).ule (zCode bits z)

def reachedFromA (alphaOne betaOne : Bool) (bits : Encoding)
    (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc alphaOne betaOne bits source middle &&
      coreArc alphaOne betaOne bits middle target

def secondFromA (alphaOne betaOne : Bool) (bits : Encoding)
    (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc alphaOne betaOne bits source target &&
    reachedFromA alphaOne betaOne bits source target

def aSecondCount (alphaOne betaOne : Bool) (bits : Encoding)
    (source : Nat) : BitVec 8 :=
  count 18 (secondFromA alphaOne betaOne bits source)

def aNonSeymour (alphaOne betaOne : Bool) (bits : Encoding)
    (source : Nat) : Bool :=
  (aSecondCount alphaOne betaOne bits source).ult
    (coreOutdegree alphaOne betaOne bits source)

def aOneNeighbor (d : Nat) : Nat :=
  if d = 0 then 1 else d + 7

def retainedAfterDelete (deleted vertex : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) && decide (vertex = aOneNeighbor d)

def deletionReached (alphaOne betaOne : Bool) (bits : Encoding)
    (deleted target : Nat) : Bool :=
  decide (target ≠ 0) && !retainedAfterDelete deleted target &&
    any 18 fun middle => retainedAfterDelete deleted middle &&
      coreArc alphaOne betaOne bits middle target

def deletionExpansionCount (alphaOne betaOne : Bool) (bits : Encoding)
    (deleted : Nat) : BitVec 8 :=
  count 18 (deletionReached alphaOne betaOne bits deleted)

def aOneDeletionExpands (alphaOne betaOne : Bool) (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule
      (deletionExpansionCount alphaOne betaOne bits deleted)

/-- The four represented X targets followed by the three represented Z
targets.  Every other possible deletion-expansion target is either retained,
the root, or unreachable from the retained neighbors by `fixedStructure`. -/
def deletionExternalTarget (q : Nat) : Nat :=
  if q < 4 then q + 2 else q + 11

def reachedFromRetainedNeighbor (alphaOne betaOne : Bool) (bits : Encoding)
    (deleted target : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) &&
    coreArc alphaOne betaOne bits (aOneNeighbor d) target

def compactDeletionExpansionCount (alphaOne betaOne : Bool) (bits : Encoding)
    (deleted : Nat) : BitVec 8 :=
  count 7 (fun q => reachedFromRetainedNeighbor alphaOne betaOne bits deleted
      (deletionExternalTarget q)) +
    bitCount (reachedFromRetainedNeighbor alphaOne betaOne bits deleted
      (aOneNeighbor deleted))

def compactAOneDeletionExpands (alphaOne betaOne : Bool)
    (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule
      (compactDeletionExpansionCount alphaOne betaOne bits deleted)

def fixedStructure (alphaOne betaOne : Bool) (bits : Encoding) : Bool :=
  orientedSquare 18 (coreArc alphaOne betaOne bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 2 (fun q => !aArc bits 1 (q + 6)) &&
  (aArc bits 1 2 || any 7 (fun i => pToH alphaOne bits i 1)) &&
  (aArc bits 1 3 || any 7 (fun i => pToH alphaOne bits i 2)) &&
  (aArc bits 1 4 || any 7 (fun i => pToH alphaOne bits i 3)) &&
  (aArc bits 1 5 || any 7 (fun i => pToH alphaOne bits i 4)) &&
  all 8 (fun a => (1 : BitVec 8).ule (aOut bits a)) &&
  all 7 (fun q => !(aOut bits (q + 1) = 1) ||
    (7 : BitVec 8).ule (aPOut alphaOne bits (q + 1))) &&
  all 15 (fun u =>
    (8 : BitVec 8).ule (coreOutdegree alphaOne betaOne bits u)) &&
  all 3 (fun z => any 7 (fun i => pToZ bits i z))

def nearSaturatedCore (alphaOne betaOne : Bool) (bits : Encoding) : Bool :=
  (!alphaOne || (phMissingCode bits).ult 35) &&
  (!betaOne || (pMissingCode bits).ult 21) &&
  fixedStructure alphaOne betaOne bits &&
  aOneDeletionExpands alphaOne betaOne bits &&
  totalPToH alphaOne bits + bitCount alphaOne = 17 &&
  totalPOut betaOne bits + bitCount betaOne = 21 &&
  totalMissingPZ bits = 2 &&
  all 7 (fun q => aNonSeymour alphaOne betaOne bits (q + 1)) &&
  all 7 (fun q => aNonSeymour alphaOne betaOne bits (q + 8)) &&
  orderedP alphaOne betaOne bits && orderedZ bits

def compactNearSaturatedCore (alphaOne betaOne : Bool)
    (bits : Encoding) : Bool :=
  (!alphaOne || (phMissingCode bits).ult 35) &&
  (!betaOne || (pMissingCode bits).ult 21) &&
  fixedStructure alphaOne betaOne bits &&
  compactAOneDeletionExpands alphaOne betaOne bits &&
  totalPToH alphaOne bits + bitCount alphaOne = 17 &&
  totalPOut betaOne bits + bitCount betaOne = 21 &&
  totalMissingPZ bits = 2 &&
  all 7 (fun p => pDegree alphaOne betaOne bits p == 8) &&
  all 7 (fun q => aNonSeymour alphaOne betaOne bits (q + 1)) &&
  all 7 (fun q => aNonSeymour alphaOne betaOne bits (q + 8)) &&
  orderedP alphaOne betaOne bits && orderedZ bits

end SeymourEight.ThreeZNearSaturated
