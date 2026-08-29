import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Saturated high-defect three-`Z` core

When both the `P → H` and internal-`P` defects vanish, orientation and the
capacity equalities say that every `P` pair and every `P`/`H` pair has exactly
one direction.  Encoding only that direction removes 49 redundant bits from
the general high-defect core.
-/

namespace SeymourEight.ThreeZSaturated

open FiveZExactRisk

abbrev Encoding := BitVec 155

/-- Index of the unordered pair `{i,j}` in the upper triangle of a seven by
seven matrix.  This is used only with `i < j < 7`. -/
def upperIndex (i j : Nat) : Nat :=
  i * (13 - i) / 2 + (j - i - 1)

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  if i = j then false
  else if i < j then bits.getLsbD (upperIndex i j)
  else !bits.getLsbD (upperIndex j i)

def pToH (bits : Encoding) (i h : Nat) : Bool :=
  bits.getLsbD (21 + i * 5 + h)

def hToP (bits : Encoding) (h i : Nat) : Bool :=
  !pToH bits i h

def pToZ (bits : Encoding) (i z : Nat) : Bool :=
  bits.getLsbD (56 + i * 3 + z)

def rToP (bits : Encoding) (r i : Nat) : Bool :=
  bits.getLsbD (77 + r * 7 + i)

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (91 + i * 8 + j)

def aToP (bits : Encoding) (a i : Nat) : Bool :=
  if a = 0 then true
  else if a < 6 then hToP bits (a - 1) i
  else rToP bits (a - 6) i

def pToA (bits : Encoding) (i a : Nat) : Bool :=
  if 0 < a && a < 6 then pToH bits i (a - 1) else false

def coreArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 18 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def coreOutdegree (bits : Encoding) (u : Nat) : BitVec 8 :=
  count 18 (coreArc bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def aPOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 7 (aToP bits a)

def totalPToH (bits : Encoding) : BitVec 8 :=
  count 35 fun q => pToH bits (q / 5) (q % 5)

def totalMissingPZ (bits : Encoding) : BitVec 8 :=
  count 21 fun q => !pToZ bits (q / 3) (q % 3)

def pDegree (bits : Encoding) (i : Nat) : BitVec 8 :=
  count 3 (pToZ bits i) + count 5 (pToH bits i) + count 7 (pArc bits i)

def orderedP (bits : Encoding) : Bool :=
  all 6 fun i =>
    (pDegree bits (i + 1)).ule (pDegree bits i) &&
      (!(pDegree bits i == pDegree bits (i + 1)) ||
        (count 5 (pToH bits (i + 1))).ule (count 5 (pToH bits i)))

def zCode (bits : Encoding) (z : Nat) : BitVec 16 :=
  count16 7 fun i => bitCount16 (pToZ bits i z) <<< i

def orderedZ (bits : Encoding) : Bool :=
  all 2 fun z => (zCode bits (z + 1)).ule (zCode bits z)

def reachedFromA (bits : Encoding) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc bits source middle && coreArc bits middle target

def secondFromA (bits : Encoding) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachedFromA bits source target

def aSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 18 (secondFromA bits source)

def aNonSeymour (bits : Encoding) (source : Nat) : Bool :=
  (aSecondCount bits source).ult (coreOutdegree bits source)

def aOneNeighbor (d : Nat) : Nat :=
  if d = 0 then 1 else d + 7

def retainedAfterDelete (deleted vertex : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) && decide (vertex = aOneNeighbor d)

def deletionReached (bits : Encoding) (deleted target : Nat) : Bool :=
  decide (target ≠ 0) && !retainedAfterDelete deleted target &&
    any 18 fun middle =>
      retainedAfterDelete deleted middle && coreArc bits middle target

def deletionExpansionCount (bits : Encoding) (deleted : Nat) : BitVec 8 :=
  count 18 (deletionReached bits deleted)

def aOneDeletionExpands (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule (deletionExpansionCount bits deleted)

def deletionExternalTarget (q : Nat) : Nat :=
  if q < 4 then q + 2 else q + 11

def reachedFromRetainedNeighbor (bits : Encoding)
    (deleted target : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) &&
    coreArc bits (aOneNeighbor d) target

def compactDeletionExpansionCount (bits : Encoding)
    (deleted : Nat) : BitVec 8 :=
  count 7 (fun q => reachedFromRetainedNeighbor bits deleted
      (deletionExternalTarget q)) +
    bitCount (reachedFromRetainedNeighbor bits deleted
      (aOneNeighbor deleted))

def compactAOneDeletionExpands (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule (compactDeletionExpansionCount bits deleted)

def fixedStructure (bits : Encoding) : Bool :=
  orientedSquare 18 (coreArc bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 2 (fun q => !aArc bits 1 (q + 6)) &&
  (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) &&
  (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) &&
  (aArc bits 1 4 || any 7 (fun i => pToH bits i 3)) &&
  (aArc bits 1 5 || any 7 (fun i => pToH bits i 4)) &&
  all 8 (fun a => (1 : BitVec 8).ule (aOut bits a)) &&
  all 7 (fun q =>
    !(aOut bits (q + 1) = 1) || (7 : BitVec 8).ule (aPOut bits (q + 1))) &&
  all 15 (fun u => (8 : BitVec 8).ule (coreOutdegree bits u)) &&
  all 3 (fun z => any 7 (fun i => pToZ bits i z))

def saturatedCoreAtMissingPToH (missing pToHTotal : Nat)
    (bits : Encoding) : Bool :=
  fixedStructure bits && aOneDeletionExpands bits &&
  totalPToH bits = BitVec.ofNat 8 pToHTotal &&
  totalMissingPZ bits = BitVec.ofNat 8 missing &&
  all 7 (fun q => aNonSeymour bits (q + 1)) &&
  all 7 (fun q => aNonSeymour bits (q + 8)) && orderedP bits && orderedZ bits

def saturatedCoreAtMissing (missing : Nat) (bits : Encoding) : Bool :=
  saturatedCoreAtMissingPToH missing 17 bits

/-- Compact deletion form for the degree-sum-56 saturated rows.  In these
rows the seven lower bounds on P degrees sum to their exact total, so every P
degree is eight. -/
def compactSaturatedCoreAtMissingPToH (missing pToHTotal : Nat)
    (bits : Encoding) : Bool :=
  fixedStructure bits && compactAOneDeletionExpands bits &&
  totalPToH bits = BitVec.ofNat 8 pToHTotal &&
  totalMissingPZ bits = BitVec.ofNat 8 missing &&
  all 7 (fun p => pDegree bits p == 8) &&
  all 7 (fun q => aNonSeymour bits (q + 1)) &&
  all 7 (fun q => aNonSeymour bits (q + 8)) &&
  orderedP bits && orderedZ bits

def compactSaturatedCoreAtMissing (missing : Nat) (bits : Encoding) : Bool :=
  compactSaturatedCoreAtMissingPToH missing 17 bits

end SeymourEight.ThreeZSaturated
