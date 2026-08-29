import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourCoreDefs

/-!
# Low-defect strengthening of the broad four-`Z` core

At external defect zero the common auxiliary union has cardinality at least
eight (proved at graph level using the degree-seven theorem).  Defects one
and two use the individual effective-target bound unchanged.  This small
conditional strengthening lets one certificate cover all three low-defect
rows.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore

open BroadFourCore

def pHIn (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 7 fun p => pToH bits p h

def hRowKey (bits : Encoding) (h : Nat) : BitVec 8 :=
  16 * hPOut bits h + pHIn bits h

/-- Symmetry-safe ordering inside the two structurally interchangeable
`A1` vertices and the four structurally interchangeable `X` vertices. -/
def orderedHClasses (bits : Encoding) : Bool :=
  (hRowKey bits 1).ule (hRowKey bits 0) &&
    all 3 fun i => (hRowKey bits (i + 3)).ule (hRowKey bits (i + 2))

def lowEffectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  if externalMissing bits == 0 then 8 else individualEffectiveLower bits p

def pLowEffectiveCondition (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + lowEffectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut bits p)

def lowCore (bits : Encoding) : Bool :=
  broadCore bits && (externalMissing bits).ule 2 &&
    all 7 (pLowEffectiveCondition bits)

def pZMissingExactly (bits : Encoding)
    (p₀ z₀ p₁ z₁ : Nat) : Bool :=
  all 28 fun q =>
    let p := q / 4
    let z := q % 4
    pToZ bits p z == !((p == p₀ && z == z₀) ||
      (p == p₁ && z == z₁))

def pZMissingOne (bits : Encoding) (p₀ z₀ : Nat) : Bool :=
  all 28 fun q =>
    let p := q / 4
    let z := q % 4
    pToZ bits p z == !(p == p₀ && z == z₀)

/-- Canonical representatives forced by descending row/column counts.  The
disjoint orbit retains its two matchings, since the degree ordering does not
couple equal rows to equal columns. -/
def canonicalMTwoTail (bits : Encoding) : Bool :=
  pZMissingExactly bits 6 2 6 3 ||
  pZMissingExactly bits 5 3 6 3 ||
  pZMissingExactly bits 5 2 6 3 ||
  pZMissingExactly bits 5 3 6 2

def canonicalMOneTail (bits : Encoding) : Bool :=
  pZMissingOne bits 6 3

def fullPToZ (bits : Encoding) : Bool :=
  all 28 fun q => pToZ bits (q / 4) (q % 4)

/-- Five genuine low-defect incidence orbits.  The second disjoint matching is
removed by the full-column tie breaker below. -/
def selectedLowPattern (mode : BitVec 3) (bits : Encoding) : Bool :=
  if mode == 0 then fullPToZ bits
  else if mode == 1 then pZMissingOne bits 6 3
  else if mode == 2 then pZMissingExactly bits 6 2 6 3
  else if mode == 3 then pZMissingExactly bits 5 3 6 3
  else if mode == 4 then pZMissingExactly bits 5 2 6 3
  else if mode == 5 then (3 : BitVec 8).ule (externalMissing bits)
  else false

def pZIncidenceCode (bits : Encoding) (z : Nat) : BitVec 7 :=
  (if pToZ bits 0 z then 1 else 0) +
  (if pToZ bits 1 z then 2 else 0) +
  (if pToZ bits 2 z then 4 else 0) +
  (if pToZ bits 3 z then 8 else 0) +
  (if pToZ bits 4 z then 16 else 0) +
  (if pToZ bits 5 z then 32 else 0) +
  (if pToZ bits 6 z then 64 else 0)

def zFullKey (bits : Encoding) (z : Nat) : BitVec 16 :=
  (zColumnCode bits z).zeroExtend 16 * 128 +
    (pZIncidenceCode bits z).zeroExtend 16

def orderedZFull (bits : Encoding) : Bool :=
  all 3 fun z => (zFullKey bits (z + 1)).ule (zFullKey bits z)

/-- Exact low-defect slice used by the decomposed finite cover. -/
def mTwoCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 2 &&
    canonicalMTwoTail bits

def mTwoSameRowCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 2 &&
    pZMissingExactly bits 6 2 6 3

def mTwoSameColumnCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 2 &&
    pZMissingExactly bits 5 3 6 3

def mTwoDisjointACore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 2 &&
    pZMissingExactly bits 5 2 6 3

def mTwoDisjointBCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 2 &&
    pZMissingExactly bits 5 3 6 2

/-- Scalar cutting-plane slices corresponding to the hand low-defect
argument. -/
def lowHPBounds (bits : Encoding) : Bool :=
  orderedHClasses bits && (25 : BitVec 8).ule (totalHToP bits) &&
    (totalHToP bits + externalMissing bits).ule 35

def selectedLowPatternCore (mode : BitVec 3) (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && lowHPBounds bits &&
    orderedZFull bits && selectedLowPattern mode bits

def mTwoHPLowCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && lowHPBounds bits &&
    externalMissing bits == 2 &&
    (totalHToP bits).ule 29

def mTwoPHLowCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 2 &&
    (totalPToH bits).ule 15

def mOnePHLowCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 1 &&
    (totalPToH bits).ule 14

def pProjectedCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits

def mTwoPHProjectedLowCore (bits : Encoding) : Bool :=
  pProjectedCore bits && lowHPBounds bits && externalMissing bits == 2 &&
    canonicalMTwoTail bits &&
    (30 : BitVec 8).ule (totalHToP bits) &&
    (totalPToH bits).ule 15

def mOnePHProjectedLowCore (bits : Encoding) : Bool :=
  pProjectedCore bits && externalMissing bits == 1 &&
    (28 : BitVec 8).ule (totalHToP bits) &&
    (totalPToH bits).ule 14

def mOneHPLowCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && lowHPBounds bits &&
    externalMissing bits == 1 && canonicalMOneTail bits &&
    (totalHToP bits).ule 31

def mOneHPHighCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && lowHPBounds bits &&
    externalMissing bits == 1 && canonicalMOneTail bits &&
    (32 : BitVec 8).ule (totalHToP bits)

def mZeroHPLowCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && lowHPBounds bits &&
    externalMissing bits == 0 && (totalHToP bits).ule 32

def mZeroHPHighCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && lowHPBounds bits &&
    externalMissing bits == 0 &&
    (33 : BitVec 8).ule (totalHToP bits)

/-- The remaining positive low-defect slice. -/
def mOneCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 1 &&
    canonicalMOneTail bits

/-- The fully saturated zero-defect slice. -/
def mZeroCore (bits : Encoding) : Bool :=
  broadCore bits && sharpKing bits && externalMissing bits == 0

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore
