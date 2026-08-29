import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.SymmetryDefs

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourCore

open Core SymmetricCore Shared.FiniteCore

/-- The four-target core is stored in the same 221-bit layout, with its fifth
`P → Z` column forced to zero. -/
def commonCore (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits &&
    everyXReached bits && allZReached 4 bits && inactiveZZero 4 bits &&
    aMinimumAndDegree bits && all 8 (aNonSeymour 4 bits) &&
    pMinimumDegree 4 bits && all 7 (pEffectiveCondition bits) &&
    all 8 (hallCondition 4 bits) && all 8 (degreeThreeTieCondition bits) &&
    degreeThreeClassification bits && threeInnerWitnesses bits &&
    degreeAndDualConditions bits && sharpKing bits

def symmetricCore (bits : Encoding) : Bool :=
  commonCore bits && SymmetricCore.ordered bits

def boxLeaf (mLo mHi deltaLo deltaHi dLo dHi : Nat)
    (bits : Encoding) : Bool :=
  symmetricCore bits &&
    (BitVec.ofNat 8 mLo).ule (externalMissing 5 bits) &&
    (externalMissing 5 bits).ule (BitVec.ofNat 8 mHi) &&
    (BitVec.ofNat 8 deltaLo).ule (aMissing bits) &&
    (aMissing bits).ule (BitVec.ofNat 8 deltaHi) &&
    (BitVec.ofNat 8 dLo).ule (alpha bits + internalMissing bits) &&
    (alpha bits + internalMissing bits).ule (BitVec.ofNat 8 dHi)

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourCore
