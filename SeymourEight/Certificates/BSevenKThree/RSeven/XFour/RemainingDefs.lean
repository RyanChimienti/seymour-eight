import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.SymmetryDefs

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore

open Core SymmetricCore

/-- A rectangular interval in the three scalar defects after canonical
relabeling.  This tail is independent of the symmetry predicate and can be
combined with either hard-parent interval. -/
def boxLeaf (mLo mHi deltaLo deltaHi dLo dHi : Nat)
    (bits : Encoding) : Bool :=
  symmetricCore bits &&
    (BitVec.ofNat 8 mLo).ule (externalMissing 5 bits) &&
    (externalMissing 5 bits).ule (BitVec.ofNat 8 mHi) &&
    (BitVec.ofNat 8 deltaLo).ule (aMissing bits) &&
    (aMissing bits).ule (BitVec.ofNat 8 deltaHi) &&
    (BitVec.ofNat 8 dLo).ule (alpha bits + internalMissing bits) &&
    (alpha bits + internalMissing bits).ule (BitVec.ofNat 8 dHi)

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore
