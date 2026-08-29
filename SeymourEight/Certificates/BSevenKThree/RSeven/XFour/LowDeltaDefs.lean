import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.RemainingDefs

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore

open Core

/-- The aggregate scalar cut implied by the seven minimum-`P`-degree
conditions and the `P`--`H` cross-edge bound. -/
def directScalarCut (bits : Encoding) : Bool :=
  (externalMissing 5 bits + 3 * aMissing bits + alpha bits +
    internalMissing bits).ule 12

def deltaZeroAllLeaf (bits : Encoding) : Bool :=
  boxLeaf 0 12 0 0 0 12 bits && directScalarCut bits

def deltaOneAllLeaf (bits : Encoding) : Bool :=
  boxLeaf 0 9 1 1 0 9 bits && directScalarCut bits

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore
