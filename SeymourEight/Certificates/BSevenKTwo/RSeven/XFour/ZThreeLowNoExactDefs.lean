import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore

open ZThreeCore

def commonCoreNoExact (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && allZReached bits &&
    (totalPToH bits).ule 17 && (totalPOut bits).ule 21 &&
    (25 : BitVec 8).ule (totalHToP bits) &&
    lowPConditions bits && generalSharpKing bits && orderedH bits

def mZeroNoExactCore (bits : Encoding) : Bool :=
  commonCoreNoExact bits && totalPToZ bits == 21 &&
    (35 : BitVec 8).ule (totalPToH bits + totalPOut bits) &&
    mZeroExternal bits && orderedRowsFrom bits 0 6

def mOneNoExactCore (bits : Encoding) : Bool :=
  commonCoreNoExact bits && totalPToZ bits == 20 &&
    (36 : BitVec 8).ule (totalPToH bits + totalPOut bits) &&
    mOneExternal bits && orderedRowsFrom bits 1 5

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore
