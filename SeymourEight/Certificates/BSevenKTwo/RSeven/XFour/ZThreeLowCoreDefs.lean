import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeCoreDefs

/-!
# Projected low-defect cores for the three-`Z` row

These retain the same `P`, `P`--`H`, and `P`--`Z` projection as the
external-defect-two core.  At defect one the unique exceptional row has two
direct `Z` neighbors and hence at least eight effective targets; all other
rows, and every row at defect zero, have the usual lower bound seven.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore

open ZThreeCore

def externalMissing (bits : Encoding) : BitVec 8 := 21 - totalPToZ bits

def lowEffectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  if externalMissing bits == 1 && pZOut bits p == 2 then 8 else 7

def lowPConditions (bits : Encoding) : Bool := all 7 fun p =>
  (8 : BitVec 8).ule (pDegree bits p) &&
  (pSecondCount bits p + lowEffectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut bits p)

def sharpKingLower (missing : BitVec 8) : BitVec 8 :=
  if missing == 0 then 6 else if missing.ule 2 then 5
  else if missing.ule 5 then 4 else if missing.ule 9 then 3
  else if missing.ule 14 then 2 else if missing.ule 20 then 1 else 0

def generalSharpKing (bits : Encoding) : Bool :=
  any 7 fun p => (sharpKingLower (21 - totalPOut bits)).ule
    (pOut bits p + pSecondCount bits p)

def rowKey (bits : Encoding) (p : Nat) : BitVec 16 :=
  (pDegree bits p).zeroExtend 16 * 256 +
    (pOut bits p).zeroExtend 16 * 16 + (pHOut bits p).zeroExtend 16

def orderedRowsFrom (bits : Encoding) (start countRows : Nat) : Bool :=
  all countRows fun i =>
    (rowKey bits (start + i + 1)).ule (rowKey bits (start + i))

def orderedH (bits : Encoding) : Bool :=
  all 5 fun h => lexGe 14 (phColumnBit bits h) (phColumnBit bits (h + 1))

def mZeroExternal (bits : Encoding) : Bool :=
  all 7 fun p => pZPattern bits p true true true

def mOneExternal (bits : Encoding) : Bool :=
  pZPattern bits 0 false true true &&
    all 6 fun i => pZPattern bits (i + 1) true true true

def commonCore (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && allZReached bits &&
    (totalPToH bits).ule 17 && (totalPOut bits).ule 21 &&
    (25 : BitVec 8).ule (totalHToP bits) &&
    lowPConditions bits && generalSharpKing bits && exactClassKing bits &&
    orderedH bits

def mZeroCore (bits : Encoding) : Bool :=
  commonCore bits && totalPToZ bits == 21 &&
    (35 : BitVec 8).ule (totalPToH bits + totalPOut bits) &&
    mZeroExternal bits && orderedRowsFrom bits 0 6

def mOneCore (bits : Encoding) : Bool :=
  commonCore bits && totalPToZ bits == 20 &&
    (36 : BitVec 8).ule (totalPToH bits + totalPOut bits) &&
    mOneExternal bits && orderedRowsFrom bits 1 5

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore
