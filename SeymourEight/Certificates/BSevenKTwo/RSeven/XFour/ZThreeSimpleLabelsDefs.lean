import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeSimpleLabels

open ZThreeCore

def simpleRowsOrdered (bits : Encoding) (start n : Nat) : Bool :=
  all n fun i =>
    let left := start + i
    let right := start + i + 1
    (pDegree bits right).ule (pDegree bits left) &&
      (if pDegree bits left == pDegree bits right then
        (pOut bits right).ule (pOut bits left) &&
          (if pOut bits left == pOut bits right then
            (pHOut bits right).ule (pHOut bits left)
          else true)
      else true)

def simpleLabels (orbit : Nat) (bits : Encoding) : Bool :=
  (if orbit = 0 then simpleRowsOrdered bits 1 5
   else simpleRowsOrdered bits 0 1 && simpleRowsOrdered bits 2 4) &&
  all 5 fun h => lexGe 14 (phColumnBit bits h) (phColumnBit bits (h + 1))

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeSimpleLabels
