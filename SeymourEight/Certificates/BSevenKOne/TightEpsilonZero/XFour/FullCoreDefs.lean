import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreDefs

/-!
# Full three-`Z` `P ∪ H` core

This is the compact core for the `m = 0` branch when the union of the
external `Z`-outneighborhoods has at least eight vertices.  All seven
vertices of `P` have three direct `Z`-neighbors, so their retained degree is
`3 + d⁺_H + d⁺_P`.  The external union gives the subtraction-free
non-Seymour inequality `q + 6 ≤ d⁺_P + 2 d⁺_H`.
-/

namespace SeymourEight.ThreeZFullCore

open TerminalCore

def retainedDegree (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  3 + pToHCount bits i + pOutCount bits i

def equationAt (bits : BitVec 119) (i : Nat) : Bool :=
  (secondPCount bits i + 6).ule
    (pOutCount bits i + 2 * pToHCount bits i)

def interchangeableOrdered (bits : BitVec 119) : Bool :=
  let orderedPair := fun i j ↦
    (retainedDegree bits j).ule (retainedDegree bits i) &&
      (!(retainedDegree bits i == retainedDegree bits j) ||
        (pToHCount bits j).ule (pToHCount bits i))
  orderedPair 0 1 && orderedPair 1 2 && orderedPair 2 3 &&
    orderedPair 3 4 && orderedPair 4 5 && orderedPair 5 6

def core (bits : BitVec 119) (alpha internalEdges degreeSum : BitVec 8) : Bool :=
  orientedOnP bits && orientedBetweenPAndH bits &&
  (totalPOut bits == internalEdges) &&
  (totalPToH bits + alpha == 17) &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  allSeven (fun i ↦
    (8 : BitVec 8).ule (retainedDegree bits i) &&
    (retainedDegree bits i).ule 11 && equationAt bits i) &&
  interchangeableOrdered bits &&
  (sumCountSeven (retainedDegree bits) == degreeSum)

end SeymourEight.ThreeZFullCore
