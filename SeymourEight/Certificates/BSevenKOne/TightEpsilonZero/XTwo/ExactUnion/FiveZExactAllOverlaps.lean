import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

namespace SeymourEight.FiveZExactRisk

/-! The six possible intersections of `W` with `H=A1 ∪ X`. -/

/-- The `H` label represented by a `W` label, or sentinel `3` for none. -/
def overlapWToH (overlap a1In w : Nat) : Nat :=
  if a1In = 1 then
    if w < overlap then w else 3
  else if w < overlap then w + 1 else 3

def overlapHInW (overlap a1In h : Nat) : Bool :=
  if a1In = 1 then decide (h < overlap)
  else decide (1 ≤ h && h ≤ overlap)

def secondWOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (i w : Nat) : Bool :=
  let h := overlapWToH overlap a1In w
  reachesW bits i w && (decide (h = 3) || !pToH bits i h)

def secondOutsideHOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (i h : Nat) : Bool :=
  !overlapHInW overlap a1In h && reachesOutsideH bits i h && !pToH bits i h

def pNonSeymourOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (i : Nat) : Bool :=
  (secondPCount bits i + count 6 (secondWOverlap overlap a1In bits i) +
      count 3 (secondOutsideHOverlap overlap a1In bits i) +
      secondMissingZCount bits i).ult (pDegree bits i)

def reachesWFromZOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (source w : Nat) : Bool :=
  let h := overlapWToH overlap a1In w
  any 5 (fun middle =>
    decide (middle ≠ source) && zArc bits source middle && zToW bits middle w) ||
  (decide (h < 3) &&
    any 7 (fun middle => zToP bits source middle && pToH bits middle h))

def secondWFromZOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (source w : Nat) : Bool :=
  reachesWFromZOverlap overlap a1In bits source w && !zToW bits source w

def reachesPFromZOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (source target : Nat) : Bool :=
  any 6 (fun w =>
    let h := overlapWToH overlap a1In w
    decide (h < 3) && zToW bits source w && hToP bits h target) ||
  any 7 (fun middle =>
    decide (middle ≠ target) && zToP bits source middle && pArc bits middle target) ||
  any 5 (fun middle =>
    decide (middle ≠ source) && zArc bits source middle && zToP bits middle target)

def secondPFromZOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (source target : Nat) : Bool :=
  reachesPFromZOverlap overlap a1In bits source target && !zToP bits source target

def reachesOutsideHFromZOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (source h : Nat) : Bool :=
  !overlapHInW overlap a1In h &&
    any 7 (fun middle => zToP bits source middle && pToH bits middle h)

def zSecondCountOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (z : Nat) : BitVec 8 :=
  count 5 (secondZFromZ bits z) +
    count 6 (secondWFromZOverlap overlap a1In bits z) +
    count 7 (secondPFromZOverlap overlap a1In bits z) +
    count 3 (reachesOutsideHFromZOverlap overlap a1In bits z)

def zNonSeymourOverlap (overlap a1In : Nat) (bits : BitVec 280)
    (z : Nat) : Bool :=
  (zSecondCountOverlap overlap a1In bits z).ule (zDegree bits z)

def overlapRows (overlap a1In : Nat) (bits : BitVec 280) : Bool :=
  all 5 (fun z => zNonSeymourOverlap overlap a1In bits z) &&
  all 7 (fun i => pNonSeymourOverlap overlap a1In bits i)

def anyOverlapRows (bits : BitVec 280) : Bool :=
  overlapRows 0 0 bits || overlapRows 1 0 bits || overlapRows 2 0 bits ||
  overlapRows 1 1 bits || overlapRows 2 1 bits || overlapRows 3 1 bits

/-- A relaxation covering both union sizes six and seven.  In the latter
case one anonymous union vertex is omitted, hence the retained `Z` degree is
only required to be seven and the lower bound on its second neighbourhood is
only known to be at most that retained degree. -/
def familyCoreAnyOverlap (bits : BitVec 280) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits && orientedPZ bits &&
  orientedSquare 5 (zArc bits) &&
  (11 : BitVec 8).ule (totalHToP bits) &&
  (totalMissingPZ bits).ule 3 &&
  all 3 (fun h => (1 : BitVec 8).ule (hPOut bits h)) &&
  fixedAStructure bits &&
  all 6 (fun w => any 5 fun z => zToW bits z w) &&
  all 5 (fun z => (7 : BitVec 8).ule (zDegree bits z)) &&
  all 3 (hNonSeymour bits) && anyOverlapRows bits

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- All twelve exact union-six/seven overlap families are UNSAT. -/
theorem familyCoreAnyOverlap_unsat (bits : BitVec 280) :
    familyCoreAnyOverlap bits = false := by
  simp only [familyCoreAnyOverlap, anyOverlapRows, overlapRows,
    zNonSeymourOverlap, zSecondCountOverlap, reachesOutsideHFromZOverlap,
    secondPFromZOverlap, reachesPFromZOverlap, secondWFromZOverlap,
    reachesWFromZOverlap, pNonSeymourOverlap, secondOutsideHOverlap,
    secondWOverlap, overlapHInW, overlapWToH, secondZFromZ, reachesZFromZ,
    zDegree, fixedAStructure, hNonSeymour, hSecondCount, reachesZFromH,
    secondPFromH, reachesPFromH, secondAFromH, reachesAFromH, hDegree,
    aOut, pDegree, secondMissingZCount, secondMissingZ, reachesZFromP,
    reachesOutsideH, reachesW, secondPCount, secondPViaPOrH,
    reachedPViaPOrH, totalMissingPZ, totalHToP, zPOut, pZOut, hPOut,
    pHOut, pOut, orientedPZ, orientedPH, orientedSquare, zToW, zArc,
    aArc, zToP, pToZ, hToP, pToH, pArc, all, any, count, bitCount]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.FiveZExactRisk
