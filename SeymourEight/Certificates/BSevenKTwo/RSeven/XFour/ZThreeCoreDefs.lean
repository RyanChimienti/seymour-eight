import Std.Tactic.BVDecide

/-!
# Canonical corrected core for the three-`Z` row

The encoding retains only the `P` tournament, both directions of the `P`--`H`
incidences, and `P -> Z`.  Its canonical tail represents the three genuine
orbits of two missing incidences under relabeling of `P` and `Z`.  Within each
orbit it also fixes the remaining row and column labels and, when justified
by the exact-status king argument, its distinguished king.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeCore

abbrev Encoding := BitVec 147

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

def directedIndex (i j : Nat) : Nat := 6 * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (directedIndex i j)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (42 + 6 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  bits.getLsbD (84 + 7 * h + p)

def pToZ (bits : Encoding) (p z : Nat) : Bool :=
  bits.getLsbD (126 + 3 * p + z)

def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pToH bits p)
def pZOut (bits : Encoding) (p : Nat) : BitVec 8 := count 3 (pToZ bits p)

def pReached (bits : Encoding) (p q : Nat) : Bool :=
  pArc bits p q ||
    any 7 (fun middle => decide (middle ≠ p) && decide (middle ≠ q) &&
      pArc bits p middle && pArc bits middle q) ||
    any 6 (fun middle => pToH bits p middle && hToP bits middle q)

def pReachedWithinP (bits : Encoding) (p q : Nat) : Bool :=
  pArc bits p q ||
    any 7 (fun middle => decide (middle ≠ p) && decide (middle ≠ q) &&
      pArc bits p middle && pArc bits middle q)

def pReachWithinPCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => decide (p ≠ q) && pReachedWithinP bits p q

def pSecond (bits : Encoding) (p q : Nat) : Bool :=
  decide (p ≠ q) && !pArc bits p q && pReached bits p q

def pSecondCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 (pSecond bits p)

def pDegree (bits : Encoding) (p : Nat) : BitVec 8 :=
  pOut bits p + pHOut bits p + pZOut bits p

def pExact (bits : Encoding) (p : Nat) : Bool := pDegree bits p == 8

def exactCount (bits : Encoding) : BitVec 8 := count 7 (pExact bits)

def exactOutsideOut (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => decide (p != q) && !pExact bits q && pArc bits p q

def exactMissingPairs (bits : Encoding) : BitVec 8 :=
  count 21 fun q =>
    let i := q / 6
    let j0 := q % 6
    let j := if j0 < i then j0 else j0 + 1
    decide (i < j) && pExact bits i && pExact bits j &&
      !pArc bits i j && !pArc bits j i

def effectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  if pZOut bits p == 1 then 8 else 7

def orientedP (bits : Encoding) : Bool :=
  all 7 fun i => all 7 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)

def orientedPH (bits : Encoding) : Bool :=
  all 7 fun p => all 6 fun h => !(pToH bits p h && hToP bits h p)

def allZReached (bits : Encoding) : Bool :=
  all 3 fun z => any 7 fun p => pToZ bits p z

def totalPOut (bits : Encoding) : BitVec 8 := count 42 fun q =>
  let p := q / 6
  let j := q % 6
  pArc bits p (if j < p then j else j + 1)

def totalPToH (bits : Encoding) : BitVec 8 := count 42 fun q =>
  pToH bits (q / 6) (q % 6)

def totalHToP (bits : Encoding) : BitVec 8 := count 42 fun q =>
  hToP bits (q / 7) (q % 7)

def totalPToZ (bits : Encoding) : BitVec 8 := count 21 fun q =>
  pToZ bits (q / 3) (q % 3)

def pConditions (bits : Encoding) : Bool := all 7 fun p =>
  (8 : BitVec 8).ule (pDegree bits p) &&
  (pSecondCount bits p + effectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut bits p)

def sharpKing (beta : Nat) (bits : Encoding) : Bool :=
  any 7 fun p =>
    (if beta = 0 then (6 : BitVec 8) else 5).ule
      (pOut bits p + pSecondCount bits p)

def exactClassKing (bits : Encoding) : Bool :=
  any 7 fun p => pExact bits p &&
    (exactCount bits + pZOut bits p + effectiveLower bits p +
      exactOutsideOut bits p).ule (16 + exactMissingPairs bits)

def exactClassKingAt (bits : Encoding) (p : Nat) : Bool :=
  pExact bits p &&
    (exactCount bits + pZOut bits p + effectiveLower bits p +
      exactOutsideOut bits p).ule (16 + exactMissingPairs bits)

def firstExactClassKing (bits : Encoding) (start : Nat) : Bool :=
  if pExact bits start then exactClassKingAt bits start
  else exactClassKingAt bits (start + 1)

def core (alpha beta : Nat) (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && allZReached bits &&
  totalPToZ bits == 19 && totalPToH bits == 17 - alpha &&
  totalPOut bits == 21 - beta && (25 : BitVec 8).ule (totalHToP bits) &&
  pConditions bits && sharpKing beta bits && exactClassKing bits

def pZPattern (bits : Encoding) (p : Nat) (b0 b1 b2 : Bool) : Bool :=
  (pToZ bits p 0 == b0) && (pToZ bits p 1 == b1) &&
    (pToZ bits p 2 == b2)

/-- The three isomorphism types of two missing incidences in a seven-by-three
matrix: both in one row, two rows sharing a column, or two disjoint pairs. -/
def externalOrbit (orbit : Nat) (bits : Encoding) : Bool :=
  if orbit = 0 then
    pZPattern bits 0 false false true &&
      all 6 (fun i => pZPattern bits (i + 1) true true true)
  else if orbit = 1 then
    pZPattern bits 0 false true true &&
      pZPattern bits 1 false true true &&
      all 5 (fun i => pZPattern bits (i + 2) true true true)
  else
    pZPattern bits 0 false true true &&
      pZPattern bits 1 true false true &&
      all 5 (fun i => pZPattern bits (i + 2) true true true)

/-- In the all-exact tournament leaf, the exact-status inequality forces its
king into the deficient-row orbit; label that king `p0`. -/
def fixedStatusKing (alpha beta _orbit : Nat) (bits : Encoding) : Bool :=
  if alpha = 1 && beta = 0 then pReachWithinPCount bits 0 == 6 else true

def boolGe (a b : Bool) : Bool := a || !b

def phColumnBit (bits : Encoding) (h k : Nat) : Bool :=
  if k < 7 then pToH bits k h else hToP bits h (k - 7)

def lexGe : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0, _, _ => true
  | n + 1, left, right =>
      if left n == right n then lexGe n left right else left n

def saturatedRowsOrdered (bits : Encoding) (start i : Nat) : Bool :=
  let left := i + start
  let right := i + start + 1
  (pDegree bits right).ule (pDegree bits left) &&
    (if pDegree bits left == pDegree bits right then
      (pOut bits right).ule (pOut bits left) &&
        (if pOut bits left == pOut bits right then
          boolGe (pArc bits 0 left) (pArc bits 0 right) &&
            (if pArc bits 0 left == pArc bits 0 right then
              (pHOut bits right).ule (pHOut bits left)
            else true)
        else true)
    else true)

def deficientRowsOrdered (bits : Encoding) : Bool :=
  (pDegree bits 1).ule (pDegree bits 0) &&
    (if pDegree bits 0 == pDegree bits 1 then
      (pOut bits 1).ule (pOut bits 0)
    else true)

/-- Stabilizer normalization after the external orbit is fixed. -/
def canonicalLabels (_alpha _beta orbit : Nat) (bits : Encoding) : Bool :=
  (if orbit = 0 then all 5 (saturatedRowsOrdered bits 1)
    else deficientRowsOrdered bits && all 4 (saturatedRowsOrdered bits 2)) &&
    all 5 (fun h => lexGe 14 (phColumnBit bits h)
      (phColumnBit bits (h + 1)))

def canonicalClassKing (orbit : Nat) (bits : Encoding) : Bool :=
  if orbit = 0 then
    exactClassKingAt bits 0 || firstExactClassKing bits 1
  else
    firstExactClassKing bits 0 || firstExactClassKing bits 2

def exactClassKingReachAt (bits : Encoding) (p : Nat) : Bool :=
  exactClassKingAt bits p &&
    (5 : BitVec 8).ule (pReachWithinPCount bits p)

def canonicalReachedClassKing (alpha beta orbit : Nat)
    (bits : Encoding) : Bool :=
  if alpha = 0 && beta = 1 then
    if orbit = 0 then
      exactClassKingReachAt bits 0 || exactClassKingReachAt bits 1
    else
      exactClassKingReachAt bits 0 || exactClassKingReachAt bits 2
  else true

def orbitTail (alpha beta orbit : Nat) (bits : Encoding) : Bool :=
  externalOrbit orbit bits && fixedStatusKing alpha beta orbit bits &&
    canonicalLabels alpha beta orbit bits && canonicalClassKing orbit bits &&
    canonicalReachedClassKing alpha beta orbit bits

/-- One representative of each genuine external-incidence orbit, sharing the
same projected graph core. -/
def canonicalCore (alpha beta : Nat) (bits : Encoding) : Bool :=
  core alpha beta bits &&
    (orbitTail alpha beta 0 bits || orbitTail alpha beta 1 bits ||
      orbitTail alpha beta 2 bits)

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeCore
