import Std.Tactic.BVDecide

/-!
# Boolean cores for the `(|B|, k) = (6, 2)` case

The core retains `H ∪ P`, the arcs from `X` to `{a₁} ∪ R`, and the arcs from
`P` to `Z` together with the optionally reached root.  Only the two vertices
of `A₁` carry non-Seymour inequalities.
-/

namespace SeymourEight.BSixKTwoCore

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def allN : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allN n p && p n

def anyN : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => anyN n p || p n

def sumN : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumN n p + bitCount (p n)

def sumCountsN : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumCountsN n p + p n

abbrev hSize (x : Nat) : Nat := 2 + x

def coreSize (x : Nat) : Nat := x + 8

def tSize (x : Nat) : Nat := 6 - x

def wSize (x : Nat) : Nat := 7 - x

def coreWidth (x : Nat) : Nat :=
  coreSize x * coreSize x + x * tSize x + 6 * wSize x

/-- The first square block records arcs within `H ∪ P`. -/
def arc {x : Nat} (bits : BitVec (coreWidth x)) (i j : Nat) : Bool :=
  bits.getLsbD (i * coreSize x + j)

/-- The second block records arcs from `X` to `{a₁} ∪ R`. -/
def xToT {x : Nat} (bits : BitVec (coreWidth x)) (i j : Nat) : Bool :=
  bits.getLsbD (coreSize x * coreSize x + i * tSize x + j)

/-- The final block records arcs from `P` to the external target set. -/
def pToW {x : Nat} (bits : BitVec (coreWidth x)) (i j : Nat) : Bool :=
  bits.getLsbD
    (coreSize x * coreSize x + x * tSize x + i * wSize x + j)

def oriented {x : Nat} (bits : BitVec (coreWidth x)) : Bool :=
  allN (coreSize x) fun i =>
    !arc bits i i &&
      allN (coreSize x) fun j =>
        decide (i = j) || !(arc bits i j && arc bits j i)

def internalOut {x : Nat} (bits : BitVec (coreWidth x)) (i : Nat) : BitVec 8 :=
  sumN (coreSize x) (arc bits i)

def hDegree {x : Nat} (bits : BitVec (coreWidth x)) (i : Nat) : BitVec 8 :=
  internalOut bits i +
    if 2 ≤ i then sumN (tSize x) (xToT bits (i - 2)) else 0

def pDegree {x : Nat} (bits : BitVec (coreWidth x)) (i : Nat) : BitVec 8 :=
  internalOut bits (hSize x + i) + sumN (wSize x) (pToW bits i)

def reachedInCore {x : Nat} (bits : BitVec (coreWidth x))
    (u target : Nat) : Bool :=
  anyN (coreSize x) fun middle =>
    decide (middle ≠ u) && decide (middle ≠ target) &&
      arc bits u middle && arc bits middle target

def secondCoreCount {x : Nat} (bits : BitVec (coreWidth x))
    (u : Nat) : BitVec 8 :=
  sumN (coreSize x) fun target =>
    decide (target ≠ u) && !arc bits u target &&
      reachedInCore bits u target

def reachedT {x : Nat} (bits : BitVec (coreWidth x))
    (u target : Nat) : Bool :=
  anyN x fun i => arc bits u (2 + i) && xToT bits i target

def reachedW {x : Nat} (bits : BitVec (coreWidth x))
    (u target : Nat) : Bool :=
  anyN 6 fun i => arc bits u (hSize x + i) && pToW bits i target

def representedSecondCount {x : Nat} (bits : BitVec (coreWidth x))
    (u : Nat) : BitVec 8 :=
  secondCoreCount bits u + sumN (tSize x) (reachedT bits u) +
    sumN (wSize x) (reachedW bits u)

def baseCore {x : Nat} (bits : BitVec (coreWidth x)) : Bool :=
  oriented bits &&
    allN (hSize x) (fun i => (8 : BitVec 8).ule (hDegree bits i)) &&
    allN 6 (fun i => (8 : BitVec 8).ule (pDegree bits i)) &&
    allN 2 (fun u =>
      (2 : BitVec 8).ule (sumN (hSize x) (arc bits u)) &&
        (representedSecondCount bits u).ult (internalOut bits u))

def totalHToP {x : Nat} (bits : BitVec (coreWidth x)) : BitVec 8 :=
  sumCountsN (hSize x) fun i =>
    sumN 6 fun j => arc bits i (hSize x + j)

def totalPToH {x : Nat} (bits : BitVec (coreWidth x)) : BitVec 8 :=
  sumCountsN 6 fun i =>
    sumN (hSize x) fun j => arc bits (hSize x + i) j

def totalHInternal {x : Nat} (bits : BitVec (coreWidth x)) : BitVec 8 :=
  sumCountsN (hSize x) fun i => sumN (hSize x) (arc bits i)

def totalPInternal {x : Nat} (bits : BitVec (coreWidth x)) : BitVec 8 :=
  sumCountsN 6 fun i => sumN 6 fun j =>
    arc bits (hSize x + i) (hSize x + j)

def totalXToT {x : Nat} (bits : BitVec (coreWidth x)) : BitVec 8 :=
  sumCountsN x fun i => sumN (tSize x) (xToT bits i)

def totalPToW {x : Nat} (bits : BitVec (coreWidth x)) : BitVec 8 :=
  sumCountsN 6 fun i => sumN (wSize x) (pToW bits i)

/-- For `x < 3`, the core needs no additional equality data. -/
def xOneCore (bits : BitVec (coreWidth 1)) : Bool :=
  baseCore bits

def xTwoCore (bits : BitVec (coreWidth 2)) : Bool :=
  baseCore bits

/-- The tight `x = 3` row is determined by its two cross-block totals. -/
def xThreeCore (bits : BitVec (coreWidth 3)) : Bool :=
  baseCore bits && totalHToP bits == 21 && totalPToH bits == 9

end SeymourEight.BSixKTwoCore
