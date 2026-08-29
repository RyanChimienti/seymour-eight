import Std.Tactic.BVDecide

/-!
# Exact five-`Z` finite core

This is a direct finite encoding of an exact five-`Z` row.  It lives outside
the graph bridge so the Boolean contradiction and its graph interpretation
remain separate.

The fixed parameters are

* external defect `m = 2`;
* exact external union size `|W| = 6`;
* `(alpha,beta,degreeSum) = (6,1,57)`; and
* `W ∩ H = {a1}`.

The layout uses full square incidence matrices.  Diagonal entries are forced
false by the core, which keeps the indexing and the later graph bridge simple.
-/

namespace SeymourEight.FiveZExactRisk

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0
def bitCount16 (b : Bool) : BitVec 16 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def sumCount : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumCount n p + p n

def count16 : Nat → (Nat → BitVec 16) → BitVec 16
  | 0, _ => 0
  | n + 1, p => count16 n p + p n

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

/-! ## Primary-variable layout -/

/-- Bits `0,...,48`: the full `7 × 7` matrix on `P`. -/
def pArc (bits : BitVec 280) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

/-- Bits `49,...,69`: arcs from the seven `P` vertices to three `H` vertices. -/
def pToH (bits : BitVec 280) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 3 + h)

/-- Bits `70,...,90`: arcs from `H` to `P`. -/
def hToP (bits : BitVec 280) (h i : Nat) : Bool :=
  bits.getLsbD (70 + h * 7 + i)

/-- Bits `91,...,125`: arcs from `P` to the five `Z` vertices. -/
def pToZ (bits : BitVec 280) (i z : Nat) : Bool :=
  bits.getLsbD (91 + i * 5 + z)

/-- Bits `126,...,160`: arcs from `Z` to `P`. -/
def zToP (bits : BitVec 280) (z i : Nat) : Bool :=
  bits.getLsbD (126 + z * 7 + i)

/-- Bits `161,...,224`: the full `8 × 8` matrix on `A`. -/
def aArc (bits : BitVec 280) (i j : Nat) : Bool :=
  bits.getLsbD (161 + i * 8 + j)

/-- Bits `225,...,249`: the full `5 × 5` matrix on `Z`. -/
def zArc (bits : BitVec 280) (i j : Nat) : Bool :=
  bits.getLsbD (225 + i * 5 + j)

/-- Bits `250,...,279`: arcs from the five `Z` vertices to the six vertices of `W`. -/
def zToW (bits : BitVec 280) (z w : Nat) : Bool :=
  bits.getLsbD (250 + z * 6 + w)

/-! ## Common finite counts and reachability -/

def orientedSquare (n : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all n fun i => !arc i i && all n fun j =>
    decide (i = j) || !(arc i j && arc j i)

def orientedPH (bits : BitVec 280) : Bool :=
  all 7 fun i => all 3 fun h => !(pToH bits i h && hToP bits h i)

def orientedPZ (bits : BitVec 280) : Bool :=
  all 7 fun i => all 5 fun z => !(pToZ bits i z && zToP bits z i)

def pOut (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 7 (pArc bits i)

def pHOut (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 3 (pToH bits i)

def hPOut (bits : BitVec 280) (h : Nat) : BitVec 8 :=
  count 7 (hToP bits h)

def pZOut (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 5 (pToZ bits i)

def zPOut (bits : BitVec 280) (z : Nat) : BitVec 8 :=
  count 7 (zToP bits z)

def totalPToH (bits : BitVec 280) : BitVec 8 :=
  count 21 fun q => pToH bits (q / 3) (q % 3)

def totalHToP (bits : BitVec 280) : BitVec 8 :=
  count 21 fun q => hToP bits (q / 7) (q % 7)

def totalMissingPPairs (bits : BitVec 280) : BitVec 8 :=
  count 49 fun q =>
    let i := q / 7
    let j := q % 7
    decide (i < j) && !pArc bits i j && !pArc bits j i

def totalMissingPZ (bits : BitVec 280) : BitVec 8 :=
  count 35 fun q => !pToZ bits (q / 5) (q % 5)

def reachedPViaPOrH (bits : BitVec 280) (i j : Nat) : Bool :=
  any 7 (fun middle =>
    decide (middle ≠ i) && decide (middle ≠ j) &&
      pArc bits i middle && pArc bits middle j) ||
  any 3 (fun h => pToH bits i h && hToP bits h j)

def secondPViaPOrH (bits : BitVec 280) (i j : Nat) : Bool :=
  decide (j ≠ i) && !pArc bits i j && reachedPViaPOrH bits i j

def secondPCount (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 7 (secondPViaPOrH bits i)

/-! ## Exact six-vertex `Z`-union contributions -/

/-- `W[0]` is the unique member of `W ∩ H`, namely `H[0]=a1`. -/
def reachesW (bits : BitVec 280) (i w : Nat) : Bool :=
  any 5 fun z => pToZ bits i z && zToW bits z w

def secondW (bits : BitVec 280) (i w : Nat) : Bool :=
  reachesW bits i w && (decide (w ≠ 0) || !pToH bits i 0)

def secondWCount (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 6 (secondW bits i)

def reachesOutsideH (bits : BitVec 280) (i h : Nat) : Bool :=
  any 7 fun middle => pArc bits i middle && pToH bits middle h

def secondOutsideH (bits : BitVec 280) (i h : Nat) : Bool :=
  decide (h ≠ 0) && reachesOutsideH bits i h && !pToH bits i h

def secondOutsideHCount (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 3 (secondOutsideH bits i)

def reachesZFromP (bits : BitVec 280) (i target : Nat) : Bool :=
  any 5 fun middle =>
    decide (middle ≠ target) && pToZ bits i middle && zArc bits middle target

def secondMissingZ (bits : BitVec 280) (i target : Nat) : Bool :=
  reachesZFromP bits i target && !pToZ bits i target

def secondMissingZCount (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  count 5 (secondMissingZ bits i)

def pDegree (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  pZOut bits i + pHOut bits i + pOut bits i

def pNonSeymour (bits : BitVec 280) (i : Nat) : Bool :=
  (secondPCount bits i + secondWCount bits i +
      secondOutsideHCount bits i + secondMissingZCount bits i).ult
    (pDegree bits i)

/-! ## The exact `A` and `H` constraints -/

def aOut (bits : BitVec 280) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def hDegree (bits : BitVec 280) (h : Nat) : BitVec 8 :=
  aOut bits (h + 1) + hPOut bits h

def reachesAFromH (bits : BitVec 280) (h target : Nat) : Bool :=
  let source := h + 1
  any 8 (fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      aArc bits source middle && aArc bits middle target) ||
  (decide (1 ≤ target && target ≤ 3) &&
    any 7 (fun middle => hToP bits h middle && pToH bits middle (target - 1)))

def secondAFromH (bits : BitVec 280) (h target : Nat) : Bool :=
  let source := h + 1
  decide (target ≠ source) && reachesAFromH bits h target &&
    !aArc bits source target

def reachesPFromH (bits : BitVec 280) (h target : Nat) : Bool :=
  let source := h + 1
  any 8 (fun middle =>
    aArc bits source middle &&
      (decide (middle = 0) ||
        (decide (1 ≤ middle && middle ≤ 3) &&
          hToP bits (middle - 1) target))) ||
  any 7 (fun middle =>
    decide (middle ≠ target) && hToP bits h middle && pArc bits middle target)

def secondPFromH (bits : BitVec 280) (h target : Nat) : Bool :=
  reachesPFromH bits h target && !hToP bits h target

def reachesZFromH (bits : BitVec 280) (h target : Nat) : Bool :=
  any 7 fun middle => hToP bits h middle && pToZ bits middle target

def hSecondCount (bits : BitVec 280) (h : Nat) : BitVec 8 :=
  count 8 (secondAFromH bits h) + count 7 (secondPFromH bits h) +
    count 5 (reachesZFromH bits h)

def hNonSeymour (bits : BitVec 280) (h : Nat) : Bool :=
  (hSecondCount bits h).ult (hDegree bits h)

def fixedAStructure (bits : BitVec 280) : Bool :=
  orientedSquare 8 (aArc bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 4 (fun q => !aArc bits 1 (q + 4)) &&
  (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) &&
  (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) &&
  all 3 (fun h => (8 : BitVec 8).ule (hDegree bits h)) &&
  all 4 (fun q => (1 : BitVec 8).ule (aOut bits (q + 4)))

/-! ## Exact `Z` constraints and non-Seymour lower bounds -/

def zDegree (bits : BitVec 280) (z : Nat) : BitVec 8 :=
  count 5 (zArc bits z) + count 6 (zToW bits z) + zPOut bits z

def reachesZFromZ (bits : BitVec 280) (source target : Nat) : Bool :=
  any 5 (fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      zArc bits source middle && zArc bits middle target) ||
  any 7 (fun middle => zToP bits source middle && pToZ bits middle target)

def secondZFromZ (bits : BitVec 280) (source target : Nat) : Bool :=
  decide (target ≠ source) && reachesZFromZ bits source target &&
    !zArc bits source target

def reachesWFromZ (bits : BitVec 280) (source w : Nat) : Bool :=
  any 5 (fun middle =>
    decide (middle ≠ source) && zArc bits source middle && zToW bits middle w) ||
  (decide (w = 0) &&
    any 7 (fun middle => zToP bits source middle && pToH bits middle 0))

def secondWFromZ (bits : BitVec 280) (source w : Nat) : Bool :=
  reachesWFromZ bits source w && !zToW bits source w

def reachesPFromZ (bits : BitVec 280) (source target : Nat) : Bool :=
  (zToW bits source 0 && hToP bits 0 target) ||
  any 7 (fun middle =>
    decide (middle ≠ target) && zToP bits source middle && pArc bits middle target) ||
  any 5 (fun middle =>
    decide (middle ≠ source) && zArc bits source middle && zToP bits middle target)

def secondPFromZ (bits : BitVec 280) (source target : Nat) : Bool :=
  reachesPFromZ bits source target && !zToP bits source target

def reachesOutsideHFromZ (bits : BitVec 280) (source h : Nat) : Bool :=
  decide (h ≠ 0) &&
    any 7 (fun middle => zToP bits source middle && pToH bits middle h)

def zSecondCount (bits : BitVec 280) (z : Nat) : BitVec 8 :=
  count 5 (secondZFromZ bits z) + count 6 (secondWFromZ bits z) +
    count 7 (secondPFromZ bits z) + count 3 (reachesOutsideHFromZ bits z)

def zNonSeymour (bits : BitVec 280) (z : Nat) : Bool :=
  (zSecondCount bits z).ult (zDegree bits z)

/-! ## Symmetry breaking -/

def hCode (bits : BitVec 280) (h : Nat) : BitVec 16 :=
  count16 7 fun i =>
    (bitCount16 (pToH bits i h) <<< i) +
      (bitCount16 (hToP bits h i) <<< (7 + i))

def orderedH (bits : BitVec 280) : Bool :=
  (hCode bits 2).ule (hCode bits 1)

def orderedP (bits : BitVec 280) : Bool :=
  all 6 fun i =>
    (pDegree bits (i + 1)).ule (pDegree bits i) &&
      (!(pDegree bits i == pDegree bits (i + 1)) ||
        (pHOut bits (i + 1)).ule (pHOut bits i))

/-! ## Fixed finite core -/

def riskCore (bits : BitVec 280) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits && orientedPZ bits &&
  orientedSquare 5 (zArc bits) &&
  (totalMissingPPairs bits == 1) &&
  (totalPToH bits == 4) && (11 : BitVec 8).ule (totalHToP bits) &&
  (totalMissingPZ bits == 2) &&
  all 3 (fun h => (1 : BitVec 8).ule (hPOut bits h)) &&
  fixedAStructure bits &&
  all 6 (fun w => any 5 fun z => zToW bits z w) &&
  all 5 (fun z => (8 : BitVec 8).ule (zDegree bits z) && zNonSeymour bits z) &&
  all 3 (hNonSeymour bits) &&
  all 7 (fun i =>
    (8 : BitVec 8).ule (pDegree bits i) &&
      (pDegree bits i).ule 14 && pNonSeymour bits i) &&
  (sumCount 7 (pDegree bits) == 57) && orderedH bits && orderedP bits

/-- Positive-control version of `riskCore`, omitting only non-Seymour bounds. -/
def riskStructure (bits : BitVec 280) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits && orientedPZ bits &&
  orientedSquare 5 (zArc bits) &&
  (totalMissingPPairs bits == 1) &&
  (totalPToH bits == 4) && (11 : BitVec 8).ule (totalHToP bits) &&
  (totalMissingPZ bits == 2) &&
  all 3 (fun h => (1 : BitVec 8).ule (hPOut bits h)) &&
  fixedAStructure bits &&
  all 6 (fun w => any 5 fun z => zToW bits z w) &&
  all 5 (fun z => (8 : BitVec 8).ule (zDegree bits z)) &&
  all 7 (fun i =>
    (8 : BitVec 8).ule (pDegree bits i) && (pDegree bits i).ule 14) &&
  (sumCount 7 (pDegree bits) == 57) && orderedH bits && orderedP bits

/--
The whole exact-union-six, `W ∩ H = {a1}` family with external defect at
most three.  The row parameters are not fixed: orientation and
`e(H,P) ≥ 11` imply `e(P,H) ≤ 10`, while the exact `P` degree accounting
recovers the usual `alpha`, `beta`, and degree-sum identity automatically.
-/
def familyCore (bits : BitVec 280) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits && orientedPZ bits &&
  orientedSquare 5 (zArc bits) &&
  (11 : BitVec 8).ule (totalHToP bits) &&
  (totalMissingPZ bits).ule 3 &&
  all 3 (fun h => (1 : BitVec 8).ule (hPOut bits h)) &&
  fixedAStructure bits &&
  all 6 (fun w => any 5 fun z => zToW bits z w) &&
  all 5 (fun z => (8 : BitVec 8).ule (zDegree bits z) && zNonSeymour bits z) &&
  all 3 (hNonSeymour bits) &&
  all 7 (fun i =>
    (8 : BitVec 8).ule (pDegree bits i) &&
      (pDegree bits i).ule 14 && pNonSeymour bits i) &&
  orderedH bits && orderedP bits

/-- The same graph-theoretic family without certificate-only symmetry
breaking.  This form makes the graph bridge independent of a canonical
labelling; its SAT cost is measured separately. -/
def familyCoreUnordered (bits : BitVec 280) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits && orientedPZ bits &&
  orientedSquare 5 (zArc bits) &&
  (11 : BitVec 8).ule (totalHToP bits) &&
  (totalMissingPZ bits).ule 3 &&
  all 3 (fun h => (1 : BitVec 8).ule (hPOut bits h)) &&
  fixedAStructure bits &&
  all 6 (fun w => any 5 fun z => zToW bits z w) &&
  all 5 (fun z => (8 : BitVec 8).ule (zDegree bits z) && zNonSeymour bits z) &&
  all 3 (hNonSeymour bits) &&
  all 7 (fun i =>
    (8 : BitVec 8).ule (pDegree bits i) &&
      (pDegree bits i).ule 14 && pNonSeymour bits i)

end SeymourEight.FiveZExactRisk
