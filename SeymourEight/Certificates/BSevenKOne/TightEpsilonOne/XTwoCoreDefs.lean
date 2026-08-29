import Std.Tactic.BVDecide

/-!
# Compact core for tight epsilon-one `(x,z)=(2,4)`

The 150-bit layout contains square/rectangular incidence blocks for `P→P`,
`P→H`, `H→P`, `P→({s}∪Z)`, and `H→A`, of sizes
`49 + 21 + 21 + 35 + 24`.
-/

namespace SeymourEight.EpsilonOneXTwoCore

abbrev Encoding := BitVec 150

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def sumCount : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumCount n p + p n

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : Encoding) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 3 + h)

def hToP (bits : Encoding) (h i : Nat) : Bool :=
  bits.getLsbD (70 + h * 7 + i)

def pToE (bits : Encoding) (i t : Nat) : Bool :=
  bits.getLsbD (91 + i * 5 + t)

def hToA (bits : Encoding) (h a : Nat) : Bool :=
  bits.getLsbD (126 + h * 8 + a)

def pOut (bits : Encoding) (i : Nat) : BitVec 8 := count 7 (pArc bits i)
def pHOut (bits : Encoding) (i : Nat) : BitVec 8 := count 3 (pToH bits i)
def pEOut (bits : Encoding) (i : Nat) : BitVec 8 := count 5 (pToE bits i)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 7 (hToP bits h)
def hAOut (bits : Encoding) (h : Nat) : BitVec 8 := count 8 (hToA bits h)

def pDegree (bits : Encoding) (i : Nat) : BitVec 8 :=
  pOut bits i + pHOut bits i + pEOut bits i

def hDegree (bits : Encoding) (h : Nat) : BitVec 8 :=
  hAOut bits h + hPOut bits h

def orientedOnP (bits : Encoding) : Bool :=
  all 7 (fun i => !pArc bits i i) &&
    all 7 (fun i => all 7 (fun j =>
      decide (i = j) || !(pArc bits i j && pArc bits j i)))

def orientedPH (bits : Encoding) : Bool :=
  all 7 (fun i => all 3 (fun h => !(pToH bits i h && hToP bits h i)))

def fixedHStructure (bits : Encoding) : Bool :=
  all 3 (fun h => !hToA bits h (h + 1)) &&
  all 3 (fun h => all 3 (fun k =>
    decide (h = k) || !(hToA bits h (k + 1) && hToA bits k (h + 1)))) &&
  !hToA bits 0 0 && all 4 (fun q => !hToA bits 0 (q + 4)) &&
  all 3 (fun h =>
    (1 : BitVec 8).ule (hAOut bits h) &&
    (8 : BitVec 8).ule (hDegree bits h) &&
    (!(hAOut bits h == 1) || hPOut bits h == 7)) &&
  all 2 (fun q => hToA bits 0 (q + 2) || any 7 (fun i => pToH bits i (q + 1)))

/-- The eight first neighbors of `a1` are indexed by `0=A1`, `i+1=Pᵢ`;
the seven second targets are indexed by the two `X` vertices followed by the
five external targets. -/
def predecessor (bits : Encoding) (d target : Nat) : Bool :=
  if target < 2 then
    if d = 0 then hToA bits 0 (target + 2)
    else pToH bits (d - 1) (target + 1)
  else if d = 0 then false
  else pToE bits (d - 1) (target - 2)

def targetCovered (bits : Encoding) : Bool :=
  all 7 (fun target => any 8 (fun d => predecessor bits d target))

def deletedReached (bits : Encoding) (d : Nat) : Bool :=
  if d = 0 then any 7 (fun i => pToH bits i 0)
  else
    hToP bits 0 (d - 1) ||
      any 7 (fun i => decide (i ≠ d - 1) && pArc bits i (d - 1))

def privateTarget (bits : Encoding) (d target : Nat) : Bool :=
  predecessor bits d target &&
    all 8 (fun other => decide (other = d) || !predecessor bits other target)

def deletionCritical (bits : Encoding) : Bool :=
  all 8 (fun d =>
    (count 7 (privateTarget bits d)).ule (bitCount (deletedReached bits d)))

def reachedP (bits : Encoding) (i j : Nat) : Bool :=
  any 7 (fun k => decide (k ≠ i) && decide (k ≠ j) &&
    pArc bits i k && pArc bits k j) ||
  any 3 (fun h => pToH bits i h && hToP bits h j)

def secondP (bits : Encoding) (i : Nat) : BitVec 8 :=
  count 7 (fun j => decide (j ≠ i) && !pArc bits i j && reachedP bits i j)

/-- A root arc exposes all eight members of `A`. -/
def rootEquation (bits : Encoding) (i : Nat) : Bool :=
  !pToE bits i 0 ||
    (secondP bits i + 9).ule
      (pEOut bits i + 2 * pHOut bits i + pOut bits i)

def uSecondA (bits : Encoding) : BitVec 8 :=
  count 8 (fun a => decide (a ≠ 1) && !hToA bits 0 a &&
    any 2 (fun q => hToA bits 0 (q + 2) && hToA bits (q + 1) a))

def uSecondP (bits : Encoding) : BitVec 8 :=
  count 7 (fun j => !hToP bits 0 j &&
    (any 7 (fun i => decide (i ≠ j) && hToP bits 0 i && pArc bits i j) ||
      any 2 (fun q => hToA bits 0 (q + 2) && hToP bits (q + 1) j)))

def uSecondE (bits : Encoding) : BitVec 8 :=
  count 5 (fun t => any 7 (fun i => hToP bits 0 i && pToE bits i t))

def uNonSeymour (bits : Encoding) : Bool :=
  (uSecondA bits + uSecondP bits + uSecondE bits + 1).ule (hDegree bits 0)

def core (bits : Encoding) : Bool :=
  orientedOnP bits && orientedPH bits && fixedHStructure bits &&
  targetCovered bits &&
  all 5 (fun t => any 7 (fun i => pToE bits i t)) &&
  all 7 (fun i => (8 : BitVec 8).ule (pDegree bits i) && rootEquation bits i) &&
  (11 : BitVec 8).ule (sumCount 3 (hPOut bits)) &&
  (sumCount 7 (pHOut bits)).ule 10 && uNonSeymour bits

end SeymourEight.EpsilonOneXTwoCore
