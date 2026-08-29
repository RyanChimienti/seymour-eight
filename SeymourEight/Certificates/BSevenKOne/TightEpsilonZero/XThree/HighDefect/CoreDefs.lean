import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Projected high-defect four-`Z` core

This is the `x = 3` analogue of the projected five-`Z` core.  It retains
`A` (eight vertices), `P` (seven vertices), and `Z` (four vertices).  The
seven members of `A \ {a₁}` and all seven members of `P` carry
non-Seymour inequalities, while `a₁` contributes its seven-neighbor
one-arc-deletion expansions.

The block sizes still total 218 bits:

* `P × P`: 49;
* `P × H` and `H × P`, with `|H| = 4`: 28 each;
* `P × Z`, with `|Z| = 4`: 28;
* `R × P`, with `|R| = 3`: 21; and
* `A × A`: 64.
-/

namespace SeymourEight.FourZHighDefect

open FiveZExactRisk

def pArc (bits : BitVec 218) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : BitVec 218) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 4 + h)

def hToP (bits : BitVec 218) (h i : Nat) : Bool :=
  bits.getLsbD (77 + h * 7 + i)

def pToZ (bits : BitVec 218) (i z : Nat) : Bool :=
  bits.getLsbD (105 + i * 4 + z)

def rToP (bits : BitVec 218) (r i : Nat) : Bool :=
  bits.getLsbD (133 + r * 7 + i)

def aArc (bits : BitVec 218) (i j : Nat) : Bool :=
  bits.getLsbD (154 + i * 8 + j)

def aToP (bits : BitVec 218) (a i : Nat) : Bool :=
  if a = 0 then true
  else if a < 5 then hToP bits (a - 1) i
  else rToP bits (a - 5) i

def pToA (bits : BitVec 218) (i a : Nat) : Bool :=
  if 0 < a && a < 5 then pToH bits i (a - 1) else false

def coreArc (bits : BitVec 218) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 19 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def coreOutdegree (bits : BitVec 218) (u : Nat) : BitVec 8 :=
  count 19 (coreArc bits u)

def aOut (bits : BitVec 218) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def aPOut (bits : BitVec 218) (a : Nat) : BitVec 8 :=
  count 7 (aToP bits a)

def totalHToP (bits : BitVec 218) : BitVec 8 :=
  count 28 fun q => aToP bits (q / 7 + 1) (q % 7)

def totalMissingPZ (bits : BitVec 218) : BitVec 8 :=
  count 28 fun q => !pToZ bits (q / 4) (q % 4)

def pDegree (bits : BitVec 218) (i : Nat) : BitVec 8 :=
  count 4 (pToZ bits i) + count 4 (pToH bits i) + count 7 (pArc bits i)

def pDegreeSum (bits : BitVec 218) : BitVec 8 :=
  sumCount 7 (pDegree bits)

/-- Symmetry break for the interchangeable `P` vertices: descending total
degree, then descending `P → H` count inside a tied degree block. -/
def orderedP (bits : BitVec 218) : Bool :=
  all 6 fun i =>
    (pDegree bits (i + 1)).ule (pDegree bits i) &&
      (!(pDegree bits i == pDegree bits (i + 1)) ||
        (count 4 (pToH bits (i + 1))).ule (count 4 (pToH bits i)))

def zCode (bits : BitVec 218) (z : Nat) : BitVec 16 :=
  count16 7 fun i => bitCount16 (pToZ bits i z) <<< i

def orderedZ (bits : BitVec 218) : Bool :=
  all 3 fun z => (zCode bits (z + 1)).ule (zCode bits z)

/-- Binary incidence-column code used to canonically label the four
interchangeable `Z` vertices after `P` has been labelled. -/
def reachedFromA (bits : BitVec 218) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc bits source middle && coreArc bits middle target

def secondFromA (bits : BitVec 218) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachedFromA bits source target

def aSecondCount (bits : BitVec 218) (source : Nat) : BitVec 8 :=
  count 19 (secondFromA bits source)

def aNonSeymour (bits : BitVec 218) (source : Nat) : Bool :=
  (aSecondCount bits source).ult (coreOutdegree bits source)

def aOneNeighbor (d : Nat) : Nat :=
  if d = 0 then 1 else d + 7

def retainedAfterDelete (deleted vertex : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) && decide (vertex = aOneNeighbor d)

def deletionReached (bits : BitVec 218) (deleted target : Nat) : Bool :=
  decide (target ≠ 0) && !retainedAfterDelete deleted target &&
    any 19 fun middle =>
      retainedAfterDelete deleted middle && coreArc bits middle target

def deletionExpansionCount (bits : BitVec 218) (deleted : Nat) : BitVec 8 :=
  count 19 (deletionReached bits deleted)

def aOneDeletionExpands (bits : BitVec 218) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule (deletionExpansionCount bits deleted)

def fixedStructure (bits : BitVec 218) : Bool :=
  orientedSquare 19 (coreArc bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 3 (fun q => !aArc bits 1 (q + 5)) &&
  (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) &&
  (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) &&
  (aArc bits 1 4 || any 7 (fun i => pToH bits i 3)) &&
  all 8 (fun a => (1 : BitVec 8).ule (aOut bits a)) &&
  all 7 (fun q =>
    !(aOut bits (q + 1) = 1) || (7 : BitVec 8).ule (aPOut bits (q + 1))) &&
  all 15 (fun u => (8 : BitVec 8).ule (coreOutdegree bits u)) &&
  (14 : BitVec 8).ule (totalHToP bits) &&
  all 4 (fun z => any 7 (fun i => pToZ bits i z))

def highDefectCore (bits : BitVec 218) : Bool :=
  fixedStructure bits && aOneDeletionExpands bits &&
  (2 : BitVec 8).ule (totalMissingPZ bits) &&
  all 7 (fun q => aNonSeymour bits (q + 1)) &&
  all 7 (fun q => aNonSeymour bits (q + 8)) && orderedP bits && orderedZ bits

def highDefectCoreAtMissing (missing : Nat) (bits : BitVec 218) : Bool :=
  highDefectCore bits && totalMissingPZ bits = BitVec.ofNat 8 missing

def highDefectCoreAtMissingDegree (missing degreeSum : Nat)
    (bits : BitVec 218) : Bool :=
  highDefectCoreAtMissing missing bits &&
    pDegreeSum bits = BitVec.ofNat 8 degreeSum

end SeymourEight.FourZHighDefect
