import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Exact-seven four-`Z` certificate core

This finite core retains the incidences needed for the exact-union-seven
four-`Z` argument.  Rather than separating the internal defect into `alpha`
and `beta`, a certificate row is indexed only by

* the external defect `missing = 0,1`;
* the sum of the seven represented `P` outdegrees; and
* one of the eight possible types of `W ∩ H`.

Here `|P| = 7`, `|H| = |Z| = 4`, `|A| = 8`, and `|W| = 7`.
The 214 primary bits are laid out as the full `P × P`, `P × H`,
`H × P`, `A × A`, `Z × Z`, and `Z × W` matrices, followed by
the optional arc `z0 → p0` in the `missing = 1` case.
-/

namespace SeymourEight.FourZExactSeven

open FiveZExactRisk

/-! ## The eight overlap types -/

/-- Canonical forms for `W ∩ H`, up to relabelling the three `X` vertices.
`H[0]` is the distinguished `A1`; `H[1],H[2],H[3]` are `X`. -/
inductive OverlapType where
  | none
  | xOne
  | aOne
  | xTwo
  | aXOne
  | xThree
  | aXTwo
  | aXThree
  deriving DecidableEq, Repr

/-- The chosen canonical identification of initial `W` vertices with `H`. -/
def wMatchesH (overlap : OverlapType) (w h : Nat) : Bool :=
  match overlap with
  | .none => false
  | .xOne => decide (w = 0 && h = 1)
  | .aOne => decide (w = 0 && h = 0)
  | .xTwo => decide ((w = 0 && h = 1) || (w = 1 && h = 2))
  | .aXOne => decide ((w = 0 && h = 0) || (w = 1 && h = 1))
  | .xThree =>
      decide ((w = 0 && h = 1) || (w = 1 && h = 2) || (w = 2 && h = 3))
  | .aXTwo =>
      decide ((w = 0 && h = 0) || (w = 1 && h = 1) || (w = 2 && h = 2))
  | .aXThree =>
      decide ((w = 0 && h = 0) || (w = 1 && h = 1) ||
        (w = 2 && h = 2) || (w = 3 && h = 3))

def hInW (overlap : OverlapType) (h : Nat) : Bool :=
  any 7 fun w => wMatchesH overlap w h

/-! ## Primary-variable layout -/

def pArc (bits : BitVec 214) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : BitVec 214) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 4 + h)

def hToP (bits : BitVec 214) (h i : Nat) : Bool :=
  bits.getLsbD (77 + h * 7 + i)

def aArc (bits : BitVec 214) (i j : Nat) : Bool :=
  bits.getLsbD (105 + i * 8 + j)

def zArc (bits : BitVec 214) (i j : Nat) : Bool :=
  bits.getLsbD (169 + i * 4 + j)

def zToW (bits : BitVec 214) (z w : Nat) : Bool :=
  bits.getLsbD (185 + z * 7 + w)

def z0ToP0 (bits : BitVec 214) : Bool :=
  bits.getLsbD 213

/-! ## `P` degree and second-neighborhood constraints -/

def orientedPH (bits : BitVec 214) : Bool :=
  all 7 fun i => all 4 fun h => !(pToH bits i h && hToP bits h i)

def pOut (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  count 7 (pArc bits i)

def pHOut (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  count 4 (pToH bits i)

def hPOut (bits : BitVec 214) (h : Nat) : BitVec 8 :=
  count 7 (hToP bits h)

def totalPToH (bits : BitVec 214) : BitVec 8 :=
  count 28 fun q => pToH bits (q / 4) (q % 4)

def totalHToP (bits : BitVec 214) : BitVec 8 :=
  count 28 fun q => hToP bits (q / 7) (q % 7)

def totalMissingPPairs (bits : BitVec 214) : BitVec 8 :=
  count 49 fun q =>
    let i := q / 7
    let j := q % 7
    decide (i < j) && !pArc bits i j && !pArc bits j i

def pToZ (missing i z : Nat) : Bool :=
  !(decide (missing = 1 && i = 0 && z = 0))

def reachedPViaPOrH (bits : BitVec 214) (i j : Nat) : Bool :=
  any 7 (fun middle =>
    decide (middle ≠ i) && decide (middle ≠ j) &&
      pArc bits i middle && pArc bits middle j) ||
  any 4 (fun h => pToH bits i h && hToP bits h j)

def secondPViaPOrH (bits : BitVec 214) (i j : Nat) : Bool :=
  decide (j ≠ i) && !pArc bits i j && reachedPViaPOrH bits i j

def secondPCount (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  count 7 (secondPViaPOrH bits i)

def reachesW (missing : Nat) (bits : BitVec 214) (i w : Nat) : Bool :=
  any 4 fun z => pToZ missing i z && zToW bits z w

def directWFromP (overlap : OverlapType) (bits : BitVec 214) (i w : Nat) : Bool :=
  any 4 fun h => wMatchesH overlap w h && pToH bits i h

def secondW (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (i w : Nat) : Bool :=
  reachesW missing bits i w && !directWFromP overlap bits i w

def secondWCount (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  count 7 (secondW missing overlap bits i)

def reachesOutsideH (bits : BitVec 214) (i h : Nat) : Bool :=
  any 7 fun middle => pArc bits i middle && pToH bits middle h

def secondOutsideH (overlap : OverlapType)
    (bits : BitVec 214) (i h : Nat) : Bool :=
  !hInW overlap h && reachesOutsideH bits i h && !pToH bits i h

def secondOutsideHCount (overlap : OverlapType)
    (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  count 4 (secondOutsideH overlap bits i)

/-- The only possibly missing direct `P → Z` arc is `p0 → z0`.
For `m=1`, a path through one of `z1,z2,z3` makes `z0` a second neighbor. -/
def missingZSecond (missing : Nat) (bits : BitVec 214) (i : Nat) : Bool :=
  decide (missing = 1 && i = 0) &&
    any 3 (fun q => zArc bits (q + 1) 0)

def pDegree (missing : Nat) (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  (if missing = 1 && i = 0 then 3 else 4) + pHOut bits i + pOut bits i

def pSecondCount (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (i : Nat) : BitVec 8 :=
  secondPCount bits i + secondWCount missing overlap bits i +
    secondOutsideHCount overlap bits i + bitCount (missingZSecond missing bits i)

def pNonSeymour (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (i : Nat) : Bool :=
  (pSecondCount missing overlap bits i).ult (pDegree missing bits i)

/-! ## Exact `A` and `H` constraints -/

def aOut (bits : BitVec 214) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def hDegree (bits : BitVec 214) (h : Nat) : BitVec 8 :=
  aOut bits (h + 1) + hPOut bits h

def reachesAFromH (bits : BitVec 214) (h target : Nat) : Bool :=
  let source := h + 1
  any 8 (fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      aArc bits source middle && aArc bits middle target) ||
  (decide (1 ≤ target && target ≤ 4) &&
    any 7 (fun middle => hToP bits h middle && pToH bits middle (target - 1)))

def secondAFromH (bits : BitVec 214) (h target : Nat) : Bool :=
  let source := h + 1
  decide (target ≠ source) && reachesAFromH bits h target &&
    !aArc bits source target

def reachesPFromH (bits : BitVec 214) (h target : Nat) : Bool :=
  let source := h + 1
  any 8 (fun middle =>
    aArc bits source middle &&
      (decide (middle = 0) ||
        (decide (1 ≤ middle && middle ≤ 4) &&
          hToP bits (middle - 1) target))) ||
  any 7 (fun middle =>
    decide (middle ≠ target) && hToP bits h middle && pArc bits middle target)

def secondPFromH (bits : BitVec 214) (h target : Nat) : Bool :=
  reachesPFromH bits h target && !hToP bits h target

def reachesZFromH (missing : Nat) (bits : BitVec 214) (h target : Nat) : Bool :=
  any 7 fun middle => hToP bits h middle && pToZ missing middle target

def hSecondCount (missing : Nat) (bits : BitVec 214) (h : Nat) : BitVec 8 :=
  count 8 (secondAFromH bits h) + count 7 (secondPFromH bits h) +
    count 4 (reachesZFromH missing bits h)

def hNonSeymour (missing : Nat) (bits : BitVec 214) (h : Nat) : Bool :=
  (hSecondCount missing bits h).ult (hDegree bits h)

def fixedAStructure (bits : BitVec 214) : Bool :=
  orientedSquare 8 (aArc bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 3 (fun q => !aArc bits 1 (q + 5)) &&
  all 3 (fun q => aArc bits 1 (q + 2) || any 7 (fun i => pToH bits i (q + 1))) &&
  all 4 (fun h => (8 : BitVec 8).ule (hDegree bits h)) &&
  all 3 (fun q => (1 : BitVec 8).ule (aOut bits (q + 5)))

/-! ## Exact `Z` constraints -/

def exceptionalZToP (missing : Nat) (bits : BitVec 214) (z i : Nat) : Bool :=
  decide (missing = 1 && z = 0 && i = 0) && z0ToP0 bits

def zDegree (missing : Nat) (bits : BitVec 214) (z : Nat) : BitVec 8 :=
  count 4 (zArc bits z) + count 7 (zToW bits z) +
    bitCount (exceptionalZToP missing bits z 0)

def reachesZFromZ (missing : Nat) (bits : BitVec 214) (source target : Nat) : Bool :=
  any 4 (fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      zArc bits source middle && zArc bits middle target) ||
  (decide (missing = 1 && source = 0 && target ≠ 0) && z0ToP0 bits)

def secondZFromZ (missing : Nat) (bits : BitVec 214) (source target : Nat) : Bool :=
  decide (target ≠ source) && reachesZFromZ missing bits source target &&
    !zArc bits source target

def reachesWFromZ (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (source w : Nat) : Bool :=
  any 4 (fun middle =>
    decide (middle ≠ source) && zArc bits source middle && zToW bits middle w) ||
  (decide (missing = 1 && source = 0) && z0ToP0 bits &&
    any 4 (fun h => wMatchesH overlap w h && pToH bits 0 h))

def secondWFromZ (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (source w : Nat) : Bool :=
  reachesWFromZ missing overlap bits source w && !zToW bits source w

def reachesPFromZ (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (source target : Nat) : Bool :=
  any 7 (fun w => any 4 (fun h =>
    wMatchesH overlap w h && zToW bits source w && hToP bits h target)) ||
  (decide (missing = 1 && source = 0 && target ≠ 0) &&
    z0ToP0 bits && pArc bits 0 target) ||
  (decide (missing = 1 && source ≠ 0 && target = 0) &&
    zArc bits source 0 && z0ToP0 bits)

def secondPFromZ (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (source target : Nat) : Bool :=
  reachesPFromZ missing overlap bits source target &&
    !exceptionalZToP missing bits source target

def reachesOutsideHFromZ (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (source h : Nat) : Bool :=
  decide (missing = 1 && source = 0) && !hInW overlap h &&
    z0ToP0 bits && pToH bits 0 h

def zSecondCount (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (z : Nat) : BitVec 8 :=
  count 4 (secondZFromZ missing bits z) +
    count 7 (secondWFromZ missing overlap bits z) +
    count 7 (secondPFromZ missing overlap bits z) +
    count 4 (reachesOutsideHFromZ missing overlap bits z)

def zNonSeymour (missing : Nat) (overlap : OverlapType)
    (bits : BitVec 214) (z : Nat) : Bool :=
  (zSecondCount missing overlap bits z).ult (zDegree missing bits z)

/-! ## Certificate-only symmetry breaking -/

def hCode (bits : BitVec 214) (h : Nat) : BitVec 16 :=
  count16 7 fun i =>
    (bitCount16 (pToH bits i h) <<< i) +
      (bitCount16 (hToP bits h i) <<< (7 + i))

def orderedH (overlap : OverlapType) (bits : BitVec 214) : Bool :=
  match overlap with
  | .none | .aOne =>
      (hCode bits 2).ule (hCode bits 1) && (hCode bits 3).ule (hCode bits 2)
  | .xOne | .aXOne => (hCode bits 3).ule (hCode bits 2)
  | .xTwo | .aXTwo => (hCode bits 2).ule (hCode bits 1)
  | .xThree | .aXThree =>
      (hCode bits 2).ule (hCode bits 1) && (hCode bits 3).ule (hCode bits 2)

def orderedP (missing : Nat) (bits : BitVec 214) : Bool :=
  let first := if missing = 1 then 1 else 0
  all (6 - first) fun q =>
    let i := q + first
    (pDegree missing bits (i + 1)).ule (pDegree missing bits i) &&
      (!(pDegree missing bits i == pDegree missing bits (i + 1)) ||
        (pHOut bits (i + 1)).ule (pHOut bits i))

/-! ## The row core -/

/-- Exact-seven four-`Z` obstruction core.  The intended parameter ranges are
`missing ∈ {0,1}`, degree sum `56,...,63-missing`, and the eight overlap
types above.  No separate `alpha` or `beta` is fixed. -/
def core (missing degreeSum : Nat) (overlap : OverlapType)
    (bits : BitVec 214) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits &&
  orientedSquare 4 (zArc bits) &&
  (totalPToH bits).ule 14 && (14 : BitVec 8).ule (totalHToP bits) &&
  totalMissingPPairs bits + (14 - totalPToH bits) =
    BitVec.ofNat 8 (63 - missing - degreeSum) &&
  all 4 (fun h => (1 : BitVec 8).ule (hPOut bits h)) &&
  fixedAStructure bits &&
  all 7 (fun w => any 4 fun z => zToW bits z w) &&
  all 4 (fun z =>
    (8 : BitVec 8).ule (zDegree missing bits z) &&
      zNonSeymour missing overlap bits z) &&
  all 4 (hNonSeymour missing bits) &&
  all 7 (fun i =>
    (8 : BitVec 8).ule (pDegree missing bits i) &&
      (pDegree missing bits i).ule 14 &&
      pNonSeymour missing overlap bits i) &&
  sumCount 7 (pDegree missing bits) = BitVec.ofNat 8 degreeSum &&
  orderedH overlap bits && orderedP missing bits

end SeymourEight.FourZExactSeven
