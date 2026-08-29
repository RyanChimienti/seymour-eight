import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Four-`Z`, union-at-least-eight aggregate core

Only the `P × P`, `P × H`, and `H × P` incidences are retained.  The
external defect is either zero or one; in the latter case the exceptional
vertex is relabelled as `P[0]`.  The core splits only on the sum of the seven
represented `P` outdegrees, rather than on two separate internal-defect
parameters.
-/

namespace SeymourEight.FourZUnionEight

open FiveZExactRisk

def pArc (bits : BitVec 105) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : BitVec 105) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 4 + h)

def hToP (bits : BitVec 105) (h i : Nat) : Bool :=
  bits.getLsbD (77 + h * 7 + i)

def orientedPH (bits : BitVec 105) : Bool :=
  all 7 fun i => all 4 fun h => !(pToH bits i h && hToP bits h i)

def pOut (bits : BitVec 105) (i : Nat) : BitVec 8 :=
  count 7 (pArc bits i)

def pHOut (bits : BitVec 105) (i : Nat) : BitVec 8 :=
  count 4 (pToH bits i)

def hPOut (bits : BitVec 105) (h : Nat) : BitVec 8 :=
  count 7 (hToP bits h)

def totalPToH (bits : BitVec 105) : BitVec 8 :=
  count 28 fun q => pToH bits (q / 4) (q % 4)

def totalHToP (bits : BitVec 105) : BitVec 8 :=
  count 28 fun q => hToP bits (q / 7) (q % 7)

def totalMissingPPairs (bits : BitVec 105) : BitVec 8 :=
  count 49 fun q =>
    let i := q / 7
    let j := q % 7
    decide (i < j) && !pArc bits i j && !pArc bits j i

def reachedPViaPOrH (bits : BitVec 105) (i j : Nat) : Bool :=
  any 7 (fun middle =>
    decide (middle ≠ i) && decide (middle ≠ j) &&
      pArc bits i middle && pArc bits middle j) ||
  any 4 (fun h => pToH bits i h && hToP bits h j)

def secondPViaPOrH (bits : BitVec 105) (i j : Nat) : Bool :=
  decide (j ≠ i) && !pArc bits i j && reachedPViaPOrH bits i j

def secondPCount (bits : BitVec 105) (i : Nat) : BitVec 8 :=
  count 7 (secondPViaPOrH bits i)

def externalFirst (missing i : Nat) : BitVec 8 :=
  if missing = 1 && i = 0 then 3 else 4

def externalSecondLower (missing i : Nat) : BitVec 8 :=
  if missing = 1 && i = 0 then 6 else 8

def pDegree (missing : Nat) (bits : BitVec 105) (i : Nat) : BitVec 8 :=
  externalFirst missing i + pHOut bits i + pOut bits i

def pNonSeymour (missing : Nat) (bits : BitVec 105) (i : Nat) : Bool :=
  (secondPCount bits i + externalSecondLower missing i).ult
    (pDegree missing bits i + pHOut bits i)

def orderedP (missing : Nat) (bits : BitVec 105) : Bool :=
  let first := if missing = 1 then 1 else 0
  all (6 - first) fun q =>
    let i := q + first
    (pDegree missing bits (i + 1)).ule (pDegree missing bits i) &&
      (!(pDegree missing bits i == pDegree missing bits (i + 1)) ||
        (pHOut bits (i + 1)).ule (pHOut bits i))

def core (missing degreeSum : Nat) (bits : BitVec 105) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits &&
  (totalPToH bits).ule 14 && (14 : BitVec 8).ule (totalHToP bits) &&
  totalMissingPPairs bits + (14 - totalPToH bits) =
    BitVec.ofNat 8 (63 - missing - degreeSum) &&
  all 7 (fun i =>
    (8 : BitVec 8).ule (pDegree missing bits i) &&
      (pDegree missing bits i).ule 14 && pNonSeymour missing bits i) &&
  sumCount 7 (pDegree missing bits) = BitVec.ofNat 8 degreeSum &&
  orderedP missing bits

end SeymourEight.FourZUnionEight
