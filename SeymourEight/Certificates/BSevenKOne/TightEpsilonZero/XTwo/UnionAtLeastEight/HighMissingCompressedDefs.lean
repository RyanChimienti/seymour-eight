import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.FiveZUnionEight

/-!
# Compressed high-missing union-eight core

The aggregate union-eight model uses each `P → Z` row only through its
cardinality.  This exact projection stores those seven missing counts as
two-bit values, quotienting the independent permutations of the five
columns in every row.
-/

namespace SeymourEight.FiveZExactRisk.HighMissingCompressed

open SeymourEight.FiveZExactRisk

def projectRaw (bits : BitVec 280) (u v : Nat) : Bool :=
  if u < 7 then
    if v < 7 then FiveZExactRisk.pArc bits u v
    else FiveZExactRisk.pToH bits u (v - 7)
  else
    FiveZExactRisk.hToP bits (u - 7) v

def pArc (raw : Nat → Nat → Bool) (i j : Nat) : Bool := raw i j
def pToH (raw : Nat → Nat → Bool) (i h : Nat) : Bool := raw i (7 + h)
def hToP (raw : Nat → Nat → Bool) (h i : Nat) : Bool := raw (7 + h) i

def pOut (raw : Nat → Nat → Bool) (i : Nat) : BitVec 8 :=
  count 7 (pArc raw i)

def pHOut (raw : Nat → Nat → Bool) (i : Nat) : BitVec 8 :=
  count 3 (pToH raw i)

def rowMissing (missing : Nat → BitVec 2) (i : Nat) : BitVec 8 :=
  (missing i).zeroExtend 8

def pZOut (missing : Nat → BitVec 2) (i : Nat) : BitVec 8 :=
  5 - rowMissing missing i

def totalHToP (raw : Nat → Nat → Bool) : BitVec 8 :=
  count 21 fun q => hToP raw (q / 7) (q % 7)

def totalPToH (raw : Nat → Nat → Bool) : BitVec 8 :=
  count 21 fun q => pToH raw (q / 3) (q % 3)

def totalMissingPZ (missing : Nat → BitVec 2) : BitVec 8 :=
  sumCount 7 (rowMissing missing)

def reachedPViaPOrH (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  any 7 (fun middle =>
    decide (middle ≠ i) && decide (middle ≠ j) &&
      pArc raw i middle && pArc raw middle j) ||
  any 3 (fun h => pToH raw i h && hToP raw h j)

def secondPViaPOrH (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  decide (j ≠ i) && !pArc raw i j && reachedPViaPOrH raw i j

def secondPCount (raw : Nat → Nat → Bool) (i : Nat) : BitVec 8 :=
  count 7 (secondPViaPOrH raw i)

def fiveZExternalLower (missing : Nat → BitVec 2) (i : Nat) : BitVec 8 :=
  if rowMissing missing i = 0 then 8
  else if rowMissing missing i = 1 then 6
  else 5

def pDegree (raw : Nat → Nat → Bool) (missing : Nat → BitVec 2)
    (i : Nat) : BitVec 8 :=
  pZOut missing i + pHOut raw i + pOut raw i

def pNonSeymourUnionEight (raw : Nat → Nat → Bool)
    (missing : Nat → BitVec 2) (i : Nat) : Bool :=
  (secondPCount raw i + fiveZExternalLower missing i).ult
    (pDegree raw missing i + pHOut raw i)

def totalPOut (raw : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 7 (pOut raw)

def internalMissing (raw : Nat → Nat → Bool) : BitVec 8 :=
  21 - totalPOut raw

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 6 else if beta.ule 2 then 5 else if beta.ule 5 then 4
  else if beta.ule 9 then 3 else if beta.ule 14 then 2
  else if beta.ule 20 then 1 else 0

def sharpKing (raw : Nat → Nat → Bool) : Bool :=
  any 7 fun i => (sharpKingLower (internalMissing raw)).ule
    (pOut raw i + secondPCount raw i)

def pRowKey (raw : Nat → Nat → Bool) (missing : Nat → BitVec 2)
    (i : Nat) : BitVec 8 :=
  rowMissing missing i * 32 + pHOut raw i * 8 + pOut raw i

def orderedP (raw : Nat → Nat → Bool) (missing : Nat → BitVec 2) : Bool :=
  all 6 fun i => (pRowKey raw missing (i + 1)).ule
    (pRowKey raw missing i)

def core (raw : Nat → Nat → Bool) (missing : Nat → BitVec 2) : Bool :=
  orientedSquare 7 (pArc raw) &&
  all 7 (fun i => all 3 fun h => !(pToH raw i h && hToP raw h i)) &&
  (11 : BitVec 8).ule (totalHToP raw) &&
  (totalMissingPZ missing).ule 3 &&
  all 7 (fun i => (8 : BitVec 8).ule (pDegree raw missing i)) &&
  all 7 (pNonSeymourUnionEight raw missing)

def allMissingCore (raw : Nat → Nat → Bool)
    (missing : Nat → BitVec 2) : Bool :=
  core raw missing && sharpKing raw && orderedP raw missing &&
    (totalHToP raw + totalPToH raw).ule 21 &&
    (21 + totalMissingPZ missing).ule (totalPOut raw + totalPToH raw) &&
    (4 : BitVec 8).ule (totalPToH raw)

end SeymourEight.FiveZExactRisk.HighMissingCompressed
