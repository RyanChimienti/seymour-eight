import SeymourEight.Shared.FiniteCore

/-!
# Finite core for the `r = 7`, `x = 2` families

The layout retains `A[8]`, `P[7]`, and six slots for `Z`.  The parameter
`zCount` activates the first four, five, or six `Z` columns, so the three
top-level rows share one encoding and one collection of graph predicates.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := BitVec 225

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (8 * i + j)

def directedIndex (i j : Nat) : Nat :=
  6 * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (64 + directedIndex i j)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (106 + 4 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  bits.getLsbD (134 + 7 * h + p)

def pToZ (bits : Encoding) (p z : Nat) : Bool :=
  bits.getLsbD (162 + 6 * p + z)

def rToP (bits : Encoding) (r p : Nat) : Bool :=
  bits.getLsbD (204 + 7 * r + p)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true
  else if a < 5 then hToP bits (a - 1) p
  else rToP bits (a - 5) p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if 0 < a && a < 5 then pToH bits p (a - 1) else false

def coreArc (zCount : Nat) (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 15 + zCount then pToZ bits (u - 8) (v - 15)
    else false
  else false

def directCount (zCount : Nat) (bits : Encoding) (u : Nat) : BitVec 8 :=
  count (15 + zCount) (coreArc zCount bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 := count 8 (aArc bits a)
def aPOut (bits : Encoding) (a : Nat) : BitVec 8 := count 7 (aToP bits a)
def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 4 (pToH bits p)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 7 (hToP bits h)
def pZOut (zCount : Nat) (bits : Encoding) (p : Nat) : BitVec 8 :=
  count zCount (pToZ bits p)

def reachesLocal (zCount : Nat) (bits : Encoding)
    (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc zCount bits source middle && coreArc zCount bits middle target

def strictSecondLocal (zCount : Nat) (bits : Encoding)
    (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc zCount bits source target &&
    reachesLocal zCount bits source target

def localSecondCount (zCount : Nat) (bits : Encoding)
    (source : Nat) : BitVec 8 :=
  count (15 + zCount) (strictSecondLocal zCount bits source)

def aNonSeymour (zCount : Nat) (bits : Encoding) (a : Nat) : Bool :=
  (localSecondCount zCount bits a).ult (directCount zCount bits a)

def pNonSeymour (zCount : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (localSecondCount zCount bits (8 + p)).ult
    (directCount zCount bits (8 + p))

def pSecondPCount (zCount : Nat) (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => strictSecondLocal zCount bits (8 + p) (8 + q)

/-- Index of one of the nine exact outneighbors of `a1`: `A1[2]` followed
by `P[7]`. -/
def aOneNeighbor (d : Nat) : Nat := if d < 2 then 1 + d else 8 + (d - 2)

def aOnePairLeft (q : Nat) : Nat :=
  if q < 8 then 0 else if q < 15 then 1 else if q < 21 then 2
  else if q < 26 then 3 else if q < 30 then 4 else if q < 33 then 5
  else if q < 35 then 6 else 7

def aOnePairRight (q : Nat) : Nat :=
  if q < 8 then 1 + q else if q < 15 then 2 + (q - 8)
  else if q < 21 then 3 + (q - 15) else if q < 26 then 4 + (q - 21)
  else if q < 30 then 5 + (q - 26) else if q < 33 then 6 + (q - 30)
  else if q < 35 then 7 + (q - 33) else 8

def retainedAfterAOnePairDeletion (left right vertex : Nat) : Bool :=
  if 1 ≤ vertex && vertex < 3 then
    decide (vertex - 1 ≠ left) && decide (vertex - 1 ≠ right)
  else if 8 ≤ vertex && vertex < 15 then
    decide (vertex - 6 ≠ left) && decide (vertex - 6 ≠ right)
  else false

def aOnePairDeletionReached (zCount : Nat) (bits : Encoding)
    (left right target : Nat) : Bool :=
  decide (target ≠ 0) && !retainedAfterAOnePairDeletion left right target &&
    any 15 fun middle => retainedAfterAOnePairDeletion left right middle &&
      coreArc zCount bits middle target

def aOnePairDeletionExpands (zCount : Nat) (bits : Encoding) : Bool :=
  (7 : BitVec 8).ule
    (count (15 + zCount) (aOnePairDeletionReached zCount bits 0 1))

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)

def orientedP (bits : Encoding) : Bool :=
  all 7 fun i => all 7 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)

def orientedPH (bits : Encoding) : Bool :=
  all 7 fun p => all 4 fun h => !(pToH bits p h && hToP bits h p)

def fixedA (bits : Encoding) : Bool :=
  aArc bits 0 1 && aArc bits 0 2 &&
  all 5 (fun i => !aArc bits 0 (3 + i)) &&
  all 6 fun q =>
    let a := q / 3
    let r := q % 3
    !aArc bits (1 + a) (5 + r)

def everyXReached (bits : Encoding) : Bool :=
  all 2 fun x =>
    any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
      any 7 (fun p => pToH bits p (2 + x))

def allZReached (zCount : Nat) (bits : Encoding) : Bool :=
  all zCount fun z => any 7 fun p => pToZ bits p z

def inactiveZZero (zCount : Nat) (bits : Encoding) : Bool :=
  if zCount = 6 then true
  else all 7 fun p => all (6 - zCount) fun j => !pToZ bits p (zCount + j)

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a =>
    (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (7 : BitVec 8).ule (aPOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aPOut bits a)

def pMinimumDegree (zCount : Nat) (bits : Encoding) : Bool :=
  all 7 fun p =>
    (8 : BitVec 8).ule
      (pOut bits p + pHOut bits p + pZOut zCount bits p)

def totalPToZ (zCount : Nat) (bits : Encoding) : BitVec 8 :=
  sumCount 7 (pZOut zCount bits)

def totalPToH (bits : Encoding) : BitVec 8 := sumCount 7 (pHOut bits)
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 4 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 7 (pOut bits)

def externalMissing (zCount : Nat) (bits : Encoding) : BitVec 8 :=
  BitVec.ofNat 8 (7 * zCount) - totalPToZ zCount bits

def effectiveAtRowSize (s v1 v2 v3 v4 v5 v6 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else if s == 5 then v5 else v6

/- The individual effective-target bound for five active external targets.
Rows with fewer active `Z` vertices use separate weaker tables in the final
core. -/
def individualEffectiveLowerFive (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 5 bits
  let s := pZOut 5 bits p
  if m == 0 then effectiveAtRowSize s 12 9 8 7 6 6
  else if m == 1 then effectiveAtRowSize s 11 9 8 7 6 6
  else if m == 2 then effectiveAtRowSize s 10 8 7 7 6 6
  else if m == 3 then effectiveAtRowSize s 9 8 7 6 6 6
  else if m == 4 then effectiveAtRowSize s 8 7 7 6 6 6
  else if m == 5 then effectiveAtRowSize s 7 7 6 6 5 5
  else if m == 6 then effectiveAtRowSize s 6 6 6 6 5 5
  else if m == 7 then effectiveAtRowSize s 5 6 6 5 5 5
  else if m == 8 then effectiveAtRowSize s 4 5 5 5 5 5
  else if m == 9 then effectiveAtRowSize s 3 5 5 5 5 5
  else if m == 10 then effectiveAtRowSize s 2 4 5 5 4 4
  else if m == 11 then effectiveAtRowSize s 1 4 4 4 4 4
  else if m == 12 then effectiveAtRowSize s 0 3 4 4 4 4
  else if m == 13 then effectiveAtRowSize s 0 3 4 4 4 4
  else effectiveAtRowSize s 0 2 3 4 4 4

def individualEffectiveLowerFour (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 4 bits
  let s := pZOut 4 bits p
  if m == 0 then effectiveAtRowSize s 11 9 8 7 7 7
  else if m == 1 then effectiveAtRowSize s 10 8 7 7 7 7
  else if m == 2 then effectiveAtRowSize s 9 8 7 6 6 6
  else if m == 3 then effectiveAtRowSize s 8 7 7 6 6 6
  else if m == 4 then effectiveAtRowSize s 7 7 6 6 6 6
  else if m == 5 then effectiveAtRowSize s 6 6 6 6 6 6
  else if m == 6 then effectiveAtRowSize s 5 6 6 5 5 5
  else if m == 7 then effectiveAtRowSize s 4 5 5 5 5 5
  else if m == 8 then effectiveAtRowSize s 3 5 5 5 5 5
  else if m == 9 then effectiveAtRowSize s 2 4 5 5 5 5
  else effectiveAtRowSize s 1 4 4 4 4 4

def individualEffectiveLowerThree (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 3 bits
  let s := pZOut 3 bits p
  if m == 0 then effectiveAtRowSize s 10 8 7 7 7 7
  else if m == 1 then effectiveAtRowSize s 9 8 7 7 7 7
  else if m == 2 then effectiveAtRowSize s 8 7 7 7 7 7
  else if m == 3 then effectiveAtRowSize s 7 7 7 7 7 7
  else if m == 4 then effectiveAtRowSize s 6 6 6 6 6 6
  else if m == 5 then effectiveAtRowSize s 5 6 6 6 6 6
  else effectiveAtRowSize s 4 5 5 5 5 5

def individualEffectiveLowerSix (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 6 bits
  let s := pZOut 6 bits p
  if m == 0 then effectiveAtRowSize s 9 9 9 9 9 6
  else if m == 1 then effectiveAtRowSize s 9 9 9 9 6 6
  else if m == 2 then effectiveAtRowSize s 9 9 9 7 6 6
  else if m == 3 then effectiveAtRowSize s 9 9 7 7 6 5
  else if m == 4 then effectiveAtRowSize s 9 8 7 6 6 5
  else if m == 5 then effectiveAtRowSize s 8 7 7 6 6 5
  else if m == 6 then effectiveAtRowSize s 7 7 6 6 5 5
  else if m == 7 then effectiveAtRowSize s 6 6 6 6 5 5
  else if m == 8 then effectiveAtRowSize s 5 6 6 5 5 5
  else if m == 9 then effectiveAtRowSize s 4 5 5 5 5 4
  else if m == 10 then effectiveAtRowSize s 3 5 5 5 5 4
  else if m == 11 then effectiveAtRowSize s 2 4 5 5 4 4
  else if m == 12 then effectiveAtRowSize s 1 4 4 4 4 4
  else if m == 13 then effectiveAtRowSize s 0 3 4 4 4 4
  else if m == 14 then effectiveAtRowSize s 0 3 4 4 4 4
  else if m == 15 then effectiveAtRowSize s 0 2 3 4 4 3
  else effectiveAtRowSize s 0 2 3 3 3 3

def individualEffectiveLower (zCount : Nat) (bits : Encoding)
    (p : Nat) : BitVec 8 :=
  if zCount = 4 then individualEffectiveLowerFour bits p
  else if zCount = 5 then individualEffectiveLowerFive bits p
  else individualEffectiveLowerSix bits p

def pEffectiveCondition (zCount : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount zCount bits p + individualEffectiveLower zCount bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut zCount bits p)

def pEffectiveConditionFive (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount 5 bits p + individualEffectiveLowerFive bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut 5 bits p)

def internalMissing (bits : Encoding) : BitVec 8 := 21 - totalPOut bits

def hMissing (bits : Encoding) : BitVec 8 :=
  6 - count 16 fun q =>
    let i := q / 4
    let j := q % 4
    decide (i < j) &&
      (aArc bits (1 + i) (1 + j) || aArc bits (1 + j) (1 + i))

def hDefect (bits : Encoding) : BitVec 8 := totalHToP bits - 18

def xTwoScalarPresolve (bits : Encoding) : Bool :=
  let m := externalMissing 5 bits
  let eta := hMissing bits
  let theta := hDefect bits
  if m.ule 3 then (3 + eta).ule theta
  else if m.ule 5 then (2 + eta).ule theta
  else if m.ule 13 then (1 + eta).ule theta
  else eta.ule theta

def xEligible (bits : Encoding) (x : Nat) : Bool :=
  aOut bits (3 + x) + aPOut bits (3 + x) == 8 &&
    aArc bits (3 + x) 0 && aArc bits (3 + x) 5 &&
      aArc bits (3 + x) 6 && aArc bits (3 + x) 7

def eligibleCount (bits : Encoding) : BitVec 8 := count 2 (xEligible bits)

def xReachedInH (bits : Encoding) (x target : Nat) : Bool :=
  decide (x ≠ target) &&
    (aArc bits (3 + x) (3 + target) || any 4 fun middle =>
      decide (middle ≠ 2 + x) && decide (middle ≠ 2 + target) &&
        aArc bits (3 + x) (1 + middle) &&
          aArc bits (1 + middle) (3 + target))

def xReachCount (bits : Encoding) (x : Nat) : BitVec 8 :=
  count 2 (xReachedInH bits x)

def eligibleAdmissible (bits : Encoding) (x : Nat) : Bool :=
  !xEligible bits x ||
    ((1 : BitVec 8).ule (aPOut bits (3 + x)) &&
      (aPOut bits (3 + x) * (xReachCount bits x + 2)).ule
        (externalMissing 5 bits))

def retainedAfterAOneDeletion (bits : Encoding) (x middle : Nat) : Bool :=
  decide (middle ≠ 0) && coreArc 5 bits (3 + x) middle

def xDeletionExpands (bits : Encoding) (x : Nat) : Bool :=
  (7 : BitVec 8).ule (count 20 fun target =>
    decide (target ≠ 3 + x) &&
      !retainedAfterAOneDeletion bits x target &&
      any 15 fun middle => retainedAfterAOneDeletion bits x middle &&
        coreArc 5 bits middle target)

def eligibleStructure (bits : Encoding) : Bool :=
  (2 + hMissing bits).ule (hDefect bits + eligibleCount bits) &&
    all 2 (eligibleAdmissible bits) &&
    all 2 fun x => !xEligible bits x || xDeletionExpands bits x

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 6 else if beta.ule 2 then 5 else if beta.ule 5 then 4
  else if beta.ule 9 then 3 else if beta.ule 14 then 2
  else if beta.ule 20 then 1 else 0

def sharpKing (zCount : Nat) (bits : Encoding) : Bool :=
  any 7 fun p => (sharpKingLower (internalMissing bits)).ule
    (pOut bits p + pSecondPCount zCount bits p)

def pRowKey (zCount : Nat) (bits : Encoding) (p : Nat) : BitVec 16 :=
  (directCount zCount bits (8 + p)).zeroExtend 16 * 4096 +
    (pZOut zCount bits p).zeroExtend 16 * 256 +
    (pHOut bits p).zeroExtend 16 * 16 + (pOut bits p).zeroExtend 16

def orderedP (zCount : Nat) (bits : Encoding) : Bool :=
  all 6 fun p => (pRowKey zCount bits (p + 1)).ule (pRowKey zCount bits p)

def zColumnCode (bits : Encoding) (z : Nat) : BitVec 8 :=
  count 7 fun p => pToZ bits p z

def orderedZ (zCount : Nat) (bits : Encoding) : Bool :=
  all (zCount - 1) fun z => (zColumnCode bits (z + 1)).ule (zColumnCode bits z)

def orderedStructuralClasses (bits : Encoding) : Bool :=
  (aPOut bits 2).ule (aPOut bits 1) &&
    (aPOut bits 4).ule (aPOut bits 3) &&
    all 2 (fun r => (aPOut bits (6 + r)).ule (aPOut bits (5 + r)))

def commonCore (zCount : Nat) (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits && fixedA bits &&
  everyXReached bits && allZReached zCount bits && inactiveZZero zCount bits &&
  (3 : BitVec 8).ule (count 4 fun q =>
    let a := q / 2
    let x := q % 2
    aArc bits (1 + a) (3 + x)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour zCount bits) &&
  pMinimumDegree zCount bits && all 7 (pNonSeymour zCount bits) &&
  aOnePairDeletionExpands zCount bits &&
  sharpKing zCount bits && orderedP zCount bits && orderedZ zCount bits &&
  orderedStructuralClasses bits

def fiveCore (bits : Encoding) : Bool :=
  commonCore 5 bits && all 7 (pEffectiveConditionFive bits) &&
  (19 : BitVec 8).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing 5 bits).ule 28

def smallCore (zCount : Nat) (bits : Encoding) : Bool :=
  commonCore zCount bits && all 7 (pEffectiveCondition zCount bits) &&
    (19 : BitVec 8).ule (totalHToP bits) &&
    (totalHToP bits + externalMissing zCount bits).ule
      (BitVec.ofNat 8 ((7 * zCount - 7 : Nat)))

end SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core
