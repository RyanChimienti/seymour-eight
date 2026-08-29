import SeymourEight.Shared.FiniteCore

/-!
# Finite core for the `r = 7`, `x = 5` rows

The 225 bits encode `A[8]`, `P[7]`, and `Z[3]`, using every bit for graph
incidences.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := BitVec 225

def aArc (bits : Encoding) (i j : Nat) : Bool := bits.getLsbD (8 * i + j)
def directedIndex (i j : Nat) : Nat := 6 * i + if j < i then j else j - 1
def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i != j) && bits.getLsbD (64 + directedIndex i j)
def pToH (bits : Encoding) (p h : Nat) : Bool := bits.getLsbD (106 + 7 * p + h)
def hToP (bits : Encoding) (h p : Nat) : Bool := bits.getLsbD (155 + 7 * h + p)
def pToZ (bits : Encoding) (p z : Nat) : Bool := bits.getLsbD (204 + 3 * p + z)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true else hToP bits (a - 1) p
def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if 0 < a then pToH bits p (a - 1) else false

def coreArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 18 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def directCount (bits : Encoding) (u : Nat) : BitVec 8 := count 18 (coreArc bits u)
def aOut (bits : Encoding) (a : Nat) : BitVec 8 := count 8 (aArc bits a)
def aPOut (bits : Encoding) (a : Nat) : BitVec 8 := count 7 (aToP bits a)
def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pToH bits p)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 7 (hToP bits h)
def pZOut (bits : Encoding) (p : Nat) : BitVec 8 := count 3 (pToZ bits p)

theorem pDegree_eq_directCount (bits : Encoding) (p : Nat) (hp : p < 7) :
    pOut bits p + pHOut bits p + pZOut bits p = directCount bits (8 + p) := by
  have h8 : ¬8 + p < 8 := by omega
  have h15 : 8 + p < 15 := by omega
  simp [pOut, pHOut, pZOut, directCount, count, coreArc, pToA,
    h8, h15, bitCount]
  ac_rfl

def reachesLocal (bits : Encoding) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle != source) && decide (middle != target) &&
      coreArc bits source middle && coreArc bits middle target
def strictSecondLocal (bits : Encoding) (source target : Nat) : Bool :=
  decide (target != source) && !coreArc bits source target &&
    reachesLocal bits source target
def localSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 18 (strictSecondLocal bits source)
def aNonSeymour (bits : Encoding) (a : Nat) : Bool :=
  (localSecondCount bits a).ult (directCount bits a)
def pNonSeymour (bits : Encoding) (p : Nat) : Bool :=
  (localSecondCount bits (8 + p)).ult (directCount bits (8 + p))
def pSecondPCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => strictSecondLocal bits (8 + p) (8 + q)

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)
def orientedP (bits : Encoding) : Bool :=
  all 7 fun i => all 7 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)
def orientedPH (bits : Encoding) : Bool :=
  all 7 fun p => all 7 fun h => !(pToH bits p h && hToP bits h p)

def fixedA (bits : Encoding) : Bool :=
  aArc bits 0 1 && aArc bits 0 2 && all 5 (fun x => !aArc bits 0 (3 + x))
def everyXReached (bits : Encoding) : Bool :=
  all 5 fun x =>
    any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
      any 7 (fun p => pToH bits p (2 + x))
def allZReached (bits : Encoding) : Bool :=
  all 3 fun z => any 7 fun p => pToZ bits p z

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a =>
    (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (7 : BitVec 8).ule (aPOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aPOut bits a)
def pMinimumDegree (bits : Encoding) : Bool :=
  all 7 fun p => (8 : BitVec 8).ule (pOut bits p + pHOut bits p + pZOut bits p)

def totalPToZ (bits : Encoding) : BitVec 8 := sumCount 7 (pZOut bits)
def totalPToH (bits : Encoding) : BitVec 8 := sumCount 7 (pHOut bits)
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 7 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 7 (pOut bits)
def externalMissing (bits : Encoding) : BitVec 8 := 21 - totalPToZ bits
def internalMissing (bits : Encoding) : BitVec 8 := 21 - totalPOut bits
def combinedDefect (bits : Encoding) : BitVec 8 :=
  40 - totalPToH bits - totalPOut bits
def hDefect (bits : Encoding) : BitVec 8 := totalHToP bits - 30
def hMissing (bits : Encoding) : BitVec 8 :=
  21 - count 49 fun q =>
    let i := q / 7
    let j := q % 7
    decide (i < j) &&
      (aArc bits (1 + i) (1 + j) || aArc bits (1 + j) (1 + i))
def xEligible (bits : Encoding) (x : Nat) : Bool :=
  aOut bits (3 + x) + aPOut bits (3 + x) == 8 && aArc bits (3 + x) 0
def xExactDegree (bits : Encoding) (x : Nat) : Bool :=
  aOut bits (3 + x) + aPOut bits (3 + x) == 8
def exactDegreeCount (bits : Encoding) : BitVec 8 := count 5 (xExactDegree bits)
def eligibleCount (bits : Encoding) : BitVec 8 := count 5 (xEligible bits)
def retainedAfterAOneDeletion (bits : Encoding) (x middle : Nat) : Bool :=
  decide (middle != 0) && coreArc bits (3 + x) middle
def atLeastSeven (value : BitVec 8) : Bool := decide (7 ≤ value.toNat)
def deletionTarget (bits : Encoding) (x target : Nat) : Bool :=
  decide (target ≠ 3 + x) &&
    !retainedAfterAOneDeletion bits x target &&
    any 15 fun middle => retainedAfterAOneDeletion bits x middle &&
      coreArc bits middle target
def deletionCount (bits : Encoding) (x : Nat) : BitVec 8 :=
  count 18 (deletionTarget bits x)
def xDeletionExpands (bits : Encoding) (x : Nat) : Bool :=
  atLeastSeven (deletionCount bits x)
def dualTail (bits : Encoding) : Bool :=
  (5 : BitVec 8).ule (hDefect bits + exactDegreeCount bits) &&
    all 5 fun x => !xEligible bits x || xDeletionExpands bits x

def effectiveAtRowSize (s v1 v2 v3 v4 v5 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else v5
def individualEffectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing bits
  let s := pZOut bits p
  if m == 0 then effectiveAtRowSize s 10 8 7 7 7
  else if m == 1 then effectiveAtRowSize s 9 8 7 7 7
  else if m == 2 then effectiveAtRowSize s 8 7 7 7 7
  else if m == 3 then effectiveAtRowSize s 7 7 6 6 6
  else if m == 4 then effectiveAtRowSize s 6 6 6 6 6
  else if m == 5 then effectiveAtRowSize s 5 6 6 6 6
  else effectiveAtRowSize s 4 5 5 5 5
def pEffectiveCondition (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + individualEffectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut bits p)

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 6 else if beta.ule 2 then 5 else if beta.ule 5 then 4
  else if beta.ule 9 then 3 else if beta.ule 14 then 2
  else if beta.ule 20 then 1 else 0
def sharpKing (bits : Encoding) : Bool :=
  any 7 fun p => (sharpKingLower (internalMissing bits)).ule
    (pOut bits p + pSecondPCount bits p)

def pRowKey (bits : Encoding) (p : Nat) : BitVec 16 :=
  (pOut bits p + pHOut bits p + pZOut bits p).zeroExtend 16 * 4096 +
    (pZOut bits p).zeroExtend 16 * 256 +
    (pHOut bits p).zeroExtend 16 * 16 + (pOut bits p).zeroExtend 16
def orderedP (bits : Encoding) : Bool :=
  all 6 fun p => (pRowKey bits (p + 1)).ule (pRowKey bits p)
def zColumnCode (bits : Encoding) (z : Nat) : BitVec 8 :=
  count 7 fun p => pToZ bits p z
def orderedZ (bits : Encoding) : Bool :=
  all 2 fun z => (zColumnCode bits (z + 1)).ule (zColumnCode bits z)
def orderedStructuralClasses (bits : Encoding) : Bool :=
  (aPOut bits 2).ule (aPOut bits 1) &&
    all 4 (fun x => (aPOut bits (4 + x)).ule (aPOut bits (3 + x)))

def baseCore (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits && fixedA bits &&
  everyXReached bits && allZReached bits &&
  (3 : BitVec 8).ule (count 10 fun q =>
    aArc bits (1 + q / 5) (3 + q % 5)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour bits) &&
  pMinimumDegree bits && all 7 (pNonSeymour bits) &&
  all 7 (pEffectiveCondition bits) && dualTail bits && sharpKing bits &&
  orderedP bits && orderedZ bits && orderedStructuralClasses bits &&
  (30 : BitVec 8).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing bits).ule 35 &&
  (hDefect bits).ule (combinedDefect bits) &&
  (externalMissing bits + combinedDefect bits).ule 5

def easyCore (bits : Encoding) : Bool :=
  baseCore bits &&
    (!(externalMissing bits).ule 2 || !(combinedDefect bits == 3) ||
      !(hDefect bits == 2))

def hardCore (m : BitVec 8) (bits : Encoding) : Bool :=
  baseCore bits && externalMissing bits == m &&
    combinedDefect bits == 3 && hDefect bits == 2

def sliceCore (m : BitVec 8) (bits : Encoding) : Bool :=
  baseCore bits && externalMissing bits == m

def pExactEight (bits : Encoding) (p : Nat) : Bool :=
  pOut bits p + pHOut bits p + pZOut bits p == 8

/-- Exact accounting and the descending P-row order force an increasingly
long degree-eight suffix as the combined external/internal defect grows. -/
def degreeEightSuffix (bits : Encoding) : Bool :=
  let s := externalMissing bits + combinedDefect bits
  pExactEight bits 5 && pExactEight bits 6 &&
    (!(1 : BitVec 8).ule s || pExactEight bits 4) &&
    (!(2 : BitVec 8).ule s || pExactEight bits 3) &&
    (!(3 : BitVec 8).ule s || pExactEight bits 2) &&
    (!(4 : BitVec 8).ule s || pExactEight bits 1) &&
    (!(5 : BitVec 8).ule s || pExactEight bits 0)

def suffixCore (bits : Encoding) : Bool :=
  baseCore bits && degreeEightSuffix bits

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core
