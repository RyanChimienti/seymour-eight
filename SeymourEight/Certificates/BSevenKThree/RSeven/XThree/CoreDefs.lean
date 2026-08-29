import SeymourEight.Shared.FiniteCore

/-!
# Compact finite core for the `r = 7`, `x = 3` families

The lone vertex of `R` is retained in the eight-vertex `A` block, but is
excluded from the six-vertex set `H = A₁ ∪ X`.  Six external columns cover
all four parameter rows without introducing anonymous vertices.
-/

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := BitVec 228

def hDirectedIndex (i j : Nat) : Nat :=
  6 * i + if j < i then j else j - 1

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  if i = 0 then decide (1 ≤ j && j ≤ 3)
  else if j = 0 then
    if i ≤ 3 then false else bits.getLsbD (i - 4)
  else decide (i ≠ j) &&
    bits.getLsbD (4 + hDirectedIndex (i - 1) (j - 1))

def pDirectedIndex (i j : Nat) : Nat :=
  6 * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (46 + pDirectedIndex i j)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (88 + 7 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  bits.getLsbD (137 + 7 * h + p)

def pToZ (bits : Encoding) (p z : Nat) : Bool :=
  bits.getLsbD (186 + 6 * p + z)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true else hToP bits (a - 1) p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if a = 0 then false else pToH bits p (a - 1)

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
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pToH bits p)
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

def pSecondPCount (zCount : Nat) (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => strictSecondLocal zCount bits (8 + p) (8 + q)

def innerReaches (bits : Encoding) (source target : Nat) : Bool :=
  any 8 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      aArc bits source middle && aArc bits middle target

def innerSecond (bits : Encoding) (source target : Nat) : Bool :=
  decide (target ≠ source) && !aArc bits source target &&
    innerReaches bits source target

def innerSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 8 (innerSecond bits source)

def innerSeymour (bits : Encoding) (source : Nat) : Bool :=
  (aOut bits source).ule (innerSecondCount bits source)

def degreeThree (bits : Encoding) (source : Nat) : Bool :=
  aOut bits source == 3

def degreeThreeInner (bits : Encoding) (source : Nat) : Bool :=
  degreeThree bits source && innerSeymour bits source

def hallZReached (_zCount : Nat) (bits : Encoding)
    (source z : Nat) : Bool :=
  any 7 fun p => aToP bits source p && pToZ bits p z

def hallZCount (zCount : Nat) (bits : Encoding) (source : Nat) : BitVec 8 :=
  count zCount (hallZReached zCount bits source)

def hallCondition (zCount : Nat) (bits : Encoding) (source : Nat) : Bool :=
  !innerSeymour bits source ||
    ((1 : BitVec 8).ule (aPOut bits source) &&
      (hallZCount zCount bits source).ult (aPOut bits source))

def degreeThreeTieCondition (bits : Encoding) (source : Nat) : Bool :=
  !degreeThreeInner bits source || (7 : BitVec 8).ule (aPOut bits source)

def degreeThreeClassification (bits : Encoding) : Bool :=
  all 8 fun source => all 8 fun target =>
    decide (source = target) || !degreeThree bits source ||
      degreeThreeInner bits source || !aArc bits source target ||
        degreeThreeInner bits target

def threeInnerWitnesses (bits : Encoding) : Bool :=
  (3 : BitVec 8).ule (count 8 (degreeThreeInner bits))

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)

def orientedP (bits : Encoding) : Bool :=
  all 7 fun i => all 7 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)

def orientedPH (bits : Encoding) : Bool :=
  all 7 fun p => all 7 fun h => !(pToH bits p h && hToP bits h p)

def everyXReached (bits : Encoding) : Bool :=
  all 3 fun x =>
    any 3 (fun a => aArc bits (1 + a) (4 + x)) ||
      any 7 (fun p => pToH bits p (3 + x))

def rUnreached (bits : Encoding) : Bool :=
  all 3 (fun a => !aArc bits (1 + a) 7) &&
    all 7 (fun p => !pToH bits p 6)

def allZReached (zCount : Nat) (bits : Encoding) : Bool :=
  all zCount fun z => any 7 fun p => pToZ bits p z

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a =>
    (3 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 3) || (7 : BitVec 8).ule (aPOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aPOut bits a)

def pMinimumDegree (zCount : Nat) (bits : Encoding) : Bool :=
  all 7 fun p =>
    (8 : BitVec 8).ule
      (pOut bits p + pHOut bits p + pZOut zCount bits p)

def totalPToZ (zCount : Nat) (bits : Encoding) : BitVec 8 :=
  sumCount 7 (pZOut zCount bits)
def totalPToH (bits : Encoding) : BitVec 8 := sumCount 7 (pHOut bits)
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 6 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 7 (pOut bits)
def totalHOut (bits : Encoding) : BitVec 8 :=
  sumCount 6 fun h => aOut bits (1 + h) + hPOut bits h

def aMissing (bits : Encoding) : BitVec 8 :=
  28 - sumCount 8 (aOut bits)

def externalMissing (zCount : Nat) (bits : Encoding) : BitVec 8 :=
  BitVec.ofNat 8 (7 * zCount) - totalPToZ zCount bits

def internalMissing (bits : Encoding) : BitVec 8 := 21 - totalPOut bits
def crossMissing (bits : Encoding) : BitVec 8 :=
  42 - totalPToH bits - totalHToP bits

def degreeGain (bits : Encoding) : BitVec 8 :=
  let d := aMissing bits
  if d.ule 1 then 6 else if d == 2 then 9 else if d == 3 then 12 else 15

def alpha (bits : Encoding) : BitVec 8 :=
  15 - degreeGain bits - totalPToH bits

def etaH (bits : Encoding) : BitVec 8 := totalHOut bits - 48
def tau (bits : Encoding) : BitVec 8 := aOut bits 7 + aMissing bits - 4

def effectiveAtRowSize
    (s v1 v2 v3 v4 v5 v6 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else if s == 5 then v5 else v6

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

def individualEffectiveLowerSix (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 6 bits
  let s := pZOut 6 bits p
  if m == 0 then effectiveAtRowSize s 13 10 8 7 7 6
  else if m == 1 then effectiveAtRowSize s 12 9 8 7 6 6
  else if m == 2 then effectiveAtRowSize s 11 9 8 7 6 6
  else if m == 3 then effectiveAtRowSize s 10 8 7 7 6 5
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

def individualEffectiveLower (zCount : Nat) (bits : Encoding) (p : Nat) : BitVec 8 :=
  if zCount = 5 then individualEffectiveLowerFive bits p
  else individualEffectiveLowerSix bits p

def pEffectiveCondition (zCount : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount zCount bits p + individualEffectiveLower zCount bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut zCount bits p)

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 6 else if beta.ule 2 then 5 else if beta.ule 5 then 4
  else if beta.ule 9 then 3 else if beta.ule 14 then 2
  else if beta.ule 20 then 1 else 0

def sharpKing (zCount : Nat) (bits : Encoding) : Bool :=
  any 7 fun p => (sharpKingLower (internalMissing bits)).ule
    (pOut bits p + pSecondPCount zCount bits p)

def degreeAndDualConditions (bits : Encoding) : Bool :=
  (27 + degreeGain bits).ule (totalHToP bits) &&
    (totalPToH bits + degreeGain bits).ule 15 &&
    (aMissing bits).ule (tau bits + 1) && (tau bits).ule 3 &&
    (2 * (3 + tau bits)).ule (etaH bits) &&
    alpha bits + degreeGain bits == etaH bits + tau bits + crossMissing bits

def commonCore (zCount : Nat) (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits &&
    everyXReached bits && rUnreached bits && allZReached zCount bits &&
    aMinimumAndDegree bits && all 8 (aNonSeymour zCount bits) &&
    pMinimumDegree zCount bits && all 7 (pEffectiveCondition zCount bits) &&
    all 8 (hallCondition zCount bits) && all 8 (degreeThreeTieCondition bits) &&
    degreeThreeClassification bits && threeInnerWitnesses bits &&
    degreeAndDualConditions bits && sharpKing zCount bits

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core
