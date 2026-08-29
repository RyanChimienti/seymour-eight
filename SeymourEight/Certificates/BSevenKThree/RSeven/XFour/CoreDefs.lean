import SeymourEight.Shared.FiniteCore

/-!
# Compact finite core for the hardest `r = 7`, `x = 4` rows

The 221 primary bits retain the induced arcs on `A`, the directed incidences
inside `P`, both directions between `P` and `H = A \ {a₁}`, and five possible
`P → Z` columns.  Since `r = 7`, the set `Q` is empty; consequently the
inner-Seymour Hall defect is computed directly from `P → Z` and requires no
anonymous signature variables.
-/

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := BitVec 221

/- The `a₁` row is fixed, and orientation fixes the three reverse `A₁ → a₁`
entries.  Only the four possible `X → a₁` arcs and the 42 directed arcs among
the other seven vertices need bits. -/
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
  bits.getLsbD (186 + 5 * p + z)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true else hToP bits (a - 1) p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if a = 0 then false else pToH bits p (a - 1)

/- Local indices are `A = 0,...,7`, `P = 8,...,14`, and active `Z` columns
start at 15.  Outgoing arcs from `Z` are intentionally projected away. -/
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
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pToH bits p)
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
  all 4 fun x =>
    any 3 (fun a => aArc bits (1 + a) (4 + x)) ||
      any 7 (fun p => pToH bits p (3 + x))

def allZReached (zCount : Nat) (bits : Encoding) : Bool :=
  all zCount fun z => any 7 fun p => pToZ bits p z

def inactiveZZero (zCount : Nat) (bits : Encoding) : Bool :=
  all 7 fun p => all (5 - zCount) fun j => !pToZ bits p (zCount + j)

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
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 7 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 7 (pOut bits)
def totalHOut (bits : Encoding) : BitVec 8 :=
  sumCount 7 fun h => aOut bits (1 + h) + hPOut bits h

def aMissing (bits : Encoding) : BitVec 8 :=
  28 - sumCount 8 (aOut bits)

def externalMissing (zCount : Nat) (bits : Encoding) : BitVec 8 :=
  BitVec.ofNat 8 (7 * zCount) - totalPToZ zCount bits

def internalMissing (bits : Encoding) : BitVec 8 := 21 - totalPOut bits

def crossMissing (bits : Encoding) : BitVec 8 :=
  49 - totalPToH bits - totalHToP bits

def alpha (bits : Encoding) : BitVec 8 :=
  12 - 3 * aMissing bits - totalPToH bits

def etaH (bits : Encoding) : BitVec 8 := totalHOut bits - 56

def effectiveAtRowSize (s v1 v2 v3 v4 v5 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else v5

/- The individual effective-target bound for five external targets.  Only
rows with at most nine missing incidences are used by the capacity-twelve
cover. -/
def individualEffectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 5 bits
  let s := pZOut 5 bits p
  if m == 0 then effectiveAtRowSize s 12 9 8 7 6
  else if m == 1 then effectiveAtRowSize s 11 9 8 7 6
  else if m == 2 then effectiveAtRowSize s 10 8 7 7 6
  else if m == 3 then effectiveAtRowSize s 9 8 7 6 6
  else if m == 4 then effectiveAtRowSize s 8 7 7 6 6
  else if m == 5 then effectiveAtRowSize s 7 7 6 6 5
  else if m == 6 then effectiveAtRowSize s 6 6 6 6 5
  else if m == 7 then effectiveAtRowSize s 5 6 6 5 5
  else if m == 8 then effectiveAtRowSize s 4 5 5 5 5
  else if m == 9 then effectiveAtRowSize s 3 5 5 5 5
  else if m == 10 then effectiveAtRowSize s 2 4 5 5 4
  else if m == 11 then effectiveAtRowSize s 1 4 4 4 4
  else if m == 12 then effectiveAtRowSize s 0 3 4 4 4
  else if m == 13 then effectiveAtRowSize s 0 3 4 4 4
  else effectiveAtRowSize s 0 2 3 4 4

def pEffectiveCondition (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount 5 bits p + individualEffectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut 5 bits p)

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 6 else if beta.ule 2 then 5 else if beta.ule 5 then 4
  else if beta.ule 9 then 3 else if beta.ule 14 then 2
  else if beta.ule 20 then 1 else 0

def sharpKing (bits : Encoding) : Bool :=
  any 7 fun p => (sharpKingLower (internalMissing bits)).ule
    (pOut bits p + pSecondPCount 5 bits p)

def pRowKey (bits : Encoding) (p : Nat) : BitVec 32 :=
  (directCount 5 bits (8 + p)).zeroExtend 32 * 4096 +
    (pZOut 5 bits p).zeroExtend 32 * 256 +
    (pHOut bits p).zeroExtend 32 * 16 + (pOut bits p).zeroExtend 32

def orderedP (bits : Encoding) : Bool :=
  all 6 fun p => (pRowKey bits (p + 1)).ule (pRowKey bits p)

def zColumnCode (bits : Encoding) (z : Nat) : BitVec 8 :=
  count 7 fun p => pToZ bits p z

def orderedZ (bits : Encoding) : Bool :=
  all 4 fun z => (zColumnCode bits (z + 1)).ule (zColumnCode bits z)

def orderedStructuralClasses (bits : Encoding) : Bool :=
  all 2 (fun a => (aPOut bits (2 + a)).ule (aPOut bits (1 + a))) &&
    all 3 (fun x => (aPOut bits (5 + x)).ule (aPOut bits (4 + x)))

def degreeAndDualConditions (bits : Encoding) : Bool :=
  (37 + 3 * aMissing bits).ule (totalHToP bits) &&
    (totalPToH bits + 3 * aMissing bits).ule 12 &&
    (2 * (3 + aMissing bits)).ule (etaH bits) &&
    alpha bits + 6 + 3 * aMissing bits ==
      etaH bits + aMissing bits + crossMissing bits

def commonCore (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits &&
    everyXReached bits && allZReached 5 bits &&
    aMinimumAndDegree bits && all 8 (aNonSeymour 5 bits) &&
    pMinimumDegree 5 bits && all 7 (pEffectiveCondition bits) &&
    all 8 (hallCondition 5 bits) && all 8 (degreeThreeTieCondition bits) &&
    degreeThreeClassification bits && threeInnerWitnesses bits &&
    degreeAndDualConditions bits && sharpKing bits

def exactLeaf (m delta d : Nat) (bits : Encoding) : Bool :=
  commonCore bits && externalMissing 5 bits == BitVec.ofNat 8 m &&
    aMissing bits == BitVec.ofNat 8 delta &&
    alpha bits + internalMissing bits == BitVec.ofNat 8 d

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core
