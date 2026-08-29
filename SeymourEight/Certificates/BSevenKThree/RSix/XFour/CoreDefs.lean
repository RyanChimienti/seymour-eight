import SeymourEight.Shared.FiniteCore

/-!
# Projected finite core for the `r = 6`, `x = 4` families

The named local vertices are `A = 0,...,7`, `P = 8,...,13`, and the unique
member of `Q` at index 14.  The separate `pToZ` array has four columns; rows
with fewer `Z` vertices set the unused columns to false.  Outgoing arcs from
`Q` and `Z` are deliberately projected away.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

open Shared.FiniteCore

def aArc (arc : Nat → Nat → Bool) (a b : Nat) : Bool := arc a b
def pArc (arc : Nat → Nat → Bool) (p q : Nat) : Bool := arc (8 + p) (8 + q)
def aToP (arc : Nat → Nat → Bool) (a p : Nat) : Bool := arc a (8 + p)
def pToA (arc : Nat → Nat → Bool) (p a : Nat) : Bool := arc (8 + p) a
def aToQ (arc : Nat → Nat → Bool) (a : Nat) : Bool := arc a 14
def pToQ (arc : Nat → Nat → Bool) (p : Nat) : Bool := arc (8 + p) 14

def coreArc (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (u v : Nat) : Bool :=
  if u < 8 then
    if v < 15 then arc u v else false
  else if u < 14 then
    if v < 15 then arc u v
    else if v < 15 + zCount then
      pToZ (u - 8) (v - 15)
    else false
  else false

def aOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 8 (aArc arc a)
def aPOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 6 (aToP arc a)
def aBOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  aPOut arc a + bitCount (aToQ arc a)
def pOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 := count 6 (pArc arc p)
def pHOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 7 fun h => pToA arc p (1 + h)
def hPOut (arc : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 6 fun p => aToP arc (1 + h) p
def pZOut (zCount : Nat) (pToZ : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count zCount (pToZ p)
def pAuxOut (y zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  pZOut zCount pToZ p + if y = 0 then 0 else bitCount (pToQ arc p)

def aDegree (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  aOut arc a + aBOut arc a
def pDegree (y zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 := pOut arc p + pHOut arc p + pAuxOut y zCount arc pToZ p

def reachesLocal (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 14 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    arc source middle && arc middle target
def strictSecondLocal (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target && reachesLocal arc source target
def pSecondPCount (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 6 fun q => strictSecondLocal arc (8 + p) (8 + q)

def projectedReaches (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  any 15 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    coreArc zCount arc pToZ source middle && coreArc zCount arc pToZ middle target
def projectedSecond (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc zCount arc pToZ source target &&
    projectedReaches zCount arc pToZ source target
def projectedSecondCount (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (source : Nat) : BitVec 8 :=
  count (15 + zCount) (projectedSecond zCount arc pToZ source)

def innerReaches (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 8 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    aArc arc source middle && aArc arc middle target
def innerSecond (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !aArc arc source target && innerReaches arc source target
def innerSecondCount (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count 8 (innerSecond arc source)
def innerSeymour (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  (aOut arc source).ule (innerSecondCount arc source)
def degreeThree (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  aOut arc source == 3
def degreeThreeInner (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  degreeThree arc source && innerSeymour arc source

def degreeThreeClassification (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun source => all 8 fun target =>
    decide (source = target) || !degreeThree arc source ||
      degreeThreeInner arc source || !aArc arc source target ||
        degreeThreeInner arc target
def threeInnerWitnesses (arc : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (count 8 (degreeThreeInner arc))

def orientedA (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun i => !aArc arc i i && all 8 fun j =>
    decide (i = j) || !(aArc arc i j && aArc arc j i)
def orientedP (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun i => !pArc arc i i && all 6 fun j =>
    decide (i = j) || !(pArc arc i j && pArc arc j i)
def orientedPH (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun p => all 7 fun h => !(pToA arc p (1 + h) && aToP arc (1 + h) p)

def fixedAOne (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun j => arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 14)
def noPToAOne (arc : Nat → Nat → Bool) : Bool := all 6 fun p => !pToA arc p 0
def qInB (arc : Nat → Nat → Bool) : Bool := any 8 fun a => aToQ arc a
def everyXReached (arc : Nat → Nat → Bool) : Bool :=
  all 4 fun x => any 3 (fun a => aArc arc (1 + a) (4 + x)) ||
    any 6 (fun p => pToA arc p (4 + x))
def everyZReached (zCount : Nat) (pToZ : Nat → Nat → Bool) : Bool :=
  all zCount fun z => any 6 fun p => pToZ p z
def inactiveZZero (zCount : Nat) (pToZ : Nat → Nat → Bool) : Bool :=
  all 6 fun p => all (4 - zCount) fun j => !pToZ p (zCount + j)
def qReachStatus (y : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (any 3 (fun a => aToQ arc (1 + a)) || any 6 (pToQ arc)) == decide (y = 1)

def aConditions (arc : Nat → Nat → Bool) : Bool := all 8 fun a =>
  (3 : BitVec 8).ule (aOut arc a) &&
    (!(aOut arc a == 3) || (6 : BitVec 8).ule (aBOut arc a)) &&
    (8 : BitVec 8).ule (aDegree arc a)
def pConditions (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 6 fun p => (8 : BitVec 8).ule (pDegree y zCount arc pToZ p)
def aNonSeymour (zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 8 fun a => (projectedSecondCount zCount arc pToZ a).ult (aDegree arc a)
def pNonSeymour (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 6 fun p =>
    (projectedSecondCount zCount arc pToZ (8 + p)).ult
      (pDegree y zCount arc pToZ p)

def totalAOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 8 (aOut arc)
def totalPOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (pOut arc)
def totalPToH (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (pHOut arc)
def totalHToP (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 7 (hPOut arc)
def totalHToQ (arc : Nat → Nat → Bool) : BitVec 8 :=
  count 7 fun h => aToQ arc (1 + h)
def totalPToZ (zCount : Nat) (pToZ : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 6 (pZOut zCount pToZ)
def totalPToQ (arc : Nat → Nat → Bool) : BitVec 8 := count 6 (pToQ arc)
def totalPToAux (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  totalPToZ zCount pToZ + if y = 0 then 0 else totalPToQ arc
def totalHOut (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 7 fun h => aOut arc (1 + h) + hPOut arc h + bitCount (aToQ arc (1 + h))

def aMissing (arc : Nat → Nat → Bool) : BitVec 8 := 28 - totalAOut arc
def internalMissing (arc : Nat → Nat → Bool) : BitVec 8 := 15 - totalPOut arc
def externalMissing (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (6 * (y + zCount)) - totalPToAux y zCount arc pToZ
def alpha (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (12 + 3 * y) - 2 * aMissing arc - totalPToH arc
def etaH (arc : Nat → Nat → Bool) : BitVec 8 := totalHOut arc - 56
def hQDefect (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (4 + 3 * y) - totalHToQ arc
def crossMissing (arc : Nat → Nat → Bool) : BitVec 8 :=
  42 - totalPToH arc - totalHToP arc

def degreeAndDualConditions (y : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (BitVec.ofNat 8 (30 - 3 * y) + 2 * aMissing arc + hQDefect y arc).ule
      (totalHToP arc) &&
    ((3 + aMissing arc).ule (etaH arc)) &&
    alpha y arc + 3 + 2 * aMissing arc ==
      etaH arc + aMissing arc + hQDefect y arc + crossMissing arc

def effectiveAtRowSize (s v1 v2 v3 v4 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else v4

def individualEffectiveTable (four : Bool) (m s : BitVec 8) : BitVec 8 :=
  if four then
    if m == 0 then effectiveAtRowSize s 11 9 8 7
    else if m == 1 then effectiveAtRowSize s 10 8 7 7
    else if m == 2 then effectiveAtRowSize s 9 8 7 6
    else if m == 3 then effectiveAtRowSize s 8 7 7 6
    else if m == 4 then effectiveAtRowSize s 7 7 6 6
    else if m == 5 then effectiveAtRowSize s 6 6 6 6
    else if m == 6 then effectiveAtRowSize s 5 6 6 5
    else 0
  else
    if m == 0 then effectiveAtRowSize s 10 8 7 7
    else if m == 1 then effectiveAtRowSize s 9 8 7 7
    else if m == 2 then effectiveAtRowSize s 8 7 7 7
    else if m == 3 then effectiveAtRowSize s 7 7 6 6
    else if m == 4 then effectiveAtRowSize s 6 6 6 6
    else if m == 5 then effectiveAtRowSize s 5 5 6 6
    else if m == 6 then effectiveAtRowSize s 4 4 5 5
    else 0

def individualEffectiveLower (y zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  individualEffectiveTable (decide (y + zCount = 4))
    (externalMissing y zCount arc pToZ) (pAuxOut y zCount arc pToZ p)

def pEffectiveCondition (y zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : Bool :=
  (pSecondPCount arc p + individualEffectiveLower y zCount arc pToZ p + 1).ule
    (pOut arc p + 2 * pHOut arc p + pAuxOut y zCount arc pToZ p)

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 5 else if beta.ule 2 then 4 else if beta.ule 5 then 3
  else if beta.ule 9 then 2 else if beta.ule 14 then 1 else 0
def sharpKing (arc : Nat → Nat → Bool) : Bool :=
  any 6 fun p => (sharpKingLower (internalMissing arc)).ule
    (pOut arc p + pSecondPCount arc p)

def pRowKey (y zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 32 :=
  (pDegree y zCount arc pToZ p).zeroExtend 32 * 65536 +
    (pZOut zCount pToZ p).zeroExtend 32 * 4096 +
    (bitCount (pToQ arc p)).zeroExtend 32 * 2048 +
    (count 3 fun a => pToA arc p (1 + a)).zeroExtend 32 * 256 +
    (count 4 fun x => pToA arc p (4 + x)).zeroExtend 32 * 16 +
    (pOut arc p).zeroExtend 32
def orderedP (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 5 fun p => (pRowKey y zCount arc pToZ (p + 1)).ule
    (pRowKey y zCount arc pToZ p)
def orderedAClasses (arc : Nat → Nat → Bool) : Bool :=
  all 2 (fun a => (aBOut arc (2 + a)).ule (aBOut arc (1 + a))) &&
    all 3 (fun x => (aBOut arc (5 + x)).ule (aBOut arc (4 + x)))
def zIn (pToZ : Nat → Nat → Bool) (z : Nat) : BitVec 8 :=
  count 6 fun p => pToZ p z
def orderedZ (zCount : Nat) (pToZ : Nat → Nat → Bool) : Bool :=
  all (zCount - 1) fun z => (zIn pToZ (z + 1)).ule (zIn pToZ z)

def commonCore (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && fixedAOne arc &&
    noPToAOne arc && qInB arc &&
    everyXReached arc && everyZReached zCount pToZ && inactiveZZero zCount pToZ &&
    qReachStatus y arc && aConditions arc && pConditions y zCount arc pToZ &&
    aNonSeymour zCount arc pToZ && pNonSeymour y zCount arc pToZ &&
    degreeThreeClassification arc &&
    threeInnerWitnesses arc && degreeAndDualConditions y arc &&
    (externalMissing y zCount arc pToZ).ule 9 &&
    all 6 (pEffectiveCondition y zCount arc pToZ) && sharpKing arc &&
    orderedP y zCount arc pToZ && orderedAClasses arc && orderedZ zCount pToZ

def exactLeaf (m delta d high : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc + internalMissing arc == BitVec.ofNat 8 d &&
    count 6 (fun p => (9 : BitVec 8).ule (pDegree 1 3 arc pToZ p)) ==
      BitVec.ofNat 8 high

def defectLeaf (m delta d : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc + internalMissing arc == BitVec.ofNat 8 d

def capacityDefect (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  externalMissing 1 3 arc pToZ + 2 * aMissing arc +
    (alpha 1 arc + internalMissing arc)

def hardCore (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && (capacityDefect arc pToZ).ule 6

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
