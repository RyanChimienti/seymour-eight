import SeymourEight.Shared.FiniteCore

/-!
# Finite core for the `r = 5`, `x = 4` families

The named vertices are `A = 0,...,7`, `P = 8,...,12`, and the two members
of `Q` at indices 13 and 14.  The separate `pToZ` array has two columns;
the one-external-target row sets its second column to false.
-/

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

open Shared.FiniteCore

def aArc (arc : Nat → Nat → Bool) (a b : Nat) : Bool := arc a b
def pArc (arc : Nat → Nat → Bool) (p q : Nat) : Bool := arc (8 + p) (8 + q)
def aToP (arc : Nat → Nat → Bool) (a p : Nat) : Bool := arc a (8 + p)
def pToA (arc : Nat → Nat → Bool) (p a : Nat) : Bool := arc (8 + p) a
def aToQ (arc : Nat → Nat → Bool) (a q : Nat) : Bool := arc a (13 + q)
def pToQ (arc : Nat → Nat → Bool) (p q : Nat) : Bool := arc (8 + p) (13 + q)

def coreArc (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (u v : Nat) : Bool :=
  if u < 8 then
    if v < 15 then arc u v else false
  else if u < 13 then
    if v < 15 then arc u v
    else if v < 15 + zCount then pToZ (u - 8) (v - 15)
    else false
  else false

def aOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 8 (aArc arc a)
def aPOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 5 (aToP arc a)
def aQOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 2 (aToQ arc a)
def aBOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  aPOut arc a + aQOut arc a
def pOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 := count 5 (pArc arc p)
def pHOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 7 fun h => pToA arc p (1 + h)
def hPOut (arc : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 5 fun p => aToP arc (1 + h) p
def pQOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 := count 2 (pToQ arc p)
def pZOut (zCount : Nat) (pToZ : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count zCount (pToZ p)
def pAuxOut (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 := pQOut arc p + pZOut zCount pToZ p

def aDegree (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  aOut arc a + aBOut arc a
def pDegree (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 := pOut arc p + pHOut arc p + pAuxOut zCount arc pToZ p

def reachesLocal (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 13 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    arc source middle && arc middle target
def strictSecondLocal (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target && reachesLocal arc source target
def pSecondPCount (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 5 fun q => strictSecondLocal arc (8 + p) (8 + q)

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
      degreeThreeInner arc source || !aArc arc source target || degreeThreeInner arc target
def threeInnerWitnesses (arc : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (count 8 (degreeThreeInner arc))

def orientedA (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun i => !aArc arc i i && all 8 fun j =>
    decide (i = j) || !(aArc arc i j && aArc arc j i)
def orientedP (arc : Nat → Nat → Bool) : Bool :=
  all 5 fun i => !pArc arc i i && all 5 fun j =>
    decide (i = j) || !(pArc arc i j && pArc arc j i)
def orientedPH (arc : Nat → Nat → Bool) : Bool :=
  all 5 fun p => all 7 fun h => !(pToA arc p (1 + h) && aToP arc (1 + h) p)

def fixedAOne (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun j => arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 13)
def noPToAOne (arc : Nat → Nat → Bool) : Bool := all 5 fun p => !pToA arc p 0
def qInB (arc : Nat → Nat → Bool) : Bool :=
  all 2 fun q => any 8 fun a => aToQ arc a q
def qReached (arc : Nat → Nat → Bool) (q : Nat) : Bool :=
  any 3 (fun a => aToQ arc (1 + a) q) || any 5 (fun p => pToQ arc p q)
def qReachStatus (y : Nat) (arc : Nat → Nat → Bool) : Bool :=
  count 2 (qReached arc) == BitVec.ofNat 8 y
def everyXReached (arc : Nat → Nat → Bool) : Bool :=
  all 4 fun x => any 3 (fun a => aArc arc (1 + a) (4 + x)) ||
    any 5 (fun p => pToA arc p (4 + x))
def everyZReached (zCount : Nat) (pToZ : Nat → Nat → Bool) : Bool :=
  all zCount fun z => any 5 fun p => pToZ p z
def inactiveZZero (zCount : Nat) (pToZ : Nat → Nat → Bool) : Bool :=
  all 5 fun p => all (2 - zCount) fun j => !pToZ p (zCount + j)

def aConditions (arc : Nat → Nat → Bool) : Bool := all 8 fun a =>
  (3 : BitVec 8).ule (aOut arc a) &&
    (!(aOut arc a == 3) || (5 : BitVec 8).ule (aBOut arc a)) &&
    (8 : BitVec 8).ule (aDegree arc a)
def pConditions (zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 5 fun p => (8 : BitVec 8).ule (pDegree zCount arc pToZ p)
def totalAOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 8 (aOut arc)
def totalPOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 5 (pOut arc)
def totalPToH (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 5 (pHOut arc)
def totalHToP (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 7 (hPOut arc)
def totalHToQ (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 7 fun h => count 2 (aToQ arc (1 + h))
def totalPToZ (zCount : Nat) (pToZ : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 5 (pZOut zCount pToZ)
def totalPToQ (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 5 (pQOut arc)
def totalPToAux (zCount : Nat) (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  totalPToQ arc + totalPToZ zCount pToZ
def totalHOut (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 7 fun h => aOut arc (1 + h) + hPOut arc h + count 2 (aToQ arc (1 + h))

def aMissing (arc : Nat → Nat → Bool) : BitVec 8 := 28 - totalAOut arc
def internalMissing (arc : Nat → Nat → Bool) : BitVec 8 := 10 - totalPOut arc
def qMissing (arc : Nat → Nat → Bool) : BitVec 8 := 10 - totalPToQ arc
def externalMissing (zCount : Nat) (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  15 - totalPToAux zCount arc pToZ
def alpha (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (12 + 3 * y) - aMissing arc - totalPToH arc
def etaH (arc : Nat → Nat → Bool) : BitVec 8 := totalHOut arc - 56
def hQDefect (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (8 + 3 * y) - totalHToQ arc
def crossMissing (arc : Nat → Nat → Bool) : BitVec 8 :=
  35 - totalPToH arc - totalHToP arc

def qAnonymousLower (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  if y == 2 then
    let d := hQDefect 2 arc + qMissing arc
    if d == 0 then 5 else if d.ule 2 then 4 else if d.ule 4 then 3
    else if d.ule 6 then 2 else if d.ule 8 then 1 else 0
  else 0
def reachesBothQFromA (arc : Nat → Nat → Bool) (a : Nat) : Bool :=
  aToQ arc a 0 && aToQ arc a 1
def reachesBothQFromP (arc : Nat → Nat → Bool) (p : Nat) : Bool :=
  pToQ arc p 0 && pToQ arc p 1
def aNonSeymour (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 8 fun a =>
    (projectedSecondCount zCount arc pToZ a +
      (if reachesBothQFromA arc a then qAnonymousLower y arc else 0)).ult
        (aDegree arc a)
def pNonSeymour (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 5 fun p =>
    (projectedSecondCount zCount arc pToZ (8 + p) +
      (if reachesBothQFromP arc p then qAnonymousLower y arc else 0)).ult
        (pDegree zCount arc pToZ p)

def degreeAndDualConditions (y : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (BitVec.ofNat 8 (23 - 3 * y) + aMissing arc + hQDefect y arc).ule
      (totalHToP arc) &&
    alpha y arc + aMissing arc ==
      etaH arc + aMissing arc + hQDefect y arc + crossMissing arc

def effectiveAtRowSize (s v1 v2 v3 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2 else v3
def individualEffectiveTable (m s : BitVec 8) : BitVec 8 :=
  if m == 0 then effectiveAtRowSize s 10 8 7
  else if m == 1 then effectiveAtRowSize s 9 8 7
  else if m == 2 then effectiveAtRowSize s 8 7 7
  else if m == 3 then effectiveAtRowSize s 7 7 6
  else 0
def individualEffectiveLower (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  individualEffectiveTable (externalMissing zCount arc pToZ) (pAuxOut zCount arc pToZ p)
def pEffectiveCondition (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : Bool :=
  (pSecondPCount arc p + individualEffectiveLower zCount arc pToZ p + 1).ule
    (pOut arc p + 2 * pHOut arc p + pAuxOut zCount arc pToZ p)

def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 4 else if beta.ule 2 then 3 else if beta.ule 5 then 2
  else if beta.ule 9 then 1 else 0
def sharpKing (arc : Nat → Nat → Bool) : Bool :=
  any 5 fun p => (sharpKingLower (internalMissing arc)).ule
    (pOut arc p + pSecondPCount arc p)

/-! The degree-seven hypothesis applied to four small induced subgraphs.  The
predicate computes each induced second neighborhood exactly, strengthening
the permissive local second-neighbor indicators while retaining a direct graph
interpretation. -/

def contiguousInducedSeymour (arc : Nat → Nat → Bool)
    (start size source : Nat) : Bool :=
  (count size fun target => arc (start + source) (start + target)).ule
    (count size fun target => strictSecondLocal arc (start + source) (start + target))
def hasContiguousInducedSeymour (arc : Nat → Nat → Bool)
    (start size : Nat) : Bool := any size (contiguousInducedSeymour arc start size)

def aOnePIndex (i : Nat) : Nat := if i < 3 then 1 + i else 8 + (i - 3)
def aOnePSeymour (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  (count 8 fun target => arc (aOnePIndex source) (aOnePIndex target)).ule
    (count 8 fun target =>
      strictSecondLocal arc (aOnePIndex source) (aOnePIndex target))
def hasAOnePInducedSeymour (arc : Nat → Nat → Bool) : Bool :=
  any 8 (aOnePSeymour arc)

/-! Since `a₁` has exact outdegree eight and exactly seven second
neighbors in these tight rows, deleting any one of its eight outarcs cannot
decrease its strict second neighborhood.  A target private to the deleted
middle must therefore be replaced by the deleted middle itself. -/

def aOneSecondTargetIndex (t : Nat) : Nat :=
  if t < 4 then 4 + t else if t < 6 then 13 + (t - 4) else 15 + (t - 6)
def aOnePrivateTarget (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (deleted target : Nat) : Bool :=
  coreArc zCount arc pToZ (aOnePIndex deleted) (aOneSecondTargetIndex target) &&
    all 8 fun other => decide (other = deleted) ||
      !coreArc zCount arc pToZ (aOnePIndex other) (aOneSecondTargetIndex target)
def aOneDeletedReached (arc : Nat → Nat → Bool) (deleted : Nat) : Bool :=
  any 8 fun other => decide (other ≠ deleted) &&
    arc (aOnePIndex other) (aOnePIndex deleted)
def aOneDeletionCondition (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (deleted : Nat) : Bool :=
  (count (6 + zCount) fun target =>
    aOnePrivateTarget zCount arc pToZ deleted target).ule
      (bitCount (aOneDeletedReached arc deleted))
def aOneDeletionConditions (zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 8 (aOneDeletionCondition zCount arc pToZ)

def pRowKey (zCount : Nat) (arc pToZ : Nat → Nat → Bool)
    (p : Nat) : BitVec 32 :=
  (pDegree zCount arc pToZ p).zeroExtend 32 * 65536 +
    (pZOut zCount pToZ p).zeroExtend 32 * 4096 +
    (pQOut arc p).zeroExtend 32 * 512 +
    (count 3 fun a => pToA arc p (1 + a)).zeroExtend 32 * 64 +
    (count 4 fun x => pToA arc p (4 + x)).zeroExtend 32 * 8 +
    (pOut arc p).zeroExtend 32
def orderedP (zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 4 fun p => (pRowKey zCount arc pToZ (p + 1)).ule (pRowKey zCount arc pToZ p)
def orderedAClasses (arc : Nat → Nat → Bool) : Bool :=
  all 2 (fun a => (aBOut arc (2 + a)).ule (aBOut arc (1 + a))) &&
    all 3 (fun x => (aBOut arc (5 + x)).ule (aBOut arc (4 + x)))
def qIn (arc : Nat → Nat → Bool) (q : Nat) : BitVec 8 :=
  count 8 (fun a => aToQ arc a q) + count 5 (fun p => pToQ arc p q)
def orderedQ (arc : Nat → Nat → Bool) : Bool := (qIn arc 1).ule (qIn arc 0)
def zIn (pToZ : Nat → Nat → Bool) (z : Nat) : BitVec 8 := count 5 fun p => pToZ p z
def orderedZ (zCount : Nat) (pToZ : Nat → Nat → Bool) : Bool :=
  all (zCount - 1) fun z => (zIn pToZ (z + 1)).ule (zIn pToZ z)

def commonCore (y zCount : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && fixedAOne arc &&
    noPToAOne arc && qInB arc && qReachStatus y arc &&
    everyXReached arc && everyZReached zCount pToZ && inactiveZZero zCount pToZ &&
    aConditions arc && pConditions zCount arc pToZ &&
    aNonSeymour y zCount arc pToZ && pNonSeymour y zCount arc pToZ &&
    degreeThreeClassification arc && threeInnerWitnesses arc &&
    degreeAndDualConditions y arc &&
    (externalMissing zCount arc pToZ).ule 3 &&
    all 5 (pEffectiveCondition zCount arc pToZ) && sharpKing arc &&
    hasContiguousInducedSeymour arc 8 5 && hasAOnePInducedSeymour arc &&
    hasContiguousInducedSeymour arc 1 12 &&
    hasContiguousInducedSeymour arc 0 13 &&
    aOneDeletionConditions zCount arc pToZ &&
    orderedP zCount arc pToZ && orderedAClasses arc && orderedQ arc && orderedZ zCount pToZ

def residualLeaf (m q hq delta : Nat) (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 2 1 arc pToZ &&
    externalMissing 1 arc pToZ == BitVec.ofNat 8 m &&
    qMissing arc == BitVec.ofNat 8 q && hQDefect 2 arc == BitVec.ofNat 8 hq &&
    aMissing arc == BitVec.ofNat 8 delta

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
