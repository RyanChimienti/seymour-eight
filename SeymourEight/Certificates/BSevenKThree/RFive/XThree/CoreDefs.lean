import SeymourEight.Shared.FiniteCore

/-!
# Compact finite core for the `r = 5`, `x = 3` families

The retained vertices are `A = 0..7`, `P = 8..12`, the two vertices of
`Q = 13..14`, and up to three external targets from index `15`.  The lone
vertex of `R` is `7`; consequently `H = A₁ ∪ X = 1..6`.
-/

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core

open Shared.FiniteCore

def aOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 8 (arc a)
def aPOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  count 5 fun p => arc a (8 + p)
def aQOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  count 2 fun q => arc a (13 + q)
def aBOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  aPOut arc a + aQOut arc a
def pOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 5 fun q => arc (8 + p) (8 + q)
def pHOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 6 fun h => arc (8 + p) (1 + h)
def hPOut (arc : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 5 fun p => arc (1 + h) (8 + p)
def hQOut (arc : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 2 fun q => arc (1 + h) (13 + q)
def pAuxOut (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count (2 + zCount) fun e => arc (8 + p) (13 + e)
def pZOut (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count zCount fun z => arc (8 + p) (15 + z)
def pDegree (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  pOut arc p + pHOut arc p + pAuxOut zCount arc p

def reaches (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 13 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    arc source middle && arc middle target
def strictSecond (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target && reaches arc source target
def secondCount (zCount : Nat) (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count (15 + zCount) (strictSecond arc source)
def pSecondP (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 5 fun q => strictSecond arc (8 + p) (8 + q)

def innerReaches (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 8 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    arc source middle && arc middle target
def innerSecond (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target && innerReaches arc source target
def innerSecondCount (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count 8 (innerSecond arc source)
def innerSeymour (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  (aOut arc source).ule (innerSecondCount arc source)
def degreeThree (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  aOut arc source == 3
def degreeThreeInner (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  degreeThree arc source && innerSeymour arc source

def hallReached (_zCount : Nat) (arc : Nat → Nat → Bool)
    (source e : Nat) : Bool :=
  !arc source (13 + e) &&
    any 5 fun p => arc source (8 + p) && arc (8 + p) (13 + e)
def hallCount (zCount : Nat) (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count (2 + zCount) (hallReached zCount arc source)
def hallCondition (zCount : Nat) (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  !innerSeymour arc source || any 2 (fun q => arc source (13 + q)) ||
    ((1 : BitVec 8).ule (aPOut arc source) &&
      (hallCount zCount arc source).ult (aPOut arc source))

def orientedA (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun i => !arc i i && all 8 fun j =>
    decide (i = j) || !(arc i j && arc j i)
def orientedP (arc : Nat → Nat → Bool) : Bool :=
  all 5 fun i => all 5 fun j =>
    decide (i = j) || !(arc (8 + i) (8 + j) && arc (8 + j) (8 + i))
def orientedPH (arc : Nat → Nat → Bool) : Bool :=
  all 5 fun p => all 6 fun h =>
    !(arc (8 + p) (1 + h) && arc (1 + h) (8 + p))

def fixedPivot (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun v => arc 0 v == decide (1 ≤ v && v ≤ 3 || 8 ≤ v && v < 13)
def everyXReached (arc : Nat → Nat → Bool) : Bool :=
  all 3 fun x => any 3 (fun a => arc (1 + a) (4 + x)) ||
    any 5 (fun p => arc (8 + p) (4 + x))
def rUnreached (arc : Nat → Nat → Bool) : Bool :=
  all 3 (fun a => !arc (1 + a) 7) && all 5 (fun p => !arc (8 + p) 7)
def qInB (arc : Nat → Nat → Bool) : Bool :=
  all 2 fun q => any 8 fun a => arc a (13 + q)
def qReached (arc : Nat → Nat → Bool) (q : Nat) : Bool :=
  any 3 (fun a => arc (1 + a) (13 + q)) ||
    any 5 (fun p => arc (8 + p) (13 + q))
def qReachStatus (y : Nat) (arc : Nat → Nat → Bool) : Bool :=
  count 2 (qReached arc) == BitVec.ofNat 8 y
def allZReached (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all zCount fun z => any 5 fun p => arc (8 + p) (15 + z)
def inactiveZZero (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  if zCount = 1 then all 5 fun p => !arc (8 + p) 16 && !arc (8 + p) 17
  else if zCount = 2 then all 5 fun p => !arc (8 + p) 17
  else true

def aMinimumAndPivot (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun a => (3 : BitVec 8).ule (aOut arc a) &&
    (!(aOut arc a == 3) || (5 : BitVec 8).ule (aBOut arc a)) &&
    (8 : BitVec 8).ule (aOut arc a + aBOut arc a)
def aNonSeymour (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun a => (secondCount zCount arc a).ult (aOut arc a + aBOut arc a)
def pMinimum (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 5 fun p => (8 : BitVec 8).ule (pDegree zCount arc p)

def degreeThreeClassification (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun source => all 8 fun target => decide (source = target) ||
    !degreeThree arc source || degreeThreeInner arc source ||
    !arc source target || degreeThreeInner arc target
def threeInnerWitnesses (arc : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (count 8 (degreeThreeInner arc))

def inducedWitness (n : Nat) (index : Nat → Nat)
    (arc : Nat → Nat → Bool) : Bool :=
  any n fun source =>
    (count n fun target => arc (index source) (index target)).ule
      (count n fun target => strictSecond arc (index source) (index target))
def aOnePIndex (i : Nat) : Nat := if i < 3 then 1 + i else 8 + (i - 3)
def hPIndex (i : Nat) : Nat := if i < 6 then 1 + i else 8 + (i - 6)
def inducedConditions (arc : Nat → Nat → Bool) : Bool :=
  inducedWitness 5 (fun i => 8 + i) arc &&
  inducedWitness 8 aOnePIndex arc &&
  inducedWitness 11 hPIndex arc &&
  inducedWitness 13 id arc

def aOneNeighborIndex (i : Nat) : Nat := if i < 3 then 1 + i else 8 + (i - 3)
def aOneSecondTargetIndex (t : Nat) : Nat :=
  if t < 3 then 4 + t else if t < 5 then 13 + (t - 3) else 15 + (t - 5)
def aOnePrivateTarget (_zCount : Nat) (arc : Nat → Nat → Bool)
    (deleted target : Nat) : Bool :=
  arc (aOneNeighborIndex deleted) (aOneSecondTargetIndex target) &&
    all 8 fun other => decide (other = deleted) ||
      !arc (aOneNeighborIndex other) (aOneSecondTargetIndex target)
def aOneDeletedReached (arc : Nat → Nat → Bool) (deleted : Nat) : Bool :=
  any 8 fun other => decide (other ≠ deleted) &&
    arc (aOneNeighborIndex other) (aOneNeighborIndex deleted)
def aOneDeletionCondition (zCount : Nat) (arc : Nat → Nat → Bool)
    (deleted : Nat) : Bool :=
  (count (5 + zCount) fun target =>
    aOnePrivateTarget zCount arc deleted target).ule
      (bitCount (aOneDeletedReached arc deleted))
def aOneDeletionConditions (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 8 (aOneDeletionCondition zCount arc)

def totalAOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 8 (aOut arc)
def totalHToP (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (hPOut arc)
def totalPToH (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 5 (pHOut arc)
def totalPOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 5 (pOut arc)
def totalHToQ (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (hQOut arc)
def totalHOut (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 6 fun h => aOut arc (1 + h) + hPOut arc h + hQOut arc h
def totalPAux (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 5 (pAuxOut zCount arc)
def totalPToQ (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 5 fun p => count 2 fun q => arc (8 + p) (13 + q)
def totalPDegree (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 5 (pDegree zCount arc)

def aMissing (arc : Nat → Nat → Bool) : BitVec 8 := 28 - totalAOut arc
def alpha (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (9 + 3 * y) - totalPToH arc
def beta (arc : Nat → Nat → Bool) : BitVec 8 := 10 - totalPOut arc
def tau (arc : Nat → Nat → Bool) : BitVec 8 := aOut arc 7 + aMissing arc - 4
def etaH (arc : Nat → Nat → Bool) : BitVec 8 := totalHOut arc - 48
def qDefect (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (6 + 3 * y) - totalHToQ arc
def qMissing (y : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (5 * y) - totalPToQ arc
def crossMissing (arc : Nat → Nat → Bool) : BitVec 8 :=
  30 - totalHToP arc - totalPToH arc
def externalMissing (y zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (5 * (y + zCount)) - totalPAux zCount arc
def capacity (y zCount : Nat) : Nat := 8 * y + 5 * zCount - 21
def totalDefect (y zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  externalMissing y zCount arc + alpha y arc + beta arc

def qAnonymousLower (y zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  if y = 2 && zCount = 1 then
    let d := qDefect y arc + qMissing y arc
    if d == 0 then 5 else if d.ule 2 then 4 else if d.ule 4 then 3
    else if d.ule 6 then 2 else if d.ule 8 then 1 else 0
  else if y = 2 && zCount = 2 then
    let d := qDefect y arc + qMissing y arc
    if d == 0 then 4 else if d.ule 2 then 3 else if d.ule 4 then 2
    else if d.ule 6 then 1 else 0
  else 0
def reachesBothQ (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  arc source 13 && arc source 14
def augmentedNonSeymour (y zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (all 8 fun a =>
    (secondCount zCount arc a +
      (if reachesBothQ arc a then qAnonymousLower y zCount arc else 0)).ult
        (aOut arc a + aBOut arc a)) &&
  (all 5 fun p =>
    (secondCount zCount arc (8 + p) +
      (if reachesBothQ arc (8 + p) then qAnonymousLower y zCount arc else 0)).ult
        (pDegree zCount arc p))

def effectiveAt (s v1 v2 v3 v4 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else v4
def effectiveFour (y zCount : Nat) (arc : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  let m := externalMissing y zCount arc
  let s := pAuxOut zCount arc p
  if m == 0 then effectiveAt s 11 9 8 7
  else if m == 1 then effectiveAt s 10 8 7 7
  else if m == 2 then effectiveAt s 9 8 7 6
  else if m == 3 then effectiveAt s 8 7 7 6
  else if m == 4 then effectiveAt s 7 7 6 6
  else effectiveAt s 6 6 6 6
def effectiveThree (y zCount : Nat) (arc : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  let m := externalMissing y zCount arc
  let s := pAuxOut zCount arc p
  if m == 0 then effectiveAt s 10 8 7 7
  else if m == 1 then effectiveAt s 9 8 7 7
  else if m == 2 then effectiveAt s 8 7 7 7
  else if m == 3 then effectiveAt s 7 7 6 6
  else effectiveAt s 6 6 6 6
def effective (y zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  if y + zCount = 4 then effectiveFour y zCount arc p
  else effectiveThree y zCount arc p
def pEffective (y zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 5 fun p => (pSecondP arc p + effective y zCount arc p + 1).ule
    (pOut arc p + 2 * pHOut arc p + pAuxOut zCount arc p)

def sharpKingLower (b : BitVec 8) : BitVec 8 :=
  if b == 0 then 4 else if b.ule 2 then 3 else if b.ule 5 then 2
  else if b.ule 9 then 1 else 0
def sharpKing (arc : Nat → Nat → Bool) : Bool :=
  any 5 fun p => (sharpKingLower (beta arc)).ule (pOut arc p + pSecondP arc p) &&
    all 5 fun q => (pOut arc q).ule (pOut arc p)

def pKey (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 32 :=
  (pDegree zCount arc p).zeroExtend 32 * 65536 +
    (pZOut zCount arc p).zeroExtend 32 * 4096 +
    (count 2 fun q => arc (8+p) (13+q)).zeroExtend 32 * 512 +
    (count 3 fun a => arc (8+p) (1+a)).zeroExtend 32 * 64 +
    (count 3 fun x => arc (8+p) (4+x)).zeroExtend 32 * 8 +
    (pOut arc p).zeroExtend 32
def qIn (arc : Nat → Nat → Bool) (q : Nat) : BitVec 8 :=
  count 8 (fun a => arc a (13 + q)) + count 5 (fun p => arc (8 + p) (13 + q))
def orderedZ (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  if zCount = 1 then true
  else if zCount = 2 then
    (count 5 fun p => arc (8+p) 16).ule (count 5 fun p => arc (8+p) 15)
  else
    (count 5 fun p => arc (8+p) 16).ule (count 5 fun p => arc (8+p) 15) &&
    (count 5 fun p => arc (8+p) 17).ule (count 5 fun p => arc (8+p) 16)
def ordered (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (all 4 fun p => (pKey zCount arc (p+1)).ule (pKey zCount arc p)) &&
  (all 2 fun a => (aBOut arc (a+2)).ule (aBOut arc (a+1))) &&
  (all 2 fun x => (aBOut arc (x+5)).ule (aBOut arc (x+4))) &&
  (qIn arc 1).ule (qIn arc 0) &&
  orderedZ zCount arc

def arithmetic (y zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (BitVec.ofNat 8 (21 - 3 * y) + qDefect y arc).ule (totalHToP arc) &&
  (totalPToH arc).ule (BitVec.ofNat 8 (9 + 3 * y)) &&
  (aMissing arc).ule (tau arc + 1) && (tau arc).ule 3 &&
  alpha y arc == etaH arc + tau arc + qDefect y arc + crossMissing arc &&
  totalPDegree zCount arc ==
    BitVec.ofNat 8 (40 + capacity y zCount) - externalMissing y zCount arc -
      alpha y arc - beta arc &&
  (externalMissing y zCount arc).ule (BitVec.ofNat 8 (capacity y zCount))

def coreFn (y zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && fixedPivot arc &&
    everyXReached arc && rUnreached arc && qInB arc && qReachStatus y arc &&
    allZReached zCount arc && inactiveZZero zCount arc &&
    aMinimumAndPivot arc && aNonSeymour zCount arc && pMinimum zCount arc &&
    augmentedNonSeymour y zCount arc &&
    all 8 (hallCondition zCount arc) && degreeThreeClassification arc &&
    threeInnerWitnesses arc && inducedConditions arc && arithmetic y zCount arc &&
    pEffective y zCount arc && sharpKing arc &&
    ordered zCount arc

abbrev Encoding := BitVec 170

def directedIndex (n i j : Nat) : Nat :=
  (n - 1) * i + if j < i then j else j - 1

def encodedArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then
      if u = 0 then decide (1 ≤ v && v ≤ 3)
      else if v = 0 then
        if u ≤ 3 then false else bits.getLsbD (u - 4)
      else decide (u ≠ v) && bits.getLsbD (4 + directedIndex 7 (u - 1) (v - 1))
    else if v < 13 then
      if u = 0 then true else bits.getLsbD (66 + 5 * (u - 1) + (v - 8))
    else if v < 15 then
      if u = 0 then false else bits.getLsbD (131 + 2 * (u - 1) + (v - 13))
    else false
  else if u < 13 then
    if v < 8 then
      if 1 ≤ v && v ≤ 6 then bits.getLsbD (101 + 6 * (u - 8) + (v - 1))
      else false
    else if v < 13 then
      decide (u ≠ v) && bits.getLsbD (46 + directedIndex 5 (u - 8) (v - 8))
    else if v < 18 then bits.getLsbD (145 + 5 * (u - 8) + (v - 13))
    else false
  else false

def core (y zCount : Nat) (bits : Encoding) : Bool :=
  coreFn y zCount (encodedArc bits)

def defectCore (y zCount defect : Nat) (bits : Encoding) : Bool :=
  core y zCount bits &&
    totalDefect y zCount (encodedArc bits) == BitVec.ofNat 8 defect

def leafCore (y zCount m defect : Nat) (bits : Encoding) : Bool :=
  defectCore y zCount defect bits &&
    externalMissing y zCount (encodedArc bits) == BitVec.ofNat 8 m

def exactLeafCore (y zCount m a b : Nat) (bits : Encoding) : Bool :=
  core y zCount bits &&
    externalMissing y zCount (encodedArc bits) == BitVec.ofNat 8 m &&
    alpha y (encodedArc bits) == BitVec.ofNat 8 a &&
    beta (encodedArc bits) == BitVec.ofNat 8 b

def qLeafCore (y zCount m c a b : Nat) (bits : Encoding) : Bool :=
  exactLeafCore y zCount m a b bits &&
    qDefect y (encodedArc bits) == BitVec.ofNat 8 c

def dualLeafCore (y zCount m c a b eta t gamma : Nat)
    (bits : Encoding) : Bool :=
  qLeafCore y zCount m c a b bits &&
    etaH (encodedArc bits) == BitVec.ofNat 8 eta &&
    tau (encodedArc bits) == BitVec.ofNat 8 t &&
    crossMissing (encodedArc bits) == BitVec.ofNat 8 gamma

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core
