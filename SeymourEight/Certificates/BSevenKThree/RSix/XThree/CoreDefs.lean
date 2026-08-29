import SeymourEight.Shared.FiniteCore

/-!
# Compact cores for the `r = 6`, `x = 3` families

The local indices are `A = 0..7`, `P = 8..13`, the unique reached `Q`
vertex at `14`, and up to four `Z` columns from `15` onward.  Auxiliary
vertices have no represented outgoing row: omitting paths through them only
weakens the second-neighborhood lower bounds used below.
-/

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

open Shared.FiniteCore

def aOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 := count 8 (arc a)
def aPOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  count 6 fun p => arc a (8 + p)
def aBOut (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  aPOut arc a + bitCount (arc a 14)
def pOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 6 fun q => arc (8 + p) (8 + q)
def pHOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 6 fun h => arc (8 + p) (1 + h)
def hPOut (arc : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 6 fun p => arc (1 + h) (8 + p)
def pAuxOut (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count (1 + zCount) fun e => arc (8 + p) (14 + e)
def pZOut (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count zCount fun z => arc (8 + p) (15 + z)
def pDegree (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  pOut arc p + pHOut arc p + pAuxOut zCount arc p

def reaches (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 14 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    arc source middle && arc middle target
def strictSecond (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target && reaches arc source target
def secondCount (zCount : Nat) (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count (15 + zCount) (strictSecond arc source)
def pSecondP (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 6 fun q => strictSecond arc (8 + p) (8 + q)

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
  any 6 fun p => arc source (8 + p) && arc (8 + p) (14 + e)
def hallCount (zCount : Nat) (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count (1 + zCount) (hallReached zCount arc source)
def hallCondition (zCount : Nat) (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  !innerSeymour arc source || arc source 14 ||
    ((1 : BitVec 8).ule (aPOut arc source) &&
      (hallCount zCount arc source).ult (aPOut arc source))

def orientedA (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun i => !arc i i && all 8 fun j =>
    decide (i = j) || !(arc i j && arc j i)
def orientedP (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun i => all 6 fun j =>
    decide (i = j) || !(arc (8 + i) (8 + j) && arc (8 + j) (8 + i))
def orientedAPQ (arc : Nat → Nat → Bool) : Bool :=
  (all 8 fun a => all 6 fun p => !(arc a (8 + p) && arc (8 + p) a)) &&
  (all 8 fun a => !(arc a 14 && arc 14 a)) &&
  (all 6 fun p => !(arc (8 + p) 14 && arc 14 (8 + p)))

def fixedPivot (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun v => arc 0 v == decide (1 ≤ v && v ≤ 3 || 8 ≤ v && v < 14)
def everyXReached (arc : Nat → Nat → Bool) : Bool :=
  all 3 fun x => any 3 (fun a => arc (1 + a) (4 + x)) ||
    any 6 (fun p => arc (8 + p) (4 + x))
def rUnreached (arc : Nat → Nat → Bool) : Bool :=
  all 3 (fun a => !arc (1 + a) 7) && all 6 (fun p => !arc (8 + p) 7)
def qReached (arc : Nat → Nat → Bool) : Bool :=
  any 3 (fun a => arc (1 + a) 14) || any 6 (fun p => arc (8 + p) 14)
def allZReached (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all zCount fun z => any 6 fun p => arc (8 + p) (15 + z)

def aMinimumAndPivot (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun a => (3 : BitVec 8).ule (aOut arc a) &&
    (!(aOut arc a == 3) || (6 : BitVec 8).ule (aBOut arc a)) &&
    (8 : BitVec 8).ule (aOut arc a + aBOut arc a)
def aNonSeymour (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun a => (secondCount zCount arc a).ult (aOut arc a + aBOut arc a)
def pMinimum (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun p => (8 : BitVec 8).ule (pDegree zCount arc p)

def degreeThreeClassification (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun source => all 8 fun target => decide (source = target) ||
    !degreeThree arc source || degreeThreeInner arc source ||
    !arc source target || degreeThreeInner arc target
def threeInnerWitnesses (arc : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (count 8 (degreeThreeInner arc))

def inducedWitness (arc : Nat → Nat → Bool) (member : Nat → Bool) : Bool :=
  any 14 fun source => member source &&
    (count 14 fun target => member target && strictSecond arc source target).ule
      (count 14 fun target => member target && arc source target)
def inducedConditions (arc : Nat → Nat → Bool) : Bool :=
  inducedWitness arc (fun v => decide (8 ≤ v)) &&
  inducedWitness arc (fun v => decide (1 ≤ v && v ≤ 3 || 8 ≤ v)) &&
  inducedWitness arc (fun v => decide (1 ≤ v && v ≤ 6 || 8 ≤ v)) &&
  inducedWitness arc (fun _ => true)

def totalAOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 8 (aOut arc)
def totalHToP (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (hPOut arc)
def totalPToH (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (pHOut arc)
def totalPOut (arc : Nat → Nat → Bool) : BitVec 8 := sumCount 6 (pOut arc)
def totalHOut (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 6 fun h => aOut arc (1 + h) + hPOut arc h + bitCount (arc (1 + h) 14)
def totalPAux (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 6 (pAuxOut zCount arc)
def aMissing (arc : Nat → Nat → Bool) : BitVec 8 := 28 - totalAOut arc
def degreeGain (arc : Nat → Nat → Bool) : BitVec 8 :=
  let d := aMissing arc
  if d.ule 1 then 3 else if d == 2 then 5 else if d == 3 then 7 else 9
def qDefect (arc : Nat → Nat → Bool) : BitVec 8 :=
  6 - count 6 fun h => arc (1 + h) 14
def alpha (arc : Nat → Nat → Bool) : BitVec 8 :=
  15 - degreeGain arc - totalPToH arc
def beta (arc : Nat → Nat → Bool) : BitVec 8 := 15 - totalPOut arc
def tau (arc : Nat → Nat → Bool) : BitVec 8 := aOut arc 7 + aMissing arc - 4
def etaH (arc : Nat → Nat → Bool) : BitVec 8 := totalHOut arc - 48
def crossMissing (arc : Nat → Nat → Bool) : BitVec 8 :=
  36 - totalHToP arc - totalPToH arc
def externalMissing (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (6 * (1 + zCount)) - totalPAux zCount arc
def totalDefect (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  externalMissing zCount arc + alpha arc + beta arc

def effectiveAt (s v1 v2 v3 v4 v5 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else v5
def effectiveFour (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  let m := externalMissing 3 arc; let s := pAuxOut 3 arc p
  if m == 0 then effectiveAt s 11 9 8 8 8
  else if m == 1 then effectiveAt s 10 8 8 7 7
  else if m == 2 then effectiveAt s 9 8 7 6 6
  else if m == 3 then effectiveAt s 8 7 7 6 6
  else if m == 4 then effectiveAt s 7 7 6 6 6
  else if m == 5 then effectiveAt s 6 6 6 6 6
  else if m == 6 then effectiveAt s 5 6 6 5 5
  else if m == 7 then effectiveAt s 4 5 5 5 5
  else if m == 8 then effectiveAt s 3 5 5 5 5
  else effectiveAt s 2 4 5 5 5
def effectiveFive (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  let m := externalMissing 4 arc; let s := pAuxOut 4 arc p
  if m == 0 then effectiveAt s 12 9 8 7 7
  else if m == 1 then effectiveAt s 11 9 8 8 7
  else if m == 2 then effectiveAt s 10 8 8 7 6
  else if m == 3 then effectiveAt s 9 8 7 6 6
  else if m == 4 then effectiveAt s 8 7 7 6 6
  else if m == 5 then effectiveAt s 7 7 6 6 5
  else if m == 6 then effectiveAt s 6 6 6 6 5
  else if m == 7 then effectiveAt s 5 6 6 5 5
  else if m == 8 then effectiveAt s 4 5 5 5 5
  else effectiveAt s 0 4 5 5 5
def effective (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  if zCount = 3 then effectiveFour arc p else effectiveFive arc p
def pEffective (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun p => (pSecondP arc p + effective zCount arc p + 1).ule
    (pOut arc p + 2 * pHOut arc p + pAuxOut zCount arc p)

def sharpKingLower (b : BitVec 8) : BitVec 8 :=
  if b == 0 then 5 else if b.ule 2 then 4 else if b.ule 5 then 3
  else if b.ule 9 then 2 else if b.ule 14 then 1 else 0
def sharpKing (arc : Nat → Nat → Bool) : Bool :=
  any 6 fun p => (sharpKingLower (beta arc)).ule (pOut arc p + pSecondP arc p) &&
    all 6 fun q => (pOut arc q).ule (pOut arc p)

def pKey (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (pDegree zCount arc p).toNat * 65536 +
    BitVec.ofNat 32 (pZOut zCount arc p).toNat * 4096 +
    BitVec.ofNat 32 (bitCount (arc (8+p) 14)).toNat * 2048 +
    BitVec.ofNat 32 (count 3 fun a => arc (8+p) (1+a)).toNat * 256 +
    BitVec.ofNat 32 (count 3 fun x => arc (8+p) (4+x)).toNat * 16 +
    BitVec.ofNat 32 (pOut arc p).toNat
def ordered (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (all 5 fun p => (pKey zCount arc (p+1)).ule (pKey zCount arc p)) &&
  (all 2 fun a => (aBOut arc (a+2)).ule (aBOut arc (a+1))) &&
  (all 2 fun x => (aBOut arc (x+5)).ule (aBOut arc (x+4))) &&
  (all (zCount-1) fun z =>
    (count 6 fun p => arc (8+p) (16+z)).ule (count 6 fun p => arc (8+p) (15+z)))

def arithmetic (_zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (21 + degreeGain arc + qDefect arc).ule (totalHToP arc) &&
  (totalPToH arc + degreeGain arc).ule 15 &&
  (aMissing arc).ule (tau arc + 1) && (tau arc).ule 3 &&
  (3 + tau arc).ule (etaH arc) &&
  alpha arc + degreeGain arc == etaH arc + tau arc + qDefect arc + crossMissing arc

def commonCoreFn (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedAPQ arc && fixedPivot arc &&
  everyXReached arc && rUnreached arc && qReached arc && allZReached zCount arc &&
  aMinimumAndPivot arc && aNonSeymour zCount arc && pMinimum zCount arc &&
  all 8 (hallCondition zCount arc) && degreeThreeClassification arc &&
  threeInnerWitnesses arc && inducedConditions arc && arithmetic zCount arc &&
  pEffective zCount arc && sharpKing arc && ordered zCount arc

abbrev Encoding := BitVec 191

def directedIndex (n i j : Nat) : Nat :=
  (n - 1) * i + if j < i then j else j - 1

def encodedArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then
      if u = 0 then decide (1 ≤ v && v ≤ 3)
      else if v = 0 then
        if u ≤ 3 then false else bits.getLsbD (u - 4)
      else decide (u ≠ v) && bits.getLsbD (4 + directedIndex 7 (u - 1) (v - 1))
    else if v < 14 then
      if u = 0 then true else bits.getLsbD (76 + 6 * (u - 1) + (v - 8))
    else if v = 14 then
      if u = 0 then false else bits.getLsbD (154 + (u - 1))
    else false
  else if u < 14 then
    if v < 8 then
      if 1 ≤ v && v ≤ 6 then bits.getLsbD (118 + 6 * (u - 8) + (v - 1))
      else false
    else if v < 14 then
      decide (u ≠ v) && bits.getLsbD (46 + directedIndex 6 (u - 8) (v - 8))
    else if v < 20 then bits.getLsbD (161 + 5 * (u - 8) + (v - 14))
    else false
  else false

def commonCore (zCount : Nat) (bits : Encoding) : Bool :=
  commonCoreFn zCount (encodedArc bits)

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core
