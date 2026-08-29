import SeymourEight.Certificates.BSevenKTwo.RSeven.XThree.CoreDefs

/-!
# Finite core for the `r = 6`, `x = 3`, `y = 1` rows

The seven-`P` encoding has one unused row in this case.  Its five `P -> H`
bits and two external bits encode the seven non-pivot `A -> q` incidences, so
the whole row fits in the 225-bit layout.
-/

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.Encoding

def aArc := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.aArc
def pArc := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pArc
def pToH := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToH
def hToP := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.hToP
def pToE := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToZ
def rToP := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.rToP

/-- Incidence from a non-pivot `A` vertex to the unique reached `Q` vertex. -/
def aToQ (bits : Encoding) (a : Nat) : Bool :=
  if a = 0 then false
  else if a < 6 then pToH bits 6 (a - 1)
  else pToE bits 6 (a - 6)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true
  else if a < 6 then hToP bits (a - 1) p
  else rToP bits (a - 6) p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if 0 < a && a < 6 then pToH bits p (a - 1) else false

/-- Local indices are `A[8]`, `P[6]`, and `E[4]`, with `E[0]=q`. -/
def coreArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 14 then aToP bits u (v - 8)
    else if v = 14 then aToQ bits u
    else false
  else if u < 14 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 14 then pArc bits (u - 8) (v - 8)
    else if v < 18 then pToE bits (u - 8) (v - 14)
    else false
  else false

def directCount (bits : Encoding) (u : Nat) : BitVec 8 :=
  count 18 (coreArc bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 := count 8 (aArc bits a)
def aPOut (bits : Encoding) (a : Nat) : BitVec 8 := count 6 (aToP bits a)
def aBOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  aPOut bits a + bitCount (aToQ bits a)
def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 5 (pToH bits p)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 6 (hToP bits h)
def pEOut (bits : Encoding) (p : Nat) : BitVec 8 := count 4 (pToE bits p)

def reachesLocal (bits : Encoding) (source target : Nat) : Bool :=
  any 14 fun middle => decide (middle != source) && decide (middle != target) &&
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

def orientedA := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.orientedA

def orientedP (bits : Encoding) : Bool :=
  all 6 fun i => all 6 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)

def orientedPH (bits : Encoding) : Bool :=
  all 6 fun p => all 5 fun h => !(pToH bits p h && hToP bits h p)

def fixedA := SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.fixedA

def everyXReached (bits : Encoding) : Bool :=
  all 3 fun x => any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
    any 6 (fun p => pToH bits p (2 + x))

def qReached (bits : Encoding) : Bool :=
  any 2 (fun a => aToQ bits (1 + a)) || any 6 (fun p => pToE bits p 0)

def allZReached (bits : Encoding) : Bool :=
  all 3 fun z => any 6 fun p => pToE bits p (1 + z)

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a => (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (6 : BitVec 8).ule (aBOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aBOut bits a)

def pMinimumDegree (bits : Encoding) : Bool :=
  all 6 fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut bits p)

def uVertex (u : Nat) : Nat := if u < 2 then 1 + u else 6 + u
def secondTarget (t : Nat) : Nat := if t < 3 then 3 + t else 11 + t

def privateTarget (bits : Encoding) (deleted target : Nat) : Bool :=
  coreArc bits (uVertex deleted) (secondTarget target) &&
    all 8 fun other => decide (other = deleted) ||
      !coreArc bits (uVertex other) (secondTarget target)

def deletedReached (bits : Encoding) (deleted : Nat) : Bool :=
  any 8 fun other => decide (other != deleted) &&
    coreArc bits (uVertex other) (uVertex deleted)

/-- The one-arc deletion consequence for the pivot's exact eight-neighborhood. -/
def tightPrivate (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (count 7 (privateTarget bits deleted)).ule (bitCount (deletedReached bits deleted))

def totalPToE (bits : Encoding) : BitVec 8 := sumCount 6 (pEOut bits)
def totalPToH (bits : Encoding) : BitVec 8 := sumCount 6 (pHOut bits)
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 5 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 6 (pOut bits)

def externalMissing (bits : Encoding) : BitVec 8 := 24 - totalPToE bits
def internalMissing (bits : Encoding) : BitVec 8 := 15 - totalPOut bits
def crossMissing (bits : Encoding) : BitVec 8 :=
  30 - totalPToH bits - totalHToP bits
def aOneToQ (bits : Encoding) : BitVec 8 := count 2 fun a => aToQ bits (1 + a)

def effectiveAtRowSize (s v1 v2 v3 v4 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else v4

def individualEffectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing bits
  let s := pEOut bits p
  if m == 0 then effectiveAtRowSize s 11 9 8 7
  else if m == 1 then effectiveAtRowSize s 10 8 7 7
  else if m == 2 then effectiveAtRowSize s 9 8 7 6
  else if m == 3 then effectiveAtRowSize s 8 7 7 6
  else if m == 4 then effectiveAtRowSize s 7 7 6 6
  else effectiveAtRowSize s 6 6 6 6

def pSecondPCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 fun q => strictSecondLocal bits (8 + p) (8 + q)

def pEffectiveCondition (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + individualEffectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut bits p)

def reachesPH (bits : Encoding) (p q : Nat) : Bool :=
  decide (p != q) && (pArc bits p q ||
    any 11 fun middle =>
      let w := if middle < 6 then 8 + middle else 1 + (middle - 6)
      decide (w != 8 + p) && decide (w != 8 + q) &&
        coreArc bits (8 + p) w && coreArc bits w (8 + q))

def reachCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 (reachesPH bits p)

def defectLoss (d : BitVec 8) : BitVec 8 :=
  if d == 0 then 0 else if d.ule 2 then 1 else if d.ule 5 then 2
  else if d.ule 9 then 3 else if d.ule 14 then 4 else 5

def sharpKing (bits : Encoding) : Bool :=
  any 6 fun p => all 6 (fun q => (pOut bits q).ule (pOut bits p)) &&
    (5 - defectLoss (internalMissing bits)).ule (reachCount bits p)

def score (bits : Encoding) (p : Nat) : BitVec 8 := pOut bits p + pHOut bits p

def scoreKing (bits : Encoding) : Bool :=
  all 6 fun p => !(all 6 fun q => (score bits q).ule (score bits p)) ||
    (5 - defectLoss (internalMissing bits + crossMissing bits)).ule
      (reachCount bits p)

def equalScoreClass (bits : Encoding) : Bool :=
  all 6 fun p =>
    let classSize := count 6 fun q => score bits q == score bits p
    let reached := count 6 fun q => score bits q == score bits p && reachesPH bits p q
    classSize.ule (reached + defectLoss (internalMissing bits + crossMissing bits) + 1)

def isExact (bits : Encoding) (p : Nat) : Bool := directCount bits (8 + p) == 8
def exactCount (bits : Encoding) : BitVec 8 := count 6 (isExact bits)
def exactInternal (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 fun q => isExact bits q && pArc bits p q
def exactOutside (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 fun q => !isExact bits q && pArc bits p q
def exactMissing (bits : Encoding) : BitVec 8 :=
  count 36 fun k =>
    let i := k / 6
    let j := k % 6
    decide (i < j) && isExact bits i && isExact bits j &&
      !pArc bits i j && !pArc bits j i

def exactClassKing (bits : Encoding) : Bool :=
  any 6 fun p => isExact bits p &&
    all 6 (fun q => !isExact bits q || (exactInternal bits q).ule (exactInternal bits p)) &&
    (pEOut bits p + individualEffectiveLower bits p + exactOutside bits p +
      exactCount bits).ule (16 + defectLoss (exactMissing bits))

def orderedP (bits : Encoding) : Bool :=
  all 5 fun p => (directCount bits (9 + p)).ule (directCount bits (8 + p))

def orderedStructuralClasses (bits : Encoding) : Bool :=
  (aBOut bits 2).ule (aBOut bits 1) &&
    all 2 (fun x => (aBOut bits (4 + x)).ule (aBOut bits (3 + x))) &&
    (aBOut bits 7).ule (aBOut bits 6)

def commonCore (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits && fixedA bits &&
  everyXReached bits && qReached bits && allZReached bits &&
  (3 : BitVec 8).ule (count 6 fun k =>
    let a := k / 3
    let x := k % 3
    aArc bits (1 + a) (3 + x)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour bits) &&
  pMinimumDegree bits && all 6 (pNonSeymour bits) && tightPrivate bits &&
  orderedP bits && orderedStructuralClasses bits

def core (bits : Encoding) : Bool :=
  commonCore bits && all 6 (pEffectiveCondition bits) &&
  sharpKing bits && exactClassKing bits &&
  (18 - aOneToQ bits).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing bits).ule 21

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core
