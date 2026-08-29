import SeymourEight.Shared.FiniteCore

/-!
# Finite core for the `r = 6`, `x = 2` families

The layout retains `A[8]`, `P[6]`, `H[4]`, five auxiliary columns, the
three `R -> P` rows, and the seven non-pivot `A -> q` incidences.  In a
reached row the first auxiliary column is `q`; in the unreached row all five
columns are `Z` and `q` is one additional semantic target.
-/

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := BitVec 197

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (8 * i + j)

def directedIndex (i j : Nat) : Nat :=
  5 * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i != j) && bits.getLsbD (64 + directedIndex i j)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (94 + 4 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  bits.getLsbD (118 + 6 * h + p)

def pToE (bits : Encoding) (p e : Nat) : Bool :=
  bits.getLsbD (142 + 5 * p + e)

def rToP (bits : Encoding) (r p : Nat) : Bool :=
  bits.getLsbD (172 + 6 * r + p)

/-- Incidence from a non-pivot `A` vertex to the unique vertex of `Q`. -/
def aToQ (bits : Encoding) (a : Nat) : Bool :=
  if a = 0 then false else bits.getLsbD (190 + a - 1)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true
  else if a < 5 then hToP bits (a - 1) p
  else rToP bits (a - 5) p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if 0 < a && a < 5 then pToH bits p (a - 1) else false

/-- In reached mode, `E[0]=q`; otherwise `E=Z` and `q` has index `14+e`. -/
def coreArc (eCount : Nat) (reached : Bool) (bits : Encoding)
    (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 14 then aToP bits u (v - 8)
    else if reached && v = 14 then aToQ bits u
    else if !reached && v = 14 + eCount then aToQ bits u
    else false
  else if u < 14 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 14 then pArc bits (u - 8) (v - 8)
    else if v < 14 + eCount then pToE bits (u - 8) (v - 14)
    else false
  else false

def vertexCount (eCount : Nat) (reached : Bool) : Nat :=
  14 + eCount + if reached then 0 else 1

def directCount (eCount : Nat) (reached : Bool) (bits : Encoding)
    (u : Nat) : BitVec 8 :=
  count (vertexCount eCount reached) (coreArc eCount reached bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 := count 8 (aArc bits a)
def aPOut (bits : Encoding) (a : Nat) : BitVec 8 := count 6 (aToP bits a)
def aBOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  aPOut bits a + bitCount (aToQ bits a)
def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 4 (pToH bits p)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 6 (hToP bits h)
def pEOut (eCount : Nat) (bits : Encoding) (p : Nat) : BitVec 8 :=
  count eCount (pToE bits p)

def reachesLocal (eCount : Nat) (reached : Bool) (bits : Encoding)
    (source target : Nat) : Bool :=
  any 14 fun middle => decide (middle != source) && decide (middle != target) &&
    coreArc eCount reached bits source middle &&
      coreArc eCount reached bits middle target

def strictSecondLocal (eCount : Nat) (reached : Bool) (bits : Encoding)
    (source target : Nat) : Bool :=
  decide (target != source) && !coreArc eCount reached bits source target &&
    reachesLocal eCount reached bits source target

def localSecondCount (eCount : Nat) (reached : Bool) (bits : Encoding)
    (source : Nat) : BitVec 8 :=
  count (vertexCount eCount reached)
    (strictSecondLocal eCount reached bits source)

def aNonSeymour (eCount : Nat) (reached : Bool) (bits : Encoding)
    (a : Nat) : Bool :=
  (localSecondCount eCount reached bits a).ult
    (directCount eCount reached bits a)

def pNonSeymour (eCount : Nat) (reached : Bool) (bits : Encoding)
    (p : Nat) : Bool :=
  (localSecondCount eCount reached bits (8 + p)).ult
    (directCount eCount reached bits (8 + p))

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)

def orientedP (bits : Encoding) : Bool :=
  all 6 fun i => all 6 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)

def orientedPH (bits : Encoding) : Bool :=
  all 6 fun p => all 4 fun h => !(pToH bits p h && hToP bits h p)

def completeP (bits : Encoding) : Bool :=
  all 6 fun p => all 6 fun q => decide (p = q) ||
    pArc bits p q || pArc bits q p

def completePH (bits : Encoding) : Bool :=
  all 6 fun p => all 4 fun h => pToH bits p h || hToP bits h p

def fixedA (bits : Encoding) : Bool :=
  aArc bits 0 1 && aArc bits 0 2 &&
  all 5 (fun i => !aArc bits 0 (3 + i)) &&
  all 6 fun k =>
    let a := k / 3
    let r := k % 3
    !aArc bits (1 + a) (5 + r)

def everyXReached (bits : Encoding) : Bool :=
  all 2 fun x => any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
    any 6 (fun p => pToH bits p (2 + x))

def qStructure (reached : Bool) (bits : Encoding) : Bool :=
  if reached then
    any 2 (fun a => aToQ bits (1 + a)) || any 6 (fun p => pToE bits p 0)
  else
    !aToQ bits 1 && !aToQ bits 2 && any 7 (fun a => aToQ bits (1 + a))

def allExternalReached (eCount : Nat) (reached : Bool)
    (bits : Encoding) : Bool :=
  if reached then
    all (eCount - 1) fun z => any 6 fun p => pToE bits p (1 + z)
  else all eCount fun z => any 6 fun p => pToE bits p z

def inactiveEZero (eCount : Nat) (bits : Encoding) : Bool :=
  if eCount = 5 then true
  else all 6 fun p => all (5 - eCount) fun j => !pToE bits p (eCount + j)

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a => (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (6 : BitVec 8).ule (aBOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aBOut bits a)

def pMinimumDegree (eCount : Nat) (_reached : Bool)
    (bits : Encoding) : Bool :=
  all 6 fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut eCount bits p)

def totalPToE (eCount : Nat) (bits : Encoding) : BitVec 8 :=
  sumCount 6 (pEOut eCount bits)
def totalPToH (bits : Encoding) : BitVec 8 := sumCount 6 (pHOut bits)
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 4 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 6 (pOut bits)

def externalMissing (eCount : Nat) (bits : Encoding) : BitVec 8 :=
  BitVec.ofNat 8 (6 * eCount) - totalPToE eCount bits
def internalMissing (bits : Encoding) : BitVec 8 := 15 - totalPOut bits
def crossMissing (bits : Encoding) : BitVec 8 :=
  24 - totalPToH bits - totalHToP bits
def aOneToQ (bits : Encoding) : BitVec 8 :=
  count 2 fun a => aToQ bits (1 + a)

def effectiveAtRowSize (s v1 v2 v3 v4 v5 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else v5

def individualEffectiveLowerFour (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing 4 bits
  let s := pEOut 4 bits p
  if m == 0 then effectiveAtRowSize s 11 9 8 7 7
  else if m == 1 then effectiveAtRowSize s 10 8 7 7 7
  else if m == 2 then effectiveAtRowSize s 9 8 7 6 6
  else if m == 3 then effectiveAtRowSize s 8 7 7 6 6
  else if m == 4 then effectiveAtRowSize s 7 7 6 6 6
  else if m == 5 then effectiveAtRowSize s 6 6 6 6 6
  else if m == 6 then effectiveAtRowSize s 5 6 6 5 5
  else effectiveAtRowSize s 4 5 5 5 5

def individualEffectiveLowerFiveAt (m s : BitVec 8) : BitVec 8 :=
  if m == 0 then effectiveAtRowSize s 12 9 8 7 6
  else if m == 1 then effectiveAtRowSize s 11 9 8 7 6
  else if m == 2 then effectiveAtRowSize s 10 8 7 7 6
  else if m == 3 then effectiveAtRowSize s 9 8 7 6 6
  else if m == 4 then effectiveAtRowSize s 8 7 7 6 6
  else if m == 5 then effectiveAtRowSize s 7 7 6 6 5
  else if m == 6 then effectiveAtRowSize s 6 6 6 6 5
  else if m == 7 then effectiveAtRowSize s 5 6 6 5 5
  else effectiveAtRowSize s 4 5 5 5 5

def individualEffectiveLowerFive (bits : Encoding) (p : Nat) : BitVec 8 :=
  individualEffectiveLowerFiveAt (externalMissing 5 bits) (pEOut 5 bits p)

def individualEffectiveLower (eCount : Nat) (bits : Encoding)
    (p : Nat) : BitVec 8 :=
  if eCount = 4 then individualEffectiveLowerFour bits p
  else individualEffectiveLowerFive bits p

def reachesPH (bits : Encoding) (p q : Nat) : Bool :=
  decide (p != q) && (pArc bits p q || any 10 fun middle =>
    let w := if middle < 6 then 8 + middle else 1 + (middle - 6)
    decide (w != 8 + p) && decide (w != 8 + q) &&
      (if w < 8 then pToA bits p w else pArc bits p (w - 8)) &&
      (if w < 8 then aToP bits w q else pArc bits (w - 8) q))

def reachCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 (reachesPH bits p)

def pSecondPCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 fun q => !pArc bits p q && reachesPH bits p q

def pEffectiveCondition (eCount : Nat) (_reached : Bool)
    (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + individualEffectiveLower eCount bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut eCount bits p)

def pEffectiveConditionFive (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + individualEffectiveLowerFive bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut 5 bits p)

def pEffectiveConditionFiveAt (m : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p +
      individualEffectiveLowerFiveAt (BitVec.ofNat 8 m) (pEOut 5 bits p) + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut 5 bits p)

def pSecondECount (eCount : Nat) (bits : Encoding) (p : Nat) : BitVec 8 :=
  count eCount fun e => !pToE bits p e &&
    any 6 fun q => pArc bits p q && pToE bits q e

def pSecondHCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 4 fun h => !pToH bits p h &&
    any 6 fun q => pArc bits p q && pToH bits q h

def pRestrictedNonSeymour (eCount : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + pSecondHCount bits p +
      pSecondECount eCount bits p).ult
    (pOut bits p + pHOut bits p + pEOut eCount bits p)

def defectLoss (d : BitVec 8) : BitVec 8 :=
  if d == 0 then 0 else if d.ule 2 then 1 else if d.ule 5 then 2
  else if d.ule 9 then 3 else if d.ule 14 then 4 else 5

def sharpKing (bits : Encoding) : Bool :=
  any 6 fun p => all 6 (fun q => (pOut bits q).ule (pOut bits p)) &&
    (5 - defectLoss (internalMissing bits)).ule (reachCount bits p)

def score (bits : Encoding) (p : Nat) : BitVec 8 :=
  pOut bits p + pHOut bits p

def scoreKing (bits : Encoding) : Bool :=
  all 6 fun p => !(all 6 fun q => (score bits q).ule (score bits p)) ||
    (5 - defectLoss (internalMissing bits + crossMissing bits)).ule
      (reachCount bits p)

def equalScoreClass (bits : Encoding) : Bool :=
  all 6 fun p =>
    let classSize := count 6 fun q => score bits q == score bits p
    let reached := count 6 fun q =>
      score bits q == score bits p && reachesPH bits p q
    classSize.ule
      (reached + defectLoss (internalMissing bits + crossMissing bits) + 1)

def isExact (eCount : Nat) (_reached : Bool) (bits : Encoding)
    (p : Nat) : Bool :=
  pOut bits p + pHOut bits p + pEOut eCount bits p == 8
def exactCount (eCount : Nat) (reached : Bool) (bits : Encoding) : BitVec 8 :=
  count 6 (isExact eCount reached bits)
def exactInternal (eCount : Nat) (reached : Bool) (bits : Encoding)
    (p : Nat) : BitVec 8 :=
  count 6 fun q => isExact eCount reached bits q && pArc bits p q
def exactOutside (eCount : Nat) (reached : Bool) (bits : Encoding)
    (p : Nat) : BitVec 8 :=
  count 6 fun q => !isExact eCount reached bits q && pArc bits p q
def exactMissing (eCount : Nat) (reached : Bool) (bits : Encoding) : BitVec 8 :=
  count 36 fun k =>
    let i := k / 6
    let j := k % 6
    decide (i < j) && isExact eCount reached bits i &&
      isExact eCount reached bits j && !pArc bits i j && !pArc bits j i

def exactClassKing (eCount : Nat) (reached : Bool) (bits : Encoding) : Bool :=
  exactCount eCount reached bits == 0 || any 6 fun p =>
    isExact eCount reached bits p &&
    all 6 (fun q => !isExact eCount reached bits q ||
      (exactInternal eCount reached bits q).ule
        (exactInternal eCount reached bits p)) &&
    (pEOut eCount bits p + individualEffectiveLower eCount bits p +
      exactOutside eCount reached bits p + exactCount eCount reached bits).ule
        (16 + defectLoss (exactMissing eCount reached bits))

/-- One of the pivot's eight outneighbors: `A1[2]` followed by `P[6]`. -/
def pivotNeighbor (i : Nat) : Nat := if i < 2 then 1 + i else 8 + (i - 2)
/-- The seven represented second targets in a tight width-five row. -/
def secondTarget (i : Nat) : Nat := if i < 2 then 3 + i else 14 + (i - 2)

def privateTarget (reached : Bool) (bits : Encoding)
    (deleted target : Nat) : Bool :=
  coreArc 5 reached bits (pivotNeighbor deleted) (secondTarget target) &&
    all 8 fun other => decide (other = deleted) ||
      !coreArc 5 reached bits (pivotNeighbor other) (secondTarget target)

def deletedReached (reached : Bool) (bits : Encoding) (deleted : Nat) : Bool :=
  any 8 fun other => decide (other != deleted) &&
    coreArc 5 reached bits (pivotNeighbor other) (pivotNeighbor deleted)

def tightPrivate (reached : Bool) (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (count 7 (privateTarget reached bits deleted)).ule
      (bitCount (deletedReached reached bits deleted))

def pRowKey (eCount : Nat) (_reached : Bool) (bits : Encoding)
    (p : Nat) : BitVec 16 :=
  (pOut bits p + pHOut bits p + pEOut eCount bits p).zeroExtend 16 * 4096 +
    (pEOut eCount bits p).zeroExtend 16 * 256 +
    (pHOut bits p).zeroExtend 16 * 16 + (pOut bits p).zeroExtend 16

def orderedP (eCount : Nat) (reached : Bool) (bits : Encoding) : Bool :=
  all 5 fun p => (pRowKey eCount reached bits (p + 1)).ule
    (pRowKey eCount reached bits p)

def orderedStructuralClasses (bits : Encoding) : Bool :=
  (aBOut bits 2).ule (aBOut bits 1) &&
    (aBOut bits 4).ule (aBOut bits 3) &&
    all 2 (fun r => (aBOut bits (6 + r)).ule (aBOut bits (5 + r)))

def orderedExternal (eCount : Nat) (reached : Bool)
    (bits : Encoding) : Bool :=
  let start := if reached then 1 else 0
  all (eCount - start - 1) fun e =>
    (count 6 fun p => pToE bits p (start + e + 1)).ule
      (count 6 fun p => pToE bits p (start + e))

/-- Descending lexicographic order on Boolean incidence signatures. -/
def lexGe : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0, _, _ => true
  | n + 1, left, right =>
      if left n == right n then lexGe n left right else left n

/-- The full `P↔H` signature of an `H` column.  The two `A₁` columns and
the two `X` columns may each be sorted independently. -/
def phColumnBit (bits : Encoding) (h k : Nat) : Bool :=
  if k < 6 then pToH bits k h else hToP bits h (k - 6)

def orderedHSignatures (bits : Encoding) : Bool :=
  lexGe 12 (phColumnBit bits 0) (phColumnBit bits 1) &&
    lexGe 12 (phColumnBit bits 2) (phColumnBit bits 3)

/-- After the reached `Q` column (when present), the `Z` columns are
interchangeable and may be sorted by their complete `P`-incidence vectors. -/
def orderedExternalSignatures (eCount : Nat) (reached : Bool)
    (bits : Encoding) : Bool :=
  let start := if reached then 1 else 0
  all (eCount - start - 1) fun e =>
    lexGe 6 (fun p => pToE bits p (start + e))
      (fun p => pToE bits p (start + e + 1))

def orderedStructuralFull (bits : Encoding) : Bool :=
  (aBOut bits 2).ule (aBOut bits 1) &&
    (!(aBOut bits 1 == aBOut bits 2) ||
      lexGe 12 (phColumnBit bits 0) (phColumnBit bits 1)) &&
  (aBOut bits 4).ule (aBOut bits 3) &&
    (!(aBOut bits 3 == aBOut bits 4) ||
      lexGe 12 (phColumnBit bits 2) (phColumnBit bits 3)) &&
  all 2 (fun r => (aBOut bits (6 + r)).ule (aBOut bits (5 + r)))

def orderedExternalFull (eCount : Nat) (reached : Bool)
    (bits : Encoding) : Bool :=
  let start := if reached then 1 else 0
  all (eCount - start - 1) fun e =>
    let left := start + e
    let right := start + e + 1
    (count 6 fun p => pToE bits p right).ule
      (count 6 fun p => pToE bits p left) &&
    (!(count 6 (fun p => pToE bits p left) ==
        count 6 (fun p => pToE bits p right)) ||
      lexGe 6 (fun p => pToE bits p left)
        (fun p => pToE bits p right))

def commonCore (eCount : Nat) (reached : Bool) (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits && fixedA bits &&
  everyXReached bits && qStructure reached bits &&
  allExternalReached eCount reached bits && inactiveEZero eCount bits &&
  (3 : BitVec 8).ule (count 4 fun k =>
    let a := k / 2
    let x := k % 2
    aArc bits (1 + a) (3 + x)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour eCount reached bits) &&
  pMinimumDegree eCount reached bits &&
  all 6 (pNonSeymour eCount reached bits) &&
  all 6 (pEffectiveCondition eCount reached bits) && sharpKing bits &&
  scoreKing bits && equalScoreClass bits && exactClassKing eCount reached bits &&
  orderedP eCount reached bits && orderedStructuralFull bits &&
  orderedExternalFull eCount reached bits

def commonBareCore (eCount : Nat) (reached : Bool) (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits && fixedA bits &&
  everyXReached bits && qStructure reached bits &&
  allExternalReached eCount reached bits && inactiveEZero eCount bits &&
  (3 : BitVec 8).ule (count 4 fun k =>
    let a := k / 2
    let x := k % 2
    aArc bits (1 + a) (3 + x)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour eCount reached bits) &&
  pMinimumDegree eCount reached bits &&
  all 6 (pNonSeymour eCount reached bits) &&
  all 6 (pEffectiveCondition eCount reached bits) && sharpKing bits &&
  scoreKing bits && equalScoreClass bits && exactClassKing eCount reached bits

def core (eCount : Nat) (reached : Bool) (bits : Encoding) : Bool :=
  commonCore eCount reached bits &&
  (!decide (eCount = 5) || tightPrivate reached bits) &&
  (16 - (if reached then aOneToQ bits else 0)).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing eCount bits).ule
    (BitVec.ofNat 8 (6 * eCount - 9))

def cCore (eCount c : Nat) (bits : Encoding) : Bool :=
  core eCount true bits && aOneToQ bits == BitVec.ofNat 8 c

def defectCore (eCount : Nat) (reached : Bool) (c m : Nat)
    (bits : Encoding) : Bool :=
  core eCount reached bits &&
    (!reached || aOneToQ bits == BitVec.ofNat 8 c) &&
    externalMissing eCount bits == BitVec.ofNat 8 m

/-- The projected exact-defect core.  All omitted `A` predicates are used
only to derive the displayed scalar and row-wise consequences. -/
def projectedDefectCore (eCount : Nat) (reached : Bool) (c m : Nat)
    (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits &&
  allExternalReached eCount reached bits && inactiveEZero eCount bits &&
  pMinimumDegree eCount reached bits &&
  all 6 (pEffectiveCondition eCount reached bits) &&
  all 6 (pRestrictedNonSeymour eCount bits) &&
  sharpKing bits && scoreKing bits && equalScoreClass bits &&
  exactClassKing eCount reached bits &&
  orderedP eCount reached bits && orderedExternal eCount reached bits &&
  orderedHSignatures bits &&
  orderedExternalSignatures eCount reached bits &&
  (16 - BitVec.ofNat 8 c).ule (totalHToP bits) &&
  externalMissing eCount bits == BitVec.ofNat 8 m &&
  (totalHToP bits + externalMissing eCount bits).ule
    (BitVec.ofNat 8 (6 * eCount - 9))

def projectedCore (eCount : Nat) (reached : Bool) (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits &&
  allExternalReached eCount reached bits && inactiveEZero eCount bits &&
  pMinimumDegree eCount reached bits &&
  all 6 (pEffectiveCondition eCount reached bits) &&
  all 6 (pRestrictedNonSeymour eCount bits) &&
  sharpKing bits && scoreKing bits && equalScoreClass bits &&
  exactClassKing eCount reached bits &&
  orderedP eCount reached bits && orderedExternal eCount reached bits &&
  orderedHSignatures bits &&
  orderedExternalSignatures eCount reached bits &&
  (16 - (if reached then aOneToQ bits else 0)).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing eCount bits).ule
    (BitVec.ofNat 8 (6 * eCount - 9))

def projectedLeaf (eCount : Nat) (reached : Bool)
    (cValue mValue alphaValue betaValue : Nat) (bits : Encoding) : Bool :=
  projectedCore eCount reached bits &&
  (!reached || aOneToQ bits == BitVec.ofNat 8 cValue) &&
  externalMissing eCount bits == BitVec.ofNat 8 mValue &&
  (BitVec.ofNat 8 (8 + cValue) - totalPToH bits) ==
    BitVec.ofNat 8 alphaValue &&
  internalMissing bits == BitVec.ofNat 8 betaValue

/-!
The common five-column projection also covers the four-column reached row:
append one zero column.  Its external defect rises by six, while every other
displayed incidence statistic is unchanged.  Sorting all four `H` columns
and all five auxiliary columns is sound because this projection forgets the
structural subclasses inside each family.
-/

def orderedAllHSignatures (bits : Encoding) : Bool :=
  all 3 fun h => lexGe 12 (phColumnBit bits h) (phColumnBit bits (h + 1))

def orderedAllExternalSignatures (bits : Encoding) : Bool :=
  all 4 fun e => lexGe 6 (fun p => pToE bits p e)
    (fun p => pToE bits p (e + 1))

def firstFourExternalReached (bits : Encoding) : Bool :=
  all 4 fun e => any 6 fun p => pToE bits p e

def sharpKingAt (bits : Encoding) (p : Nat) : Bool :=
  all 6 (fun q => (pOut bits q).ule (pOut bits p)) &&
    (5 - defectLoss (internalMissing bits)).ule (reachCount bits p)

def scoreKingAt (bits : Encoding) (p : Nat) : Bool :=
  all 6 (fun q => (score bits q).ule (score bits p)) &&
    (5 - defectLoss (internalMissing bits + crossMissing bits)).ule
      (reachCount bits p)

def exactClassKingAt (bits : Encoding) (p : Nat) : Bool :=
  isExact 5 true bits p &&
    all 6 (fun q => !isExact 5 true bits q ||
      (exactInternal 5 true bits q).ule (exactInternal 5 true bits p)) &&
    (pEOut 5 bits p + individualEffectiveLower 5 bits p +
      exactOutside 5 true bits p + exactCount 5 true bits).ule
        (16 + defectLoss (exactMissing 5 true bits))

/-- Witness-first `P` normalization: a score king is `p0`; a sharp king is
`p0` or `p1`; and a nonempty exact class has a king among `p0,p1,p2`.
The three remaining labels are sorted by the unary row key. -/
def canonicalP (bits : Encoding) : Bool :=
  scoreKingAt bits 0 &&
  (sharpKingAt bits 0 || sharpKingAt bits 1) &&
  (exactCount 5 true bits == 0 || exactClassKingAt bits 0 ||
    exactClassKingAt bits 1 || exactClassKingAt bits 2) &&
  all 2 fun i => (pRowKey 5 true bits (4 + i)).ule
    (pRowKey 5 true bits (3 + i))

def externalFirstRowKey (bits : Encoding) (p : Nat) : BitVec 16 :=
  (pEOut 5 bits p).zeroExtend 16 * 4096 +
    (pOut bits p + pHOut bits p + pEOut 5 bits p).zeroExtend 16 * 256 +
    (pHOut bits p).zeroExtend 16 * 16 + (pOut bits p).zeroExtend 16

def orderedPExternalFirst (bits : Encoding) : Bool :=
  all 5 fun p => (externalFirstRowKey bits (p + 1)).ule
    (externalFirstRowKey bits p)

/-- A relaxation of the pivot-neighbor single-deletion inequality.  Among
auxiliary targets private to one `P` row, at most the unique `Q` column can
also have an `A₁` source; every other such column is genuinely private.
Allowing all four `H` rows on the right keeps the consequence invariant under
abstract `H` relabeling. -/
def privateExternalCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 5 fun e => pToE bits p e && all 6 (fun q =>
    decide (q = p) || !pToE bits q e)

def deletedPReachedRelaxed (bits : Encoding) (p : Nat) : Bool :=
  any 4 (fun h => hToP bits h p) ||
    any 6 (fun q => decide (q != p) && pArc bits q p)

def pTightPrivate (bits : Encoding) : Bool :=
  all 6 fun p => (privateExternalCount bits p).ule
    (bitCount (deletedPReachedRelaxed bits p) + 1)

def universalCore (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits &&
  firstFourExternalReached bits &&
  pMinimumDegree 5 true bits &&
  all 6 (pEffectiveCondition 5 true bits) &&
  all 6 (pRestrictedNonSeymour 5 bits) &&
  pTightPrivate bits && sharpKing bits && scoreKing bits &&
  equalScoreClass bits && exactClassKing 5 true bits &&
  orderedPExternalFirst bits &&
  orderedAllHSignatures bits &&
  orderedAllExternalSignatures bits &&
  (14 : BitVec 8).ule (totalHToP bits) &&
  (totalPToH bits).ule 10 &&
  (totalHToP bits + externalMissing 5 bits).ule 21

def canonicalUniversalCore (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits &&
  firstFourExternalReached bits &&
  pMinimumDegree 5 true bits &&
  all 6 (pEffectiveCondition 5 true bits) &&
  all 6 (pRestrictedNonSeymour 5 bits) &&
  pTightPrivate bits && canonicalP bits && equalScoreClass bits &&
  all 2 (fun i => (pRowKey 5 true bits (4 + i)).ule
    (pRowKey 5 true bits (3 + i))) &&
  orderedAllHSignatures bits && orderedAllExternalSignatures bits &&
  (14 : BitVec 8).ule (totalHToP bits) &&
  (totalPToH bits).ule 10 &&
  (totalHToP bits + externalMissing 5 bits).ule 21

def canonicalUniversalLeaf (mValue phValue betaValue : Nat)
    (bits : Encoding) : Bool :=
  canonicalUniversalCore bits &&
  externalMissing 5 bits == BitVec.ofNat 8 mValue &&
  totalPToH bits == BitVec.ofNat 8 phValue &&
  internalMissing bits == BitVec.ofNat 8 betaValue

def universalLeaf (mValue phValue betaValue : Nat)
    (bits : Encoding) : Bool :=
  universalCore bits &&
  externalMissing 5 bits == BitVec.ofNat 8 mValue &&
  totalPToH bits == BitVec.ofNat 8 phValue &&
  internalMissing bits == BitVec.ofNat 8 betaValue

def universalM (mValue : Nat) (bits : Encoding) : Bool :=
  universalCore bits &&
  externalMissing 5 bits == BitVec.ofNat 8 mValue

/-! A small residual core retaining only the `A₁/X` data used by the hand
argument.  It specializes to the hard reached row with both `A₁ → q`
arcs present; the other `A` and `R → P` bits remain irrelevant. -/

def hArc (bits : Encoding) (h k : Nat) : Bool :=
  aArc bits (1 + h) (1 + k)

/-- `t=0` is `a₁`; `t=1,2,3` are the three vertices of `R`. -/
def xToT (bits : Encoding) (x t : Nat) : Bool :=
  aArc bits (3 + x) (if t = 0 then 0 else 4 + t)

def hToQTwo (bits : Encoding) (h : Nat) : Bool :=
  if h < 2 then true else aToQ bits (1 + h)

def hDirectTwo (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 4 (hArc bits h) + hPOut bits h + bitCount (hToQTwo bits h) +
    (if h < 2 then 0 else count 4 (xToT bits (h - 2)))

def orientedHH (bits : Encoding) : Bool :=
  all 4 fun h => !hArc bits h h && all 4 fun k =>
    decide (h = k) || !(hArc bits h k && hArc bits k h)

def aOneSecondH (bits : Encoding) (a h : Nat) : Bool :=
  decide (a != h) && !hArc bits a h &&
    (any 4 (fun k => decide (k != a) && decide (k != h) &&
      hArc bits a k && hArc bits k h) ||
    any 6 (fun p => hToP bits a p && pToH bits p h) ||
    (decide (2 ≤ a) && decide (h < 2) && xToT bits (a - 2) 0))

def aOneSecondP (bits : Encoding) (a p : Nat) : Bool :=
  !hToP bits a p &&
    (any 4 (fun h => decide (h != a) &&
      hArc bits a h && hToP bits h p) ||
    any 6 (fun q => hToP bits a q && pArc bits q p) ||
    (decide (2 ≤ a) && xToT bits (a - 2) 0))

def aOneSecondZ (bits : Encoding) (a z : Nat) : Bool :=
  any 6 fun p => hToP bits a p && pToE bits p (1 + z)

def aOneSecondT (bits : Encoding) (a t : Nat) : Bool :=
  (if a < 2 then true else !xToT bits (a - 2) t) &&
    any 2 fun x => hArc bits a (2 + x) && xToT bits x t

def hSecondQ (bits : Encoding) (h : Nat) : Bool :=
  !hToQTwo bits h &&
    (any 4 (fun k => decide (k != h) &&
      hArc bits h k && hToQTwo bits k) ||
    any 6 (fun p => hToP bits h p && pToE bits p 0))

def aOneRestrictedSecondCount (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 4 (aOneSecondH bits a) + count 6 (aOneSecondP bits a) +
    count 4 (aOneSecondZ bits a) + count 4 (aOneSecondT bits a) +
    bitCount (hSecondQ bits a)

def aOneRestrictedNonSeymour (bits : Encoding) (a : Nat) : Bool :=
  (aOneRestrictedSecondCount bits a).ult (hDirectTwo bits a)

def pSecondTCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 4 fun t => any 2 fun x =>
    pToH bits p (2 + x) && xToT bits x t

def pSecondHMicroCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 4 fun h => !pToH bits p h &&
    (any 6 (fun q => pArc bits p q && pToH bits q h) ||
      any 4 (fun k => pToH bits p k && hArc bits k h))

def pSecondEMicroCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 5 fun e => !pToE bits p e &&
    (any 6 (fun q => pArc bits p q && pToE bits q e) ||
      (decide (e = 0) && any 4 (fun h =>
        pToH bits p h && hToQTwo bits h)))

def pMicroNonSeymour (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + pSecondHMicroCount bits p +
      pSecondEMicroCount bits p + pSecondTCount bits p).ult
    (pOut bits p + pHOut bits p + pEOut 5 bits p)

def microCoreCTwo (m alpha : Nat) (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && orientedHH bits &&
  all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
    (!(count 4 (hArc bits a) == 2) ||
      (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQTwo bits a)))) &&
  all 4 (fun h => (8 : BitVec 8).ule (hDirectTwo bits h)) &&
  everyXReached bits && all 4 (fun z => any 6 fun p => pToE bits p (1 + z)) &&
  all 6 (fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut 5 bits p)) &&
  all 4 (aOneRestrictedNonSeymour bits) &&
  all 6 (pMicroNonSeymour bits) &&
  externalMissing 5 bits == BitVec.ofNat 8 m &&
  totalPToH bits == BitVec.ofNat 8 (10 - alpha) &&
  (14 : BitVec 8).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing 5 bits).ule 21

def hToQCore (_c : Nat) (bits : Encoding) (h : Nat) : Bool :=
  aToQ bits (1 + h)

def hDirectCore (c : Nat) (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 4 (hArc bits h) + hPOut bits h + bitCount (hToQCore c bits h) +
    (if h < 2 then 0 else count 4 (xToT bits (h - 2)))

def hSecondQCore (c : Nat) (bits : Encoding) (h : Nat) : Bool :=
  !hToQCore c bits h &&
    (any 4 (fun k => decide (k != h) &&
      hArc bits h k && hToQCore c bits k) ||
    any 6 (fun p => hToP bits h p && pToE bits p 0))

def hRestrictedSecondCountCore (c : Nat) (bits : Encoding)
    (h : Nat) : BitVec 8 :=
  count 4 (aOneSecondH bits h) + count 6 (aOneSecondP bits h) +
    count 4 (aOneSecondZ bits h) + count 4 (aOneSecondT bits h) +
    bitCount (hSecondQCore c bits h)

def hRestrictedNonSeymourCore (c : Nat) (bits : Encoding) (h : Nat) : Bool :=
  (hRestrictedSecondCountCore c bits h).ult (hDirectCore c bits h)

def pSecondEMicroCoreCount (c : Nat) (bits : Encoding)
    (p : Nat) : BitVec 8 :=
  count 5 fun e => !pToE bits p e &&
    (any 6 (fun q => pArc bits p q && pToE bits q e) ||
      (decide (e = 0) && any 4 (fun h =>
        pToH bits p h && hToQCore c bits h)))

def pMicroNonSeymourCore (c : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + pSecondHMicroCount bits p +
      pSecondEMicroCoreCount c bits p + pSecondTCount bits p).ult
    (pOut bits p + pHOut bits p + pEOut 5 bits p)

def microCore (c : Nat) (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && orientedHH bits &&
  all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
    (!(count 4 (hArc bits a) == 2) ||
      (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) &&
  all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) &&
  everyXReached bits &&
  ((decide (0 < c)) || any 6 (fun p => pToE bits p 0) ||
    any 2 (fun x => hToQCore c bits (2 + x))) &&
  all 4 (fun z => any 6 fun p => pToE bits p (1 + z)) &&
  all 6 (fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut 5 bits p)) &&
  all 4 (hRestrictedNonSeymourCore c bits) &&
  all 6 (pMicroNonSeymourCore c bits) &&
  aOneToQ bits == BitVec.ofNat 8 c &&
  (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing 5 bits).ule 21

/-- The reached local core with only the four `H`-row second-neighborhood
constraints.  The `P`-row constraints are unnecessary in the low-cross
remainder once all six individual-effective inequalities are retained. -/
def microHCore (c : Nat) (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && orientedHH bits &&
  all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
    (!(count 4 (hArc bits a) == 2) ||
      (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) &&
  all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) &&
  everyXReached bits &&
  ((decide (0 < c)) || any 6 (fun p => pToE bits p 0) ||
    any 2 (fun x => hToQCore c bits (2 + x))) &&
  all 4 (fun z => any 6 fun p => pToE bits p (1 + z)) &&
  all 6 (fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut 5 bits p)) &&
  all 4 (hRestrictedNonSeymourCore c bits) &&
  aOneToQ bits == BitVec.ofNat 8 c &&
  (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing 5 bits).ule 21

def microLeaf (c m alpha : Nat) (bits : Encoding) : Bool :=
  microCore c bits &&
  externalMissing 5 bits == BitVec.ofNat 8 m &&
  totalPToH bits == BitVec.ofNat 8 (8 + c - alpha)

def microCZeroResidual (bits : Encoding) : Bool :=
  microCore 0 bits && totalPToH bits == 4

def microCZeroNonHard (bits : Encoding) : Bool :=
  microCore 0 bits && (4 : BitVec 8).ule (totalPToH bits) &&
    (totalPToH bits).ule 8

/-! Width-specialized local cores for the other two parameter rows.  These
use the same incidence layout.  In the four-column reached row `E[0]=q` and
`E[1..3]=Z`; in the unreached row all five `E` columns are `Z` and no vertex
of `H ∪ P` points to `q`. -/

def hSecondZCount (zCount offset : Nat) (bits : Encoding) (h : Nat) : BitVec 8 :=
  count zCount fun z => any 6 fun p => hToP bits h p && pToE bits p (offset + z)

def hRestrictedSecondCountFour (c : Nat) (bits : Encoding)
    (h : Nat) : BitVec 8 :=
  count 4 (aOneSecondH bits h) + count 6 (aOneSecondP bits h) +
    hSecondZCount 3 1 bits h + count 4 (aOneSecondT bits h) +
    bitCount (hSecondQCore c bits h)

def hRestrictedNonSeymourFour (c : Nat) (bits : Encoding) (h : Nat) : Bool :=
  (hRestrictedSecondCountFour c bits h).ult (hDirectCore c bits h)

def pMicroNonSeymourFour (c : Nat) (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + pSecondHMicroCount bits p +
      pSecondEMicroCoreCount c bits p + pSecondTCount bits p).ult
    (pOut bits p + pHOut bits p + pEOut 4 bits p)

def microFour (c : Nat) (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && orientedHH bits &&
  all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
    (!(count 4 (hArc bits a) == 2) ||
      (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) &&
  all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) &&
  everyXReached bits &&
  ((decide (0 < c)) || any 6 (fun p => pToE bits p 0) ||
    any 2 (fun x => hToQCore c bits (2 + x))) &&
  all 3 (fun z => any 6 fun p => pToE bits p (1 + z)) &&
  all 6 (fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut 4 bits p)) &&
  all 4 (hRestrictedNonSeymourFour c bits) &&
  all 6 (pMicroNonSeymourFour c bits) &&
  aOneToQ bits == BitVec.ofNat 8 c &&
  (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) &&
  (totalHToP bits + (24 - totalPToE 4 bits)).ule 15 &&
  (totalPToH bits).ule (BitVec.ofNat 8 (8 + c))

def hDirectUnreached (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 4 (hArc bits h) + hPOut bits h +
    (if h < 2 then 0 else count 4 (xToT bits (h - 2)))

def hRestrictedSecondCountUnreached (bits : Encoding)
    (h : Nat) : BitVec 8 :=
  count 4 (aOneSecondH bits h) + count 6 (aOneSecondP bits h) +
    hSecondZCount 5 0 bits h + count 4 (aOneSecondT bits h)

def hRestrictedNonSeymourUnreached (bits : Encoding) (h : Nat) : Bool :=
  (hRestrictedSecondCountUnreached bits h).ult (hDirectUnreached bits h)

def pMicroNonSeymourUnreached (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + pSecondHMicroCount bits p +
      pSecondECount 5 bits p + pSecondTCount bits p).ult
    (pOut bits p + pHOut bits p + pEOut 5 bits p)

def microUnreached (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && orientedHH bits &&
  all 4 (fun h => !hToQCore 0 bits h) &&
  all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
    (!(count 4 (hArc bits a) == 2) ||
      (6 : BitVec 8).ule (hPOut bits a))) &&
  all 4 (fun h => (8 : BitVec 8).ule (hDirectUnreached bits h)) &&
  everyXReached bits && all 5 (fun z => any 6 fun p => pToE bits p z) &&
  all 6 (fun p => (8 : BitVec 8).ule
    (pOut bits p + pHOut bits p + pEOut 5 bits p)) &&
  all 4 (hRestrictedNonSeymourUnreached bits) &&
  all 6 (pMicroNonSeymourUnreached bits) &&
  (3 : BitVec 8).ule (totalPToH bits) &&
  (totalPToH bits).ule 8

def microCOneHighAlpha (bits : Encoding) : Bool :=
  microCore 1 bits && (totalPToH bits).ule 6

def microCOneAll (bits : Encoding) : Bool :=
  microCore 1 bits && (totalPToH bits).ule 9

def microCOneHighPH (bits : Encoding) : Bool :=
  microCore 1 bits && (6 : BitVec 8).ule (totalPToH bits) &&
    (totalPToH bits).ule 9

def microCOneNonHard (bits : Encoding) : Bool :=
  microCore 1 bits && (totalPToH bits).ule 9 &&
  !(totalPToH bits == 3 && externalMissing 5 bits == 0)

def microCOnePositiveMissing (bits : Encoding) : Bool :=
  microCore 1 bits && (totalPToH bits).ule 9 &&
  (1 : BitVec 8).ule (externalMissing 5 bits)

def microCOneLowAlphaHighMissing (bits : Encoding) : Bool :=
  microCore 1 bits &&
    ((totalPToH bits == 9 && (5 : BitVec 8).ule (externalMissing 5 bits)) ||
      (totalPToH bits == 8 && externalMissing 5 bits == 5))

def microCTwoResidual (bits : Encoding) : Bool :=
  microCore 2 bits &&
    ((totalPToH bits == 9 && (5 : BitVec 8).ule (externalMissing 5 bits)) ||
      (totalPToH bits == 8 && (4 : BitVec 8).ule (externalMissing 5 bits)) ||
      totalPToH bits == 7 ||
      (totalPToH bits == 6 && externalMissing 5 bits == 3))

def microCTwoHighPH (bits : Encoding) : Bool :=
  microCore 2 bits && (7 : BitVec 8).ule (totalPToH bits) &&
    (totalPToH bits).ule 10

def reachedFullHybrid (c : Nat) (bits : Encoding) : Bool :=
  commonBareCore 5 true bits && tightPrivate true bits &&
  aOneToQ bits == BitVec.ofNat 8 c &&
  (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) &&
  (totalHToP bits + externalMissing 5 bits).ule 21 &&
  (totalPToH bits).ule (BitVec.ofNat 8 (8 + c)) &&
  microCore c bits

/-- The small local obstruction, supplemented only by the two projected
consequences needed for the equality leaves: every `P` row obeys the
individual-effective inequality, and some `P` row is a sharp king. -/
def reachedEffectiveHybrid (c : Nat) (bits : Encoding) : Bool :=
  microCore c bits &&
  all 6 (pEffectiveCondition 5 true bits) && sharpKing bits &&
  (totalPToH bits).ule (BitVec.ofNat 8 (8 + c))

def reachedProjectedHybrid (c : Nat) (bits : Encoding) : Bool :=
  reachedEffectiveHybrid c bits && scoreKing bits && equalScoreClass bits &&
  exactClassKing 5 true bits

def reachedEffectiveLeaf (c m alpha : Nat) (bits : Encoding) : Bool :=
  reachedEffectiveHybrid c bits &&
  externalMissing 5 bits == BitVec.ofNat 8 m &&
  totalPToH bits == BitVec.ofNat 8 (8 + c - alpha)

/-- The low-`P → H` remainder after the local high-cross certificates. -/
def reachedEffectiveLowPH (c bound : Nat) (bits : Encoding) : Bool :=
  reachedEffectiveHybrid c bits &&
  (totalPToH bits).ule (BitVec.ofNat 8 bound)

def reachedEffectivePH (c ph : Nat) (bits : Encoding) : Bool :=
  reachedEffectiveHybrid c bits && totalPToH bits == BitVec.ofNat 8 ph

def reachedPOnlyPH (c ph : Nat) (bits : Encoding) : Bool :=
  orientedP bits && pMinimumDegree 5 true bits &&
  all 6 (pEffectiveCondition 5 true bits) && sharpKing bits &&
  totalPToH bits == BitVec.ofNat 8 ph &&
  (externalMissing 5 bits).ule (BitVec.ofNat 8 (5 + c))

def pFullSignatureBit (bits : Encoding) (p k : Nat) : Bool :=
  if k < 6 then pArc bits p k
  else if k < 12 then pArc bits (k - 6) p
  else if k < 16 then pToH bits p (k - 12)
  else if k < 20 then hToP bits (k - 16) p
  else pToE bits p (k - 20)

def orderedPTailSignatures (bits : Encoding) : Bool :=
  all 4 fun i => lexGe 25 (pFullSignatureBit bits (1 + i))
    (pFullSignatureBit bits (2 + i))

def hFullSignatureBit (bits : Encoding) (h k : Nat) : Bool :=
  if k < 4 then hArc bits h k
  else if k < 8 then hArc bits (k - 4) h
  else if k < 14 then hToP bits h (k - 8)
  else if k < 20 then pToH bits (k - 14) h
  else if k = 20 then aToQ bits (1 + h)
  else if h < 2 then false else xToT bits (h - 2) (k - 21)

def orderedStructuralPairSignatures (bits : Encoding) : Bool :=
  lexGe 25 (hFullSignatureBit bits 0) (hFullSignatureBit bits 1) &&
  lexGe 25 (hFullSignatureBit bits 2) (hFullSignatureBit bits 3)

def distinguishedAOne (bits : Encoding) : Bool :=
  count 4 (hArc bits 0) == 2 && hArc bits 0 2 && hArc bits 0 3

def reachedEffectiveLowPHDistinguished (c bound : Nat)
    (bits : Encoding) : Bool :=
  reachedEffectiveLowPH c bound bits && distinguishedAOne bits

def reachedEffectivePHDistinguished (c ph : Nat)
    (bits : Encoding) : Bool :=
  reachedEffectivePH c ph bits && distinguishedAOne bits

def microHEffectiveLowPH (c bound : Nat) (bits : Encoding) : Bool :=
  microHCore c bits && all 6 (pEffectiveCondition 5 true bits) &&
  distinguishedAOne bits &&
  (totalPToH bits).ule (BitVec.ofNat 8 bound)

def microHEffectiveLowPHMissing (c bound m : Nat) (bits : Encoding) : Bool :=
  microHCore c bits && all 6 (pEffectiveConditionFiveAt m bits) &&
  distinguishedAOne bits &&
  (totalPToH bits).ule (BitVec.ofNat 8 bound) &&
  externalMissing 5 bits == BitVec.ofNat 8 m

theorem reachedEffectiveLowPHDistinguished_implies_microH
    (c bound : Nat) (bits : Encoding)
    (h : reachedEffectiveLowPHDistinguished c bound bits = true) :
    microHEffectiveLowPH c bound bits = true := by
  simp only [reachedEffectiveLowPHDistinguished, reachedEffectiveLowPH,
    reachedEffectiveHybrid, microCore, microHEffectiveLowPH, microHCore,
    Bool.and_eq_true] at h ⊢
  aesop

theorem microHEffectiveLowPH_to_missing
    (c bound m : Nat) (bits : Encoding)
    (h : microHEffectiveLowPH c bound bits = true)
    (hm : externalMissing 5 bits = BitVec.ofNat 8 m) :
    microHEffectiveLowPHMissing c bound m bits = true := by
  rw [microHEffectiveLowPH, Bool.and_eq_true] at h
  rcases h with ⟨hHead, hPH⟩
  rw [Bool.and_eq_true] at hHead
  rcases hHead with ⟨hHead, hDist⟩
  rw [Bool.and_eq_true] at hHead
  rcases hHead with ⟨hCore, hEff⟩
  rw [microHEffectiveLowPHMissing, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · rw [Bool.and_eq_true]
        refine ⟨hCore, ?_⟩
        rw [all_eq_true_iff] at hEff ⊢
        intro p hp
        have := hEff p hp
        simpa [pEffectiveCondition, pEffectiveConditionFiveAt,
          individualEffectiveLower,
          individualEffectiveLowerFive, hm] using this
      · exact hDist
    · exact hPH
  · simp [hm]

def microFourDistinguished (c : Nat) (bits : Encoding) : Bool :=
  microFour c bits && distinguishedAOne bits

def microUnreachedDistinguished (bits : Encoding) : Bool :=
  microUnreached bits && distinguishedAOne bits

def hardResidualAOne (bits : Encoding) : Bool :=
  distinguishedAOne bits &&
  (16 : BitVec 8).ule (totalHToP bits)

def fixedSharpHybridLeaf (c m alpha : Nat) (bits : Encoding) : Bool :=
  microLeaf c m alpha bits &&
  pEffectiveConditionFiveAt m bits 0 && sharpKingAt bits 0 &&
  orderedPTailSignatures bits &&
  orderedStructuralPairSignatures bits && orderedExternalSignatures 5 true bits

def canonicalHybridLeaf (c m alpha : Nat) (bits : Encoding) : Bool :=
  microLeaf c m alpha bits &&
  all 3 (pEffectiveConditionFiveAt m bits) && equalScoreClass bits &&
  canonicalP bits && orderedStructuralPairSignatures bits &&
  orderedExternalSignatures 5 true bits

def canonicalHybridExactLeaf (c m alpha beta : Nat)
    (bits : Encoding) : Bool :=
  canonicalHybridLeaf c m alpha bits &&
  internalMissing bits == BitVec.ofNat 8 beta

def orderedLastThreeSignatures (bits : Encoding) : Bool :=
  lexGe 25 (pFullSignatureBit bits 3) (pFullSignatureBit bits 4) &&
  lexGe 25 (pFullSignatureBit bits 4) (pFullSignatureBit bits 5)

/-- A witness-coincidence branch. `sharpIndex` is `0` or `1`; an
`exactIndex` below `3` names the exact-class witness, while `3` denotes an
empty exact class. -/
def branchedHybridExactLeaf (c m alpha beta sharpIndex exactIndex : Nat)
    (bits : Encoding) : Bool :=
  microLeaf c m alpha bits &&
  all 3 (pEffectiveConditionFiveAt m bits) && equalScoreClass bits &&
  scoreKingAt bits 0 && sharpKingAt bits sharpIndex &&
  (if exactIndex < 3 then exactClassKingAt bits exactIndex
    else exactCount 5 true bits == 0) &&
  orderedLastThreeSignatures bits && orderedStructuralPairSignatures bits &&
  hardResidualAOne bits &&
  orderedExternalSignatures 5 true bits &&
  internalMissing bits == BitVec.ofNat 8 beta

def branchedHybridHPLeaf (c m alpha beta hp sharpIndex exactIndex : Nat)
    (bits : Encoding) : Bool :=
  branchedHybridExactLeaf c m alpha beta sharpIndex exactIndex bits &&
  totalHToP bits == BitVec.ofNat 8 hp &&
  (!decide (beta = 0) || completeP bits) &&
  (!decide (hp + (8 + c - alpha) = 24) || completePH bits)

def singleExternalMissingAt (row column : Nat) (bits : Encoding) : Bool :=
  all 6 fun p => all 5 fun e =>
    pToE bits p e == !(decide (p = row) && decide (e = column))

def singleMissingHybridHPLeaf
    (c alpha beta hp sharpIndex exactIndex row column : Nat)
    (bits : Encoding) : Bool :=
  branchedHybridHPLeaf c 1 alpha beta hp sharpIndex exactIndex bits &&
  singleExternalMissingAt row column bits &&
  pEffectiveConditionFiveAt 1 bits row && scoreKing bits

def singleMissingArithmeticLeaf (row column : Nat)
    (bits : Encoding) : Bool :=
  orientedP bits && orientedPH bits && pMinimumDegree 5 true bits &&
  singleExternalMissingAt row column bits &&
  internalMissing bits == 0 && crossMissing bits == 0 &&
  pEffectiveConditionFiveAt 1 bits 0 &&
  pEffectiveConditionFiveAt 1 bits 1 &&
  pEffectiveConditionFiveAt 1 bits row &&
  scoreKingAt bits 0 && sharpKingAt bits 1 && scoreKing bits

def reachedEffectiveNoMissing (c : Nat) (bits : Encoding) : Bool :=
  reachedEffectiveHybrid c bits && externalMissing 5 bits == 0

/-- Scalar equality boundary `P→H = 3+m`: degree summation forces every
`P` row to be exact and the internal `P` graph to have no missing pair. -/
def equalityBoundaryLeaf (m : Nat) (bits : Encoding) : Bool :=
  externalMissing 5 bits == BitVec.ofNat 8 m &&
  internalMissing bits == 0 && all 6 (isExact 5 true bits) &&
  pEffectiveConditionFiveAt m bits 0 && sharpKingAt bits 0

/-- The residual combines the small `H`-local obstruction with the projected
`P`-king and individual-effective consequences.  Both predicates use the
same graph incidences, so their conjunction requires no additional bits. -/
def hybridLeaf (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  microLeaf c m alpha bits && projectedDefectCore 5 true c m bits &&
    internalMissing bits == BitVec.ofNat 8 beta

/-- Equality closure for the unique `c=0, m=0, α=5` residual: every
auxiliary incidence is present, `P` is a tournament, and all `P` rows have
outdegree exactly eight. -/
def cZeroHardLeaf (bits : Encoding) : Bool :=
  hybridLeaf 0 0 5 0 bits &&
  all 6 (fun p => all 5 (fun e => pToE bits p e)) &&
  all 6 (isExact 5 true bits)

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
