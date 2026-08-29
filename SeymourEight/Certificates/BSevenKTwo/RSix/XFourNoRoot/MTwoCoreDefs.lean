import SeymourEight.Shared.FiniteCore

/-!
# The exact two-auxiliary-defect deletion core

All six `P` vertices have degree eight in this equality leaf.  The encoding
therefore retains only the local incidences used after deleting a direct
auxiliary arc, together with the seven exact outside predecessor-signature
counts of the three auxiliaries.
-/

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

open Shared.FiniteCore

abbrev Encoding := Nat → Bool

def directedIndex (i j n : Nat) : Nat := (n - 1) * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits (directedIndex i j 6)
def pToH (bits : Encoding) (p h : Nat) : Bool := bits (30 + 6 * p + h)
def hToP (bits : Encoding) (h p : Nat) : Bool := bits (66 + 6 * h + p)
def pToE (bits : Encoding) (p e : Nat) : Bool := bits (102 + 3 * p + e)
def hArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits (120 + directedIndex i j 6)
def hToAOne (bits : Encoding) (h : Nat) : Bool := bits (150 + h)
def hToR (bits : Encoding) (h : Nat) : Bool := bits (156 + h)
def hToQ (bits : Encoding) (h : Nat) : Bool := bits (162 + h)
def eToP (bits : Encoding) (e p : Nat) : Bool := bits (168 + 6 * e + p)
def eToH (bits : Encoding) (e h : Nat) : Bool := bits (186 + 6 * e + h)
def eToAOne (bits : Encoding) (e : Nat) : Bool := bits (204 + e)
def eToR (bits : Encoding) (e : Nat) : Bool := bits (207 + e)
def eToRoot (bits : Encoding) (e : Nat) : Bool := bits (210 + e)
def eArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits (213 + directedIndex i j 3)

def signatureCount (bits : Encoding) (mask : Nat) : BitVec 8 :=
  bitCount (bits (219 + 4 * mask)) +
    2 * bitCount (bits (220 + 4 * mask)) +
    4 * bitCount (bits (221 + 4 * mask)) +
    8 * bitCount (bits (222 + 4 * mask))

def rToP (bits : Encoding) (p : Nat) : Bool := bits (247 + p)
def rToQ (bits : Encoding) : Bool := bits 253
def rToAOne (bits : Encoding) : Bool := bits 254
def rToH (bits : Encoding) (h : Nat) : Bool := bits (255 + h)

def maskHas (mask e : Nat) : Bool := decide (((mask + 1) / 2 ^ e) % 2 = 1)

/-- Target indices are `a1,R,H(6),P(6),E(3),s`. -/
def pLocalArc (bits : Encoding) (p target : Nat) : Bool :=
  if target < 2 then false
  else if target < 8 then pToH bits p (target - 2)
  else if target < 14 then pArc bits p (target - 8)
  else if target < 17 then pToE bits p (target - 14)
  else false

def hLocalArc (bits : Encoding) (h target : Nat) : Bool :=
  if target = 0 then hToAOne bits h
  else if target = 1 then hToR bits h
  else if target < 8 then hArc bits h (target - 2)
  else if target < 14 then hToP bits h (target - 8)
  else if target = 14 then hToQ bits h
  else false

def eLocalArc (bits : Encoding) (e target : Nat) : Bool :=
  if target = 0 then eToAOne bits e
  else if target = 1 then eToR bits e
  else if target < 8 then eToH bits e (target - 2)
  else if target < 14 then eToP bits e (target - 8)
  else if target < 17 then eArc bits e (target - 14)
  else eToRoot bits e

def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 18 (pLocalArc bits p)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 6 (hToP bits h)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pToH bits p)
def pPOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pArc bits p)
def pEOut (bits : Encoding) (p : Nat) : BitVec 8 := count 3 (pToE bits p)

def outsideForE (bits : Encoding) (e : Nat) : BitVec 8 :=
  sumCount 7 fun mask => if maskHas mask e then signatureCount bits mask else 0

def outsideUnionCount (bits : Encoding) : BitVec 8 :=
  sumCount 7 (signatureCount bits)

def eDegree (bits : Encoding) (e : Nat) : BitVec 8 :=
  count 18 (eLocalArc bits e) + outsideForE bits e

def pReachesLocal (bits : Encoding) (p target : Nat) : Bool :=
  any 6 (fun q => pArc bits p q && pLocalArc bits q target) ||
  any 6 (fun h => pToH bits p h && hLocalArc bits h target) ||
  any 3 (fun e => pToE bits p e && eLocalArc bits e target)

def pStrictSecondLocal (bits : Encoding) (p target : Nat) : Bool :=
  decide (target ≠ 8 + p) && !pLocalArc bits p target &&
    pReachesLocal bits p target

def pLocalSecondCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 18 (pStrictSecondLocal bits p)

def aOneLocalArc (target : Nat) : Bool :=
  decide (target = 2 || target = 3 || 8 ≤ target && target < 14)

def rLocalArc (bits : Encoding) (target : Nat) : Bool :=
  if target = 0 then rToAOne bits
  else if target = 1 then false
  else if target < 8 then rToH bits (target - 2)
  else if target < 14 then rToP bits (target - 8)
  else if target = 14 then rToQ bits
  else false

/-- Local two-step reachability for an `X` row.  Its possible intermediates
are exactly `a₁`, `R`, `H`, `P`, and the reached `Q` auxiliary. -/
def hReachesLocal (bits : Encoding) (h target : Nat) : Bool :=
  (hToAOne bits h && aOneLocalArc target) ||
  (hToR bits h && rLocalArc bits target) ||
  any 6 (fun middle => hArc bits h middle &&
    hLocalArc bits middle target) ||
  any 6 (fun p => hToP bits h p && pLocalArc bits p target) ||
  (hToQ bits h && eLocalArc bits 0 target)

def hStrictSecondLocal (bits : Encoding) (h target : Nat) : Bool :=
  decide (target ≠ 2 + h) && !hLocalArc bits h target &&
    hReachesLocal bits h target

def hLocalSecondCount (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 18 (hStrictSecondLocal bits h)

def signatureMeetsRow (bits : Encoding) (p mask : Nat) : Bool :=
  any 3 fun e => maskHas mask e && pToE bits p e

def pOutsideSecondCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  sumCount 7 fun mask =>
    if signatureMeetsRow bits p mask then signatureCount bits mask else 0

def hOutsideSecondCount (bits : Encoding) (h : Nat) : BitVec 8 :=
  if hToQ bits h then outsideForE bits 0 else 0

def retainedReachesLocal (bits : Encoding) (p deleted target : Nat) : Bool :=
  any 6 (fun q => pArc bits p q && pLocalArc bits q target) ||
  any 6 (fun h => pToH bits p h && hLocalArc bits h target) ||
  any 3 (fun e => decide (e ≠ deleted) && pToE bits p e &&
    eLocalArc bits e target)

def deletionLocalTarget (bits : Encoding) (p deleted target : Nat) : Bool :=
  decide (target ≠ 8 + p) &&
    if target = 14 + deleted then retainedReachesLocal bits p deleted target
    else !pLocalArc bits p target && retainedReachesLocal bits p deleted target

def retainedSignatureMeetsRow (bits : Encoding) (p deleted mask : Nat) : Bool :=
  any 3 fun e => decide (e ≠ deleted) && maskHas mask e && pToE bits p e

def deletionCount (bits : Encoding) (p deleted : Nat) : BitVec 8 :=
  count 18 (deletionLocalTarget bits p deleted) +
    sumCount 7 (fun mask => if retainedSignatureMeetsRow bits p deleted mask
      then signatureCount bits mask else 0)

def retainedReachesLocalAny
    (bits : Encoding) (p deleted target : Nat) : Bool :=
  any 6 (fun q => decide (deleted ≠ 8 + q) && pArc bits p q &&
      pLocalArc bits q target) ||
  any 6 (fun h => decide (deleted ≠ 2 + h) && pToH bits p h &&
      hLocalArc bits h target) ||
  any 3 (fun e => decide (deleted ≠ 14 + e) && pToE bits p e &&
      eLocalArc bits e target)

def deletionLocalTargetAny
    (bits : Encoding) (p deleted target : Nat) : Bool :=
  decide (target ≠ 8 + p) &&
    if target = deleted then retainedReachesLocalAny bits p deleted target
    else !pLocalArc bits p target &&
      retainedReachesLocalAny bits p deleted target

def retainedSignatureMeetsRowAny
    (bits : Encoding) (p deleted mask : Nat) : Bool :=
  any 3 fun e => decide (deleted ≠ 14 + e) && maskHas mask e &&
    pToE bits p e

def deletionCountAny (bits : Encoding) (p deleted : Nat) : BitVec 8 :=
  count 18 (deletionLocalTargetAny bits p deleted) +
    sumCount 7 (fun mask => if retainedSignatureMeetsRowAny bits p deleted mask
      then signatureCount bits mask else 0)

def localDeletionCountAny (bits : Encoding) (p deleted : Nat) : BitVec 8 :=
  count 18 (deletionLocalTargetAny bits p deleted)

def retainedOriginalLocalSecondCount
    (bits : Encoding) (p deleted : Nat) : BitVec 8 :=
  count 18 fun target =>
    pStrictSecondLocal bits p target &&
      deletionLocalTarget bits p deleted target

def oriented (bits : Encoding) : Bool :=
  (all 6 fun i => all 6 fun j => decide (i = j) ||
    !(pArc bits i j && pArc bits j i)) &&
  (all 6 fun i => all 6 fun j => decide (i = j) ||
    !(hArc bits i j && hArc bits j i)) &&
  (all 3 fun i => all 3 fun j => decide (i = j) ||
    !(eArc bits i j && eArc bits j i)) &&
  (all 6 fun p => all 6 fun h => !(pToH bits p h && hToP bits h p)) &&
  (all 6 fun p => all 3 fun e => !(pToE bits p e && eToP bits e p)) &&
  (all 6 fun h => !(hToQ bits h && eToH bits 0 h)) &&
  (all 6 fun h => !(hToR bits h && rToH bits h))

def fixedHToZ (bits : Encoding) : Bool :=
  all 3 fun e => all 6 fun h => decide (e = 0) || !bits (162 + h)

def signatureCapacity (bits : Encoding) : Bool :=
  all 7 fun mask => (signatureCount bits mask).ule 8

def totals (bits : Encoding) : Bool :=
  (count 18 (fun n => pToE bits (n / 3) (n % 3)) == 16) &&
  (count 30 (fun n =>
    let p := n / 5
    let j := n % 5
    pArc bits p (if j < p then j else j + 1)) == 15) &&
  (count 36 (fun n => pToH bits (n / 6) (n % 6)) == 17) &&
  ((19 : BitVec 8).ule (count 36 fun n => hToP bits (n / 6) (n % 6)))

/-- Redundant equality consequences of the exact defect-two totals.  Stating
them pointwise avoids asking the SAT backend to rediscover saturation of the
`P×P` and `P×H` capacity rectangles. -/
def saturatedPairRectangles (bits : Encoding) : Bool :=
  (all 6 fun p => all 6 fun q => decide (p = q) ||
    pArc bits p q || pArc bits q p) &&
  (all 6 fun p => all 6 fun h => pToH bits p h || hToP bits h p) &&
  (count 36 (fun n => hToP bits (n / 6) (n % 6)) == 19)

def pConditions (bits : Encoding) : Bool := all 6 fun p =>
  pOut bits p == 8 &&
    (pLocalSecondCount bits p + pOutsideSecondCount bits p).ule 7 &&
    all 18 (fun deleted => !pLocalArc bits p deleted ||
      (7 : BitVec 8).ule (deletionCountAny bits p deleted))

def xConditions (bits : Encoding) : Bool := all 4 fun x =>
  (hLocalSecondCount bits (2 + x) +
    hOutsideSecondCount bits (2 + x)).ult (count 18 fun target =>
      hLocalArc bits (2 + x) target)

/-- Projection of one-arc deletion to the already represented original strict
second neighbors.  The degree-seven reduction says that at most one such
target can disappear. -/
def projectedPConditions (bits : Encoding) : Bool := all 6 fun p =>
  pOut bits p == 8 && (pLocalSecondCount bits p).ule 7 &&
    all 3 (fun e => !pToE bits p e ||
      (pLocalSecondCount bits p).ule
        (retainedOriginalLocalSecondCount bits p e + 1))

def tailLocalPConditions (bits : Encoding) : Bool := all 6 fun p =>
  pOut bits p == 8 && (pLocalSecondCount bits p).ule 7 &&
    all 18 (fun deleted => !pLocalArc bits p deleted ||
      (7 : BitVec 8).ule (localDeletionCountAny bits p deleted))

def eConditions (bits : Encoding) : Bool := all 3 fun e =>
  (8 : BitVec 8).ule (eDegree bits e)

def pRowKey (bits : Encoding) (p : Nat) : BitVec 16 :=
  (pEOut bits p).zeroExtend 16 * 256 +
    (pHOut bits p).zeroExtend 16 * 16 + (pPOut bits p).zeroExtend 16
def orderedP (bits : Encoding) : Bool :=
  all 5 fun p => (pRowKey bits (p + 1)).ule (pRowKey bits p)
def orderedH (bits : Encoding) : Bool :=
  (hPOut bits 1 + bitCount (hToQ bits 1)).ule
      (hPOut bits 0 + bitCount (hToQ bits 0)) &&
    all 3 fun x =>
      (hPOut bits (3 + x) + bitCount (hToQ bits (3 + x))).ule
        (hPOut bits (2 + x) + bitCount (hToQ bits (2 + x)))
def ePIn (bits : Encoding) (e : Nat) : BitVec 8 := count 6 fun p => pToE bits p e
def orderedZ (bits : Encoding) : Bool :=
  (count 18 (eLocalArc bits 2)).ule (count 18 (eLocalArc bits 1))

def everyXReached (bits : Encoding) : Bool := all 4 fun x =>
  any 2 (fun a => hArc bits a (2 + x)) ||
    any 6 (fun p => pToH bits p (2 + x))

def hInternalOut (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 6 (hArc bits h) + bitCount (hToAOne bits h) + bitCount (hToR bits h)

def hBOut (bits : Encoding) (h : Nat) : BitVec 8 :=
  count 6 (hToP bits h) + bitCount (hToQ bits h)

def hConditions (bits : Encoding) : Bool := all 6 fun h =>
  (2 : BitVec 8).ule (hInternalOut bits h) &&
    (8 : BitVec 8).ule (hInternalOut bits h + hBOut bits h) &&
    (!(hInternalOut bits h == 2) || (6 : BitVec 8).ule (hBOut bits h))

def retainedToX (bits : Encoding) (deleted x : Nat) : Bool :=
  any 8 fun u => decide (u ≠ deleted) &&
    if u < 2 then hArc bits u (2 + x) else pToH bits (u - 2) (2 + x)

def retainedToE (bits : Encoding) (deleted e : Nat) : Bool :=
  any 8 fun u => decide (u ≠ deleted) &&
    if u < 2 then decide (e = 0) && hToQ bits u
    else pToE bits (u - 2) e

def retainedToDeleted (bits : Encoding) (deleted : Nat) : Bool :=
  any 8 fun u => decide (u ≠ deleted) &&
    if u < 2 then
      if deleted < 2 then hArc bits u deleted
      else hToP bits u (deleted - 2)
    else
      if deleted < 2 then pToH bits (u - 2) deleted
      else pArc bits (u - 2) (deleted - 2)

def sevenSetExpansion (bits : Encoding) : Bool := all 8 fun deleted =>
  (7 : BitVec 8).ule
    (count 4 (retainedToX bits deleted) + count 3 (retainedToE bits deleted) +
      bitCount (retainedToDeleted bits deleted))

def rInternalOut (bits : Encoding) : BitVec 8 :=
  bitCount (rToAOne bits) + count 6 (rToH bits)
def rBOut (bits : Encoding) : BitVec 8 := count 6 (rToP bits) + bitCount (rToQ bits)
def rConditions (bits : Encoding) : Bool :=
  (2 : BitVec 8).ule (rInternalOut bits) &&
    (8 : BitVec 8).ule (rInternalOut bits + rBOut bits) &&
    (!(rInternalOut bits == 2) || (6 : BitVec 8).ule (rBOut bits))

/-- Root-neighborhood indices are `a1,H(6),R`. -/
def aToB (bits : Encoding) (source target : Nat) : Bool :=
  if source = 0 then decide (target < 6)
  else if source < 7 then
    if target < 6 then hToP bits (source - 1) target else hToQ bits (source - 1)
  else if target < 6 then rToP bits target else rToQ bits

def aToA (bits : Encoding) (source target : Nat) : Bool :=
  if source = 0 then decide (1 ≤ target && target < 3)
  else if source < 7 then
    if target = 0 then hToAOne bits (source - 1)
    else if target < 7 then hArc bits (source - 1) (target - 1)
    else hToR bits (source - 1)
  else if target = 0 then rToAOne bits
  else if target < 7 then rToH bits (target - 1)
  else false

def rootRetainedToB (bits : Encoding) (deleted target : Nat) : Bool :=
  any 8 fun source => decide (source ≠ deleted) && aToB bits source target

def rootRetainedToDeleted (bits : Encoding) (deleted : Nat) : Bool :=
  any 8 fun source => decide (source ≠ deleted) && aToA bits source deleted

def rootSevenExpansion (bits : Encoding) : Bool := all 8 fun deleted =>
  (7 : BitVec 8).ule
    (count 7 (rootRetainedToB bits deleted) +
      bitCount (rootRetainedToDeleted bits deleted))

def core (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
    hToQ bits 0 && hToQ bits 1 && everyXReached bits && hConditions bits &&
    rConditions bits && sevenSetExpansion bits && rootSevenExpansion bits &&
    signatureCapacity bits && (outsideUnionCount bits).ule 7 && totals bits &&
    pConditions bits && xConditions bits && projectedPConditions bits &&
    eConditions bits

def coreOutside (n : Nat) (bits : Encoding) : Bool :=
  core bits && outsideUnionCount bits == n

def coreOutsidePattern (lastE outside : Nat) (bits : Encoding) : Bool :=
  core bits && pEOut bits 5 == lastE && outsideUnionCount bits == outside

def outsideAdjSeven (bits : Encoding) (w e : Nat) : Bool :=
  bits (219 + 3 * w + e)

def outsideCodeSeven (bits : Encoding) (w : Nat) : BitVec 8 :=
  bitCount (outsideAdjSeven bits w 0) +
    2 * bitCount (outsideAdjSeven bits w 1) +
    4 * bitCount (outsideAdjSeven bits w 2)

def orderedOutsideSeven (bits : Encoding) : Bool :=
  all 6 fun w =>
    (outsideCodeSeven bits w).ule (outsideCodeSeven bits (w + 1))

def outsideForESeven (bits : Encoding) (e : Nat) : BitVec 8 :=
  count 7 fun w => outsideAdjSeven bits w e

def eDegreeSeven (bits : Encoding) (e : Nat) : BitVec 8 :=
  count 18 (eLocalArc bits e) + outsideForESeven bits e

def pOutsideSecondSeven (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun w => any 3 fun e => pToE bits p e && outsideAdjSeven bits w e

def hOutsideSecondSeven (bits : Encoding) (h : Nat) : BitVec 8 :=
  if hToQ bits h then count 7 fun w => outsideAdjSeven bits w 0 else 0

def retainedOutsideSeven (bits : Encoding) (p deleted w : Nat) : Bool :=
  any 3 fun e => decide (deleted ≠ 14 + e) && pToE bits p e &&
    outsideAdjSeven bits w e

def deletionCountAnySeven (bits : Encoding) (p deleted : Nat) : BitVec 8 :=
  count 18 (deletionLocalTargetAny bits p deleted) +
    count 7 (retainedOutsideSeven bits p deleted)

def retainedOutsideESeven (bits : Encoding) (p deleted w : Nat) : Bool :=
  any 3 fun e => decide (e ≠ deleted) && pToE bits p e &&
    outsideAdjSeven bits w e

def deletionCountESeven (bits : Encoding) (p deleted : Nat) : BitVec 8 :=
  count 18 (deletionLocalTarget bits p deleted) +
    count 7 (retainedOutsideESeven bits p deleted)

def pConditionsSeven (bits : Encoding) : Bool := all 6 fun p =>
  pOut bits p == 8 &&
    (pLocalSecondCount bits p + pOutsideSecondSeven bits p).ule 7 &&
    all 18 (fun deleted => !pLocalArc bits p deleted ||
      (7 : BitVec 8).ule (deletionCountAnySeven bits p deleted))

def auxiliaryDeletionPConditionsSeven (bits : Encoding) : Bool :=
  all 6 fun p => pOut bits p == 8 && all 3 fun deleted =>
    !pToE bits p deleted ||
      (7 : BitVec 8).ule (deletionCountESeven bits p deleted)

def xConditionsSeven (bits : Encoding) : Bool := all 4 fun x =>
  (hLocalSecondCount bits (2 + x) +
    hOutsideSecondSeven bits (2 + x)).ult (count 18 fun target =>
      hLocalArc bits (2 + x) target)

def eConditionsSeven (bits : Encoding) : Bool := all 3 fun e =>
  (8 : BitVec 8).ule (eDegreeSeven bits e)

def coreSeven (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
    hToQ bits 0 && hToQ bits 1 && everyXReached bits && hConditions bits &&
    rConditions bits && orderedOutsideSeven bits && totals bits &&
    saturatedPairRectangles bits && auxiliaryDeletionPConditionsSeven bits &&
    xConditionsSeven bits && eConditionsSeven bits

def coreSevenPattern (lastE : Nat) (bits : Encoding) : Bool :=
  coreSeven bits && pEOut bits 5 == lastE

/-- Binary code of the three auxiliary incidences in a `P` row.  In the
two-defect leaf, symmetry and `orderedZ` leave only seven pairs of row codes. -/
def pECode (bits : Encoding) (p : Nat) : BitVec 8 :=
  bitCount (pToE bits p 0) + 2 * bitCount (pToE bits p 1) +
    4 * bitCount (pToE bits p 2)

def coreSevenLeaf (lastE code4 code5 : Nat) (bits : Encoding) : Bool :=
  coreSevenPattern lastE bits && (all 4 fun p => pECode bits p == 7) &&
    pECode bits 4 == code4 && pECode bits 5 == code5

def projectedCore (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
    hToQ bits 0 && hToQ bits 1 && everyXReached bits && hConditions bits &&
    rConditions bits && sevenSetExpansion bits && rootSevenExpansion bits &&
    totals bits && projectedPConditions bits

def localCore (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
    hToQ bits 0 && hToQ bits 1 && everyXReached bits && hConditions bits &&
    rConditions bits && sevenSetExpansion bits && rootSevenExpansion bits &&
    totals bits && tailLocalPConditions bits

def minimalLocalCore (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
    totals bits && tailLocalPConditions bits

def minimalLocalCorePattern (lastE : Nat) (bits : Encoding) : Bool :=
  minimalLocalCore bits && pEOut bits 5 == lastE

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
