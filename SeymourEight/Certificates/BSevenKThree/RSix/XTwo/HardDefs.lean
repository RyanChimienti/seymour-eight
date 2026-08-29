import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CoreDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.CoreDefs

/-!
# Projected hard core for the reached five-target row

This reuses the established `A/P/Q/Z` primitives from the `x = 4` family,
but counts only the five genuine vertices of `H = A₁ ∪ X`.  The two vertices
of `R` occupy A-indices 6 and 7 and are forced unreachable from `A₁ ∪ P`.
-/

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

abbrev easyCore := SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.core

def pHOut (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  count 5 fun h ↦ pToA arc p (1 + h)

def hPOut (arc : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 6 fun p ↦ aToP arc (1 + h) p

def pDegree (arc pToZ : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  pOut arc p + pHOut arc p + pAuxOut 1 5 arc pToZ p

def noToR (arc : Nat → Nat → Bool) : Bool :=
  (all 3 fun a ↦ all 2 fun r ↦ !aArc arc (1 + a) (6 + r)) &&
    (all 6 fun p ↦ all 2 fun r ↦ !pToA arc p (6 + r))

def everyXReached (arc : Nat → Nat → Bool) : Bool :=
  all 2 fun x ↦ any 3 (fun a ↦ aArc arc (1 + a) (4 + x)) ||
    any 6 (fun p ↦ pToA arc p (4 + x))

def pConditions (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 6 fun p ↦ (8 : BitVec 8).ule (pDegree arc pToZ p)

def pNonSeymour (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 6 fun p ↦
    (projectedSecondCount 5 arc pToZ (8 + p)).ult (pDegree arc pToZ p)

def totalPToH (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 6 (pHOut arc)

def totalHToP (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 5 (hPOut arc)

def totalHToQ (arc : Nat → Nat → Bool) : BitVec 8 :=
  count 5 fun h ↦ aToQ arc (1 + h)

def hQDefect (arc : Nat → Nat → Bool) : BitVec 8 :=
  5 - totalHToQ arc

def alpha (arc : Nat → Nat → Bool) : BitVec 8 :=
  8 - totalPToH arc

def externalMissing (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  36 - totalPToAux 1 5 arc pToZ

def capacityDefect (arc pToZ : Nat → Nat → Bool) : BitVec 8 :=
  externalMissing arc pToZ + alpha arc + internalMissing arc

def degreeConditions (arc : Nat → Nat → Bool) : Bool :=
  (22 + hQDefect arc).ule (totalHToP arc) &&
    (totalPToH arc).ule 8

def effectiveAt (s v1 v2 v3 v4 v5 v6 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else if s == 4 then v4 else if s == 5 then v5
  else v6

def effectiveTable (m s : BitVec 8) : BitVec 8 :=
  if m == 0 then effectiveAt s 13 10 8 7 7 6
  else if m == 1 then effectiveAt s 12 9 8 7 6 6
  else if m == 2 then effectiveAt s 11 9 8 7 6 6
  else if m == 3 then effectiveAt s 10 8 7 7 6 5
  else if m == 4 then effectiveAt s 9 8 7 6 6 5
  else if m == 5 then effectiveAt s 8 7 7 6 6 5
  else if m == 6 then effectiveAt s 7 7 6 6 5 5
  else if m == 7 then effectiveAt s 6 6 6 6 5 5
  else if m == 8 then effectiveAt s 5 6 6 5 5 5
  else if m == 9 then effectiveAt s 4 5 5 5 5 4
  else if m == 10 then effectiveAt s 3 5 5 5 5 4
  else effectiveAt s 2 4 5 5 4 4

def pEffective (arc pToZ : Nat → Nat → Bool) (p : Nat) : Bool :=
  (pSecondPCount arc p +
      effectiveTable (externalMissing arc pToZ) (pAuxOut 1 5 arc pToZ p) + 1).ule
    (pOut arc p + 2 * pHOut arc p + pAuxOut 1 5 arc pToZ p)

def inducedWitness (arc : Nat → Nat → Bool)
    (member : Nat → Bool) : Bool :=
  any 14 fun source ↦ member source &&
    (count 14 fun target ↦ member target &&
      strictSecondLocal arc source target).ule
      (count 14 fun target ↦ member target && arc source target)

def inducedConditions (arc : Nat → Nat → Bool) : Bool :=
  inducedWitness arc (fun v ↦ decide (8 ≤ v)) &&
  inducedWitness arc (fun v ↦ decide (1 ≤ v && v ≤ 3 || 8 ≤ v)) &&
  inducedWitness arc (fun v ↦ decide (1 ≤ v && v ≤ 5 || 8 ≤ v)) &&
  inducedWitness arc (fun _ ↦ true)

def pRowKey (arc pToZ : Nat → Nat → Bool) (p : Nat) : BitVec 32 :=
  (pDegree arc pToZ p).zeroExtend 32 * 65536 +
    (pZOut 5 pToZ p).zeroExtend 32 * 4096 +
    (bitCount (pToQ arc p)).zeroExtend 32 * 2048 +
    (count 3 fun a ↦ pToA arc p (1 + a)).zeroExtend 32 * 256 +
    (count 2 fun x ↦ pToA arc p (4 + x)).zeroExtend 32 * 16 +
    (pOut arc p).zeroExtend 32

def orderedP (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 5 fun p ↦ (pRowKey arc pToZ (p + 1)).ule (pRowKey arc pToZ p)

def orderedAClasses (arc : Nat → Nat → Bool) : Bool :=
  (all 2 fun a ↦ (aBOut arc (2 + a)).ule (aBOut arc (1 + a))) &&
    (aBOut arc 5).ule (aBOut arc 4)

def orderedZ (pToZ : Nat → Nat → Bool) : Bool :=
  all 4 fun z ↦ (zIn pToZ (z + 1)).ule (zIn pToZ z)

def qTrimmed (arc : Nat → Nat → Bool)
    (qToZ qOutside : Nat → Bool) : Bool :=
  !arc 14 14 &&
    (all 14 fun u ↦ !(arc u 14 && arc 14 u)) &&
    count 15 (arc 14) + count 5 qToZ + count 8 qOutside == 8

def extendedLocalSecond (arc pToZ : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  projectedSecond 5 arc pToZ source target ||
    (decide (target ≠ source) && !arc source target &&
      arc source 14 && arc 14 target)

def extendedZSecond (arc pToZ : Nat → Nat → Bool)
    (qToZ : Nat → Bool) (source z : Nat) : Bool :=
  projectedSecond 5 arc pToZ source (15 + z) ||
    (!coreArc 5 arc pToZ source (15 + z) && arc source 14 && qToZ z)

def extendedOutsideSecond (arc : Nat → Nat → Bool)
    (qOutside : Nat → Bool) (source outside : Nat) : Bool :=
  arc source 14 && qOutside outside

def selectedSecondCount (arc pToZ : Nat → Nat → Bool)
    (qToZ qOutside : Nat → Bool) (source : Nat) : BitVec 8 :=
  count 15 (extendedLocalSecond arc pToZ source) +
    count 5 (extendedZSecond arc pToZ qToZ source) +
    count 8 (extendedOutsideSecond arc qOutside source)

def selectedNonSeymour (arc pToZ : Nat → Nat → Bool)
    (qToZ qOutside : Nat → Bool) : Bool :=
  (all 8 fun a ↦ (selectedSecondCount arc pToZ qToZ qOutside a).ult
    (aDegree arc a)) &&
  (all 6 fun p ↦
    (selectedSecondCount arc pToZ qToZ qOutside (8 + p)).ult
      (pDegree arc pToZ p))

def hallZReached (arc pToZ : Nat → Nat → Bool)
    (qToZ : Nat → Bool) (source z : Nat) : Bool :=
  (any 6 fun p ↦ aToP arc source p && pToZ p z) ||
    (aToQ arc source && qToZ z)

def hallCount (arc pToZ : Nat → Nat → Bool)
    (qToZ qOutside : Nat → Bool) (source : Nat) : BitVec 8 :=
  count 5 (hallZReached arc pToZ qToZ source) +
    if aToQ arc source then count 8 qOutside else 0

def hallConditions (arc pToZ : Nat → Nat → Bool)
    (qToZ qOutside : Nat → Bool) : Bool :=
  all 8 fun source ↦ !innerSeymour arc source ||
    (hallCount arc pToZ qToZ qOutside source).ult (aBOut arc source)

/-! The hard row must retain paths through all six auxiliary vertices
`Q ∪ Z`.  The eight anonymous columns below form the canonical nested
family with the same six marginal sizes.  Its union for any selected family
has the smallest possible cardinality, so it is a sound graph lower bound. -/

def auxIncoming (arc pToZ : Nat → Nat → Bool)
    (source aux : Nat) : Bool :=
  if source < 8 then
    if aux = 0 then aToQ arc source else false
  else if source < 14 then
    if aux = 0 then pToQ arc (source - 8)
    else pToZ (source - 8) (aux - 1)
  else false

def auxNamedOut (auxArc : Nat → Nat → Bool) (aux : Nat) : BitVec 8 :=
  count 20 (auxArc aux)

def auxOutsideNeed (auxArc : Nat → Nat → Bool) (aux : Nat) : BitVec 8 :=
  8 - auxNamedOut auxArc aux

def auxOutside (auxArc : Nat → Nat → Bool)
    (aux slot : Nat) : Bool :=
  (BitVec.ofNat 8 (slot + 1)).ule (auxOutsideNeed auxArc aux)

def auxiliaryExact (auxArc : Nat → Nat → Bool) : Bool :=
  all 6 fun aux ↦ (auxNamedOut auxArc aux).ule 8

def auxiliaryOriented (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  (all 6 fun aux ↦ all 14 fun source ↦
    !(auxIncoming arc pToZ source aux && auxArc aux source)) &&
  (all 6 fun aux ↦ !auxArc aux (14 + aux) && all 6 fun other ↦
    decide (aux = other) ||
      !(auxArc aux (14 + other) && auxArc other (14 + aux)))

def namedDirect (arc pToZ : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  if source < 14 then coreArc 5 arc pToZ source target else false

def namedArc (arc pToZ auxArc : Nat → Nat → Bool)
    (middle target : Nat) : Bool :=
  if middle < 14 then coreArc 5 arc pToZ middle target
  else if middle < 20 then auxArc (middle - 14) target
  else false

def fullReachesNamed (arc pToZ auxArc : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  any 20 fun middle ↦ decide (middle ≠ source) && decide (middle ≠ target) &&
    namedDirect arc pToZ source middle && namedArc arc pToZ auxArc middle target

def fullSecondNamed (arc pToZ auxArc : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  decide (target ≠ source) && !namedDirect arc pToZ source target &&
    fullReachesNamed arc pToZ auxArc source target

def fullOutsideSecond (arc pToZ auxArc : Nat → Nat → Bool)
    (source slot : Nat) : Bool :=
  any 6 fun aux ↦ auxIncoming arc pToZ source aux && auxOutside auxArc aux slot

def fullSecondCount (arc pToZ auxArc : Nat → Nat → Bool)
    (source : Nat) : BitVec 8 :=
  count 20 (fullSecondNamed arc pToZ auxArc source) +
    count 8 (fullOutsideSecond arc pToZ auxArc source)

def fullNonSeymour (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  (all 8 fun a ↦ (fullSecondCount arc pToZ auxArc a).ult (aDegree arc a)) &&
  (all 6 fun p ↦
    (fullSecondCount arc pToZ auxArc (8 + p)).ult (pDegree arc pToZ p))

def fullHallZReached (arc pToZ auxArc : Nat → Nat → Bool)
    (source z : Nat) : Bool :=
  (any 6 fun p ↦ aToP arc source p && pToZ p z) ||
    (aToQ arc source && auxArc 0 (15 + z))

def fullHallCount (arc pToZ auxArc : Nat → Nat → Bool)
    (source : Nat) : BitVec 8 :=
  count 5 (fullHallZReached arc pToZ auxArc source) +
    count 8 fun slot ↦ aToQ arc source && auxOutside auxArc 0 slot

def fullHallConditions (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  all 8 fun source ↦ !innerSeymour arc source ||
    (fullHallCount arc pToZ auxArc source).ult (aBOut arc source)

def aOneInner (arc : Nat → Nat → Bool) : Bool :=
  all 3 fun i ↦ degreeThreeInner arc (1 + i)

def commonCore (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  easyCore 5 true arc pToZ && aOneInner arc && degreeConditions arc &&
    (capacityDefect arc pToZ).ule 11 &&
    sharpKing arc && (all 6 fun p ↦ pEffective arc pToZ p) &&
    auxiliaryExact auxArc &&
    auxiliaryOriented arc pToZ auxArc && fullNonSeymour arc pToZ auxArc &&
    fullHallConditions arc pToZ auxArc

def exactLeaf (m : Nat) (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  commonCore arc pToZ auxArc &&
    externalMissing arc pToZ == BitVec.ofNat 8 m

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore
