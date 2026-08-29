import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CoreDefs

/-!
# Exact auxiliary-neighborhood projection for the hard rows

For `y = 1`, `z = 3`, the four auxiliary vertices are the unique member of
`Q` followed by the three vertices of `Z`.  We retain eight outneighbors of
each auxiliary vertex.  Targets in `{s} ∪ A ∪ P ∪ Q ∪ Z` have nineteen
named columns; the union of all other retained targets has at most 32 padded
columns.  This is enough to state one-arc deletion exactly without assuming
that paths through an auxiliary vertex stay in the smaller core.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryCore

open Shared.FiniteCore
open Core

def auxNamedOut (auxArc : Nat → Nat → Bool) (i : Nat) : BitVec 8 :=
  count 19 (auxArc i)

def maskHas (mask i : Nat) : Bool :=
  match mask with
  | 0 => decide (i = 0)
  | 1 => decide (i = 1)
  | 2 => decide (i = 0 ∨ i = 1)
  | 3 => decide (i = 2)
  | 4 => decide (i = 0 ∨ i = 2)
  | 5 => decide (i = 1 ∨ i = 2)
  | 6 => decide (i = 0 ∨ i = 1 ∨ i = 2)
  | 7 => decide (i = 3)
  | 8 => decide (i = 0 ∨ i = 3)
  | 9 => decide (i = 1 ∨ i = 3)
  | 10 => decide (i = 0 ∨ i = 1 ∨ i = 3)
  | 11 => decide (i = 2 ∨ i = 3)
  | 12 => decide (i = 0 ∨ i = 2 ∨ i = 3)
  | 13 => decide (i = 1 ∨ i = 2 ∨ i = 3)
  | 14 => decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
  | _ => false

def signatureValue (signature : Nat → BitVec 4) (mask : Nat) : BitVec 8 :=
  (signature mask).zeroExtend 8

def auxOutsideOut (signature : Nat → BitVec 4) (i : Nat) : BitVec 8 :=
  sumCount 15 fun mask =>
    if maskHas mask i then signatureValue signature mask else 0

def auxiliaryExact (auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) : Bool :=
  all 4 fun i => auxNamedOut auxArc i + auxOutsideOut signature i == 8

/-!
The graph bridge does not need to reproduce the actual intersections of the
four anonymous outside neighborhoods.  It uses the canonical nested family
with the same four marginal sizes: slot `t` belongs to auxiliary `i` exactly
when `t` is below the number of unnamed retained outneighbors of `i`.
-/

def canonicalOutsideNeed (auxArc : Nat → Nat → Bool) (i : Nat) : BitVec 8 :=
  8 - auxNamedOut auxArc i

def bitCount4 (b : Bool) : BitVec 4 := if b then 1 else 0

def count4 : Nat → (Nat → Bool) → BitVec 4
  | 0, _ => 0
  | n + 1, p => count4 n p + bitCount4 (p n)

def canonicalSlotHasMask (auxArc : Nat → Nat → Bool)
    (slot mask : Nat) : Bool :=
  all 4 fun i =>
    (BitVec.ofNat 8 (slot + 1)).ule (canonicalOutsideNeed auxArc i) ==
      maskHas mask i

def canonicalSignature (auxArc : Nat → Nat → Bool) (mask : Nat) : BitVec 4 :=
  count4 8 fun slot => canonicalSlotHasMask auxArc slot mask

def incomingToAux (arc pToZ : Nat → Nat → Bool)
    (source i : Nat) : Bool :=
  if source < 8 then
    if i = 0 then aToQ arc source else false
  else if source < 14 then
    if i = 0 then pToQ arc (source - 8) else pToZ (source - 8) (i - 1)
  else false

def auxiliaryOriented (arc pToZ auxArc : Nat → Nat → Bool) : Bool :=
  (all 4 fun i => all 14 fun source =>
    !(incomingToAux arc pToZ source i && auxArc i source)) &&
  (all 4 fun i => all 4 fun j =>
    !(auxArc i (14 + j) && auxArc j (14 + i)))

def hallZReached (arc pToZ auxArc : Nat → Nat → Bool)
    (source z : Nat) : Bool :=
  (any 6 fun p => aToP arc source p && pToZ p z) ||
    (aToQ arc source && auxArc 0 (15 + z))

def hallCount (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4)
    (source : Nat) : BitVec 8 :=
  count 3 (hallZReached arc pToZ auxArc source) +
    if aToQ arc source then auxOutsideOut signature 0 else 0

def hallConditions (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) : Bool :=
  all 8 fun source => !innerSeymour arc source ||
    (hallCount arc pToZ auxArc signature source).ult (aBOut arc source)

def pDirect (arc pToZ : Nat → Nat → Bool) (p target : Nat) : Bool :=
  if target < 18 then coreArc 3 arc pToZ (8 + p) target else false

def sourceDirect (arc pToZ : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  if target < 18 then coreArc 3 arc pToZ source target else false

def namedArc (arc pToZ auxArc : Nat → Nat → Bool)
    (middle target : Nat) : Bool :=
  if middle < 14 then
    if target < 18 then coreArc 3 arc pToZ middle target else false
  else if middle < 18 then auxArc (middle - 14) target
  else false

def fullReachesNamed (arc pToZ auxArc : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  any 18 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    sourceDirect arc pToZ source middle &&
    namedArc arc pToZ auxArc middle target

def fullSecondNamed (arc pToZ auxArc : Nat → Nat → Bool)
    (source target : Nat) : Bool :=
  decide (target ≠ source) && !sourceDirect arc pToZ source target &&
    fullReachesNamed arc pToZ auxArc source target

def sourceHitsMask (arc pToZ : Nat → Nat → Bool)
    (source mask : Nat) : Bool :=
  any 4 fun i => sourceDirect arc pToZ source (14 + i) && maskHas mask i

def fullOutsideCount (arc pToZ : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) (source : Nat) : BitVec 8 :=
  sumCount 15 fun mask =>
    if sourceHitsMask arc pToZ source mask then signatureValue signature mask else 0

def fullSecondCount (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4)
    (source : Nat) : BitVec 8 :=
  count 19 (fullSecondNamed arc pToZ auxArc source) +
    fullOutsideCount arc pToZ signature source

def fullNonSeymour (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) : Bool :=
  all 7 fun h => (fullSecondCount arc pToZ auxArc signature (1 + h)).ult
    (aDegree arc (1 + h))

def deletionReachesNamed (arc pToZ auxArc : Nat → Nat → Bool)
    (p deleted target : Nat) : Bool :=
  any 18 fun middle => decide (middle ≠ 8 + p) &&
    decide (middle ≠ deleted) && decide (middle ≠ target) &&
    pDirect arc pToZ p middle && namedArc arc pToZ auxArc middle target

def deletionRetainsNamed (arc pToZ auxArc : Nat → Nat → Bool)
    (p deleted target : Nat) : Bool :=
  fullSecondNamed arc pToZ auxArc (8 + p) target &&
    deletionReachesNamed arc pToZ auxArc p deleted target

def deletionHitsMask (arc pToZ : Nat → Nat → Bool)
    (p deleted mask : Nat) : Bool :=
  any 4 fun i => decide (14 + i ≠ deleted) &&
    pDirect arc pToZ p (14 + i) && maskHas mask i

def deletionRetainedOutsideCount (arc pToZ : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) (p deleted : Nat) : BitVec 8 :=
  sumCount 15 fun mask =>
    if sourceHitsMask arc pToZ (8 + p) mask &&
        deletionHitsMask arc pToZ p deleted mask then
      signatureValue signature mask else 0

def deletionRetainedCount (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4)
    (p deleted : Nat) : BitVec 8 :=
  count 19 (deletionRetainsNamed arc pToZ auxArc p deleted) +
    deletionRetainedOutsideCount arc pToZ signature p deleted

def deletionExpands (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4)
    (p deleted : Nat) : Bool :=
  !pDirect arc pToZ p deleted ||
    (fullSecondCount arc pToZ auxArc signature (8 + p)).ule
      (deletionRetainedCount arc pToZ auxArc signature p deleted + 1)

def externalDeletionConditions (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) : Bool :=
  all 6 fun p => !(pDegree 1 3 arc pToZ p == 8) || all 4 fun deletedAux =>
    deletionExpands arc pToZ auxArc signature p (14 + deletedAux)

def fullDeletionAt (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4)
    (p : Nat) : Bool :=
  (all 7 fun h => deletionExpands arc pToZ auxArc signature p (1 + h)) &&
    (all 6 fun q => deletionExpands arc pToZ auxArc signature p (8 + q))

def auxiliaryCore (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) : Bool :=
  auxiliaryOriented arc pToZ auxArc && auxiliaryExact auxArc signature &&
    hallConditions arc pToZ auxArc signature &&
    fullNonSeymour arc pToZ auxArc signature

def hardAuxCore (arc pToZ auxArc : Nat → Nat → Bool)
    (signature : Nat → BitVec 4) : Bool :=
  hardCore arc pToZ && auxiliaryCore arc pToZ auxArc signature

def auxiliaryDefectLeaf (m delta d : Nat)
    (arc pToZ auxArc : Nat → Nat → Bool) (signature : Nat → BitVec 4) : Bool :=
  commonCore 1 3 arc pToZ && auxiliaryCore arc pToZ auxArc signature &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc + internalMissing arc == BitVec.ofNat 8 d &&
    fullDeletionAt arc pToZ auxArc signature (6 - (m + 2 * delta + d))

def auxiliaryFineLeaf (m delta alphaValue betaValue : Nat)
    (arc pToZ auxArc : Nat → Nat → Bool) (signature : Nat → BitVec 4) : Bool :=
  commonCore 1 3 arc pToZ && auxiliaryCore arc pToZ auxArc signature &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc == BitVec.ofNat 8 alphaValue &&
    internalMissing arc == BitVec.ofNat 8 betaValue &&
    fullDeletionAt arc pToZ auxArc signature
      (6 - (m + 2 * delta + alphaValue + betaValue))

def auxiliaryCapacityLeaf (m capacity : Nat)
    (arc pToZ auxArc : Nat → Nat → Bool) (signature : Nat → BitVec 4) : Bool :=
  commonCore 1 3 arc pToZ && auxiliaryCore arc pToZ auxArc signature &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    fullDeletionAt arc pToZ auxArc signature (6 - capacity)

def auxiliaryCapacityOnlyLeaf (capacity : Nat)
    (arc pToZ auxArc : Nat → Nat → Bool) (signature : Nat → BitVec 4) : Bool :=
  commonCore 1 3 arc pToZ && auxiliaryCore arc pToZ auxArc signature &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    fullDeletionAt arc pToZ auxArc signature (6 - capacity)

def auxiliaryAllCapacities
    (arc pToZ auxArc : Nat → Nat → Bool) (signature : Nat → BitVec 4) : Bool :=
  hardAuxCore arc pToZ auxArc signature &&
    fullDeletionAt arc pToZ auxArc signature
      (6 - (capacityDefect arc pToZ).toNat)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryCore
