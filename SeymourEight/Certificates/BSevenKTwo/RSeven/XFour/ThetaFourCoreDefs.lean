import Std.Tactic.BVDecide

/-!
# Compressed finite core for the hardest `(7,2)`, `r=7`, `x=4` shard

This sound relaxation retains only `A`, `P`, the `P→Z` incidences, and the
anonymous outside-terminal signature counts needed by `P`.  Fixed and
complementary arcs are definitionally reconstructed, and all reachability is
computed rather than stored.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ThetaFourCore

abbrev Encoding := BitVec 222

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def sumCount : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumCount n p + p n

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

/-! `A={a1,A1[2],X[4],R}` has indices `0,...,7`; `P` has indices
`8,...,14`; `Z` has indices `15,...,18`. -/

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (8 * i + j)

def upperIndex (i j : Nat) : Nat :=
  i * (13 - i) / 2 + (j - i - 1)

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  if i = j then false
  else if i < j then bits.getLsbD (64 + upperIndex i j)
  else !bits.getLsbD (64 + upperIndex j i)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (85 + 6 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  !pToH bits p h

def pToZ (bits : Encoding) (p z : Nat) : Bool :=
  bits.getLsbD (127 + 4 * p + z)

def rToP (bits : Encoding) (p : Nat) : Bool :=
  bits.getLsbD (155 + p)

def signatureCount (bits : Encoding) (mask : Nat) : BitVec 8 :=
  (bits.extractLsb' (162 + 4 * mask) 4).zeroExtend 8

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true
  else if a < 7 then hToP bits (a - 1) p
  else rToP bits p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if 0 < a && a < 7 then pToH bits p (a - 1) else false

def coreArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 19 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def directCount (bits : Encoding) (u : Nat) : BitVec 8 :=
  count 19 (coreArc bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def aPOut (bits : Encoding) (a : Nat) : BitVec 8 :=
  count 7 (aToP bits a)

def pOut (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 (pArc bits p)

def pHOut (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 (pToH bits p)

def pZOut (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 4 (pToZ bits p)

def reachesLocal (bits : Encoding) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc bits source middle && coreArc bits middle target

def strictSecondLocal (bits : Encoding) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachesLocal bits source target

def localSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 19 (strictSecondLocal bits source)

def signatureMeetsPZ (bits : Encoding) (p mask : Nat) : Bool :=
  any 4 fun z =>
    decide (((mask + 1) / 2 ^ z) % 2 = 1) && pToZ bits p z

def outsideSecondCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  sumCount 15 fun mask =>
    if signatureMeetsPZ bits p mask then signatureCount bits mask else 0

def aNonSeymour (bits : Encoding) (a : Nat) : Bool :=
  (localSecondCount bits a).ult (directCount bits a)

def pNonSeymour (bits : Encoding) (p : Nat) : Bool :=
  (localSecondCount bits (8 + p) + outsideSecondCount bits p).ult
    (directCount bits (8 + p))

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)

def fixedA (bits : Encoding) : Bool :=
  aArc bits 0 1 && aArc bits 0 2 &&
  all 5 (fun i => !aArc bits 0 (3 + i)) &&
  !aArc bits 1 7 && !aArc bits 2 7

def everyXReached (bits : Encoding) : Bool :=
  all 4 fun x =>
    any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
      any 7 (fun p => pToH bits p (2 + x))

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a =>
    (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (7 : BitVec 8).ule (aPOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aPOut bits a)

def pDegreeEight (bits : Encoding) : Bool :=
  all 7 fun p => pOut bits p + pHOut bits p + pZOut bits p == 8

def profile (bits : Encoding) : Bool :=
  pZOut bits 0 == 2 && pZOut bits 1 == 3 && pZOut bits 2 == 3 &&
  pZOut bits 3 == 3 && pZOut bits 4 == 3 && pZOut bits 5 == 4 &&
  pZOut bits 6 == 4

def signatureCapacity (bits : Encoding) : Bool :=
  all 15 (fun mask => (signatureCount bits mask).ule 8) &&
  all 4 fun z =>
    (sumCount 15 fun mask =>
      if ((mask + 1) / 2 ^ z) % 2 = 1 then signatureCount bits mask else 0).ule 8

def hMissingPairs (bits : Encoding) : BitVec 8 :=
  count 36 fun q =>
    let i := q / 6
    let j := q % 6
    decide (i < j) && !aArc bits (1 + i) (1 + j) &&
      !aArc bits (1 + j) (1 + i)

def xEligible (bits : Encoding) (x : Nat) : Bool :=
  let source := 3 + x
  directCount bits source == 8 && aArc bits source 0 && aArc bits source 7

def xReach (bits : Encoding) (x target : Nat) : Bool :=
  let source := 3 + x
  let destination := 3 + target
  aArc bits source destination || any 6 (fun middle =>
    decide (1 + middle ≠ source) && decide (1 + middle ≠ destination) &&
      aArc bits source (1 + middle) && aArc bits (1 + middle) destination)

def eligibleType (bits : Encoding) (x : Nat) : Bool :=
  let b := aPOut bits (3 + x)
  let r := count 4 fun target => decide (target ≠ x) && xReach bits x target
  (b == 1) || ((b == 2) && r.ule 3) || ((b == 3) && r.ule 2) ||
    ((4 : BitVec 8).ule b && r.ule 1)

def retainedAfterAOneDeletion (bits : Encoding) (x vertex : Nat) : Bool :=
  decide (vertex ≠ 0) && coreArc bits (3 + x) vertex

def xDeletionExpands (bits : Encoding) (x : Nat) : Bool :=
  let retained := retainedAfterAOneDeletion bits x
  let reached := fun target =>
    decide (target ≠ 3 + x) && !retained target &&
      any 15 (fun middle => retained middle && coreArc bits middle target)
  (7 : BitVec 8).ule (count 19 reached)

def hTargetedDeletion (bits : Encoding) : Bool :=
  (hMissingPairs bits).ule (count 4 (xEligible bits)) &&
  all 4 fun x => !xEligible bits x ||
    (eligibleType bits x && xDeletionExpands bits x)

/-- A compact sound relaxation of an external-profile shard in the `theta=4` leaf. -/
def hardestProfileCore (bits : Encoding) : Bool :=
  orientedA bits && fixedA bits && everyXReached bits &&
  (3 : BitVec 8).ule (count 8 fun q =>
    let a := q / 4
    let x := q % 4
    aArc bits (1 + a) (3 + x)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour bits) &&
  pDegreeEight bits && (sumCount 7 (pHOut bits) == 13) && profile bits &&
  signatureCapacity bits && all 7 (pNonSeymour bits) && hTargetedDeletion bits

/-- The `eta=0` specialization of `hardestProfileCore`. -/
def hardestProfileEtaZeroCore (bits : Encoding) : Bool :=
  hardestProfileCore bits && hMissingPairs bits == 0

/-- One of the sixteen exhaustive incidence patterns from the first retained
`P` vertex to the four vertices of `Z`.  Splitting on this nibble gives
independent certificate checkpoints without weakening the eta-zero target. -/
def pZPattern (bits : Encoding) (p : Nat) (b0 b1 b2 b3 : Bool) : Bool :=
  (pToZ bits p 0 == b0) && (pToZ bits p 1 == b1) &&
  (pToZ bits p 2 == b2) && (pToZ bits p 3 == b3)

/-- Canonical encoding of the hardest retained-row orbit.  The first row hits
`z₂,z₃`; the second contains those two and additionally hits `z₁`; the third
and fourth both omit the same shared vertex `z₂`. -/
def hardestProfileEtaZeroRepeatedSharedOmissionCore (bits : Encoding) : Bool :=
  hardestProfileEtaZeroCore bits && pZPattern bits 0 false false true true &&
    pZPattern bits 1 false true true true &&
    pZPattern bits 2 true true false true &&
    pZPattern bits 3 true true false true

/-- The complementary canonical mixed-omission core in which the omission of
the third displayed row is unique among the remaining three-neighbor rows. -/
def mixedOmissionUniqueInnerOmissionCore (bits : Encoding) : Bool :=
  hardestProfileEtaZeroCore bits && pZPattern bits 0 false false true true &&
    pZPattern bits 1 false true true true &&
    pZPattern bits 2 true true false true &&
    pToZ bits 3 2 && pToZ bits 4 2

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ThetaFourCore
