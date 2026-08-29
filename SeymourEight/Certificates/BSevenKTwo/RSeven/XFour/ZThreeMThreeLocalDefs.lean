import Std.Tactic.BVDecide

/-!
# Local equality core for the three-`Z`, defect-three leaf

All aggregate bounds are tight in this leaf.  Thus `P` and `H` are
tournaments, every `P` and `H` vertex has degree eight, and every `P`--`H`
pair is oriented.  Keeping the local `A ∪ P ∪ Z` graph also makes the
one-arc deletion expansion at each `X` vertex directly checkable.  No
external-mask case split is used: vertex relabeling is left entirely inside
the single certificate.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeLocalCore

abbrev Encoding := BitVec 155

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

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
  bits.getLsbD (127 + 3 * p + z)

def rToP (bits : Encoding) (p : Nat) : Bool :=
  bits.getLsbD (148 + p)

def aToP (bits : Encoding) (a p : Nat) : Bool :=
  if a = 0 then true
  else if a < 7 then hToP bits (a - 1) p
  else rToP bits p

def pToA (bits : Encoding) (p a : Nat) : Bool :=
  if 0 < a && a < 7 then pToH bits p (a - 1) else false

/- `A={a1,A1[2],X[4],R}` is `0,...,7`, `P` is `8,...,14`, and
`Z` is `15,...,17`. -/
def coreArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 18 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def directCount (bits : Encoding) (u : Nat) : BitVec 8 :=
  count 18 (coreArc bits u)

def aOut (bits : Encoding) (a : Nat) : BitVec 8 := count 8 (aArc bits a)
def aPOut (bits : Encoding) (a : Nat) : BitVec 8 := count 7 (aToP bits a)
def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pToH bits p)
def pZOut (bits : Encoding) (p : Nat) : BitVec 8 := count 3 (pToZ bits p)

def reachesLocal (bits : Encoding) (source target : Nat) : Bool :=
  any 15 fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    coreArc bits source middle && coreArc bits middle target

def strictSecondLocal (bits : Encoding) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachesLocal bits source target

def localSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 18 (strictSecondLocal bits source)

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)

def fixedA (bits : Encoding) : Bool :=
  aArc bits 0 1 && aArc bits 0 2 &&
  all 5 (fun i => !aArc bits 0 (3 + i)) &&
  !aArc bits 1 7 && !aArc bits 2 7 &&
  all 4 (fun x => aArc bits (3 + x) 0 && aArc bits (3 + x) 7)

def everyXReached (bits : Encoding) : Bool :=
  all 4 fun x => any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
    any 7 (fun p => pToH bits p (2 + x))

def hTournament (bits : Encoding) : Bool :=
  all 6 fun i => all 6 fun j => decide (i = j) ||
    (aArc bits (1 + i) (1 + j) != aArc bits (1 + j) (1 + i))

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a => (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (7 : BitVec 8).ule (aPOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aPOut bits a)

def hDegreeEight (bits : Encoding) : Bool :=
  all 6 fun h => directCount bits (1 + h) == 8

def pDegreeEight (bits : Encoding) : Bool :=
  all 7 fun p => pOut bits p + pHOut bits p + pZOut bits p == 8

def totalPToZ (bits : Encoding) : BitVec 8 :=
  count 21 fun q => pToZ bits (q / 3) (q % 3)

def aNonSeymour (bits : Encoding) : Bool :=
  all 8 fun a => (localSecondCount bits a).ult (directCount bits a)

def pNonSeymour (bits : Encoding) : Bool :=
  all 7 fun p => (localSecondCount bits (8 + p)).ult
    (directCount bits (8 + p))

def retainedAfterAOneDeletion (bits : Encoding) (x vertex : Nat) : Bool :=
  decide (vertex ≠ 0) && coreArc bits (3 + x) vertex

def xDeletionExpands (bits : Encoding) (x : Nat) : Bool :=
  let retained := retainedAfterAOneDeletion bits x
  let reached := fun target => decide (target ≠ 3 + x) && !retained target &&
    any 15 (fun middle => retained middle && coreArc bits middle target)
  (7 : BitVec 8).ule (count 18 reached)

def core (bits : Encoding) : Bool :=
  orientedA bits && fixedA bits && hTournament bits &&
  hDegreeEight bits && pDegreeEight bits &&
  totalPToZ bits == 18 && aNonSeymour bits && pNonSeymour bits &&
  all 4 (xDeletionExpands bits)

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeLocalCore
