import Std.Tactic.BVDecide

/-!
# General finite core for the four-`Z` complement

Unlike `ThetaFourCore.Encoding`, this layout does not assume that `P` is a
tournament or that every `P`--`H` pair is oriented.  It is used only for the
branches preceding the existing eta-zero mixed-omission residual.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourCore

abbrev Encoding := BitVec 225

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

def aArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (8 * i + j)

def directedIndex (i j : Nat) : Nat :=
  6 * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (64 + directedIndex i j)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (106 + 6 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  bits.getLsbD (148 + 7 * h + p)

def pToZ (bits : Encoding) (p z : Nat) : Bool :=
  bits.getLsbD (190 + 4 * p + z)

def rToP (bits : Encoding) (p : Nat) : Bool :=
  bits.getLsbD (218 + p)

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

def aOut (bits : Encoding) (a : Nat) : BitVec 8 := count 8 (aArc bits a)
def aPOut (bits : Encoding) (a : Nat) : BitVec 8 := count 7 (aToP bits a)
def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 7 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pToH bits p)
def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 7 (hToP bits h)
def pZOut (bits : Encoding) (p : Nat) : BitVec 8 := count 4 (pToZ bits p)

def reachesLocal (bits : Encoding) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc bits source middle && coreArc bits middle target

def strictSecondLocal (bits : Encoding) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachesLocal bits source target

def localSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 19 (strictSecondLocal bits source)

def aNonSeymour (bits : Encoding) (a : Nat) : Bool :=
  (localSecondCount bits a).ult (directCount bits a)

def pNonSeymour (bits : Encoding) (p : Nat) : Bool :=
  (localSecondCount bits (8 + p)).ult (directCount bits (8 + p))

/-- Strict second neighbors in `P`, reached through the retained `P ∪ H`
blocks.  These are disjoint from the effective targets outside `P ∪ Z`
supplied by the auxiliary-capacity inequality. -/
def pSecondPCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => strictSecondLocal bits (8 + p) (8 + q)

def orientedA (bits : Encoding) : Bool :=
  all 8 fun i => !aArc bits i i && all 8 fun j =>
    decide (i = j) || !(aArc bits i j && aArc bits j i)

def orientedP (bits : Encoding) : Bool :=
  all 7 fun i => all 7 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)

def orientedPH (bits : Encoding) : Bool :=
  all 7 fun p => all 6 fun h => !(pToH bits p h && hToP bits h p)

def fixedA (bits : Encoding) : Bool :=
  aArc bits 0 1 && aArc bits 0 2 &&
  all 5 (fun i => !aArc bits 0 (3 + i)) &&
  !aArc bits 1 7 && !aArc bits 2 7

def everyXReached (bits : Encoding) : Bool :=
  all 4 fun x =>
    any 2 (fun a => aArc bits (1 + a) (3 + x)) ||
      any 7 (fun p => pToH bits p (2 + x))

def allZReached (bits : Encoding) : Bool :=
  all 4 fun z => any 7 fun p => pToZ bits p z

def aMinimumAndDegree (bits : Encoding) : Bool :=
  all 8 fun a =>
    (2 : BitVec 8).ule (aOut bits a) &&
    (!(aOut bits a == 2) || (7 : BitVec 8).ule (aPOut bits a)) &&
    (8 : BitVec 8).ule (aOut bits a + aPOut bits a)

def pMinimumDegree (bits : Encoding) : Bool :=
  all 7 fun p =>
    (8 : BitVec 8).ule (pOut bits p + pHOut bits p + pZOut bits p)

def totalPToZ (bits : Encoding) : BitVec 8 := sumCount 7 (pZOut bits)
def totalPToH (bits : Encoding) : BitVec 8 := sumCount 7 (pHOut bits)
def totalHToP (bits : Encoding) : BitVec 8 := sumCount 6 (hPOut bits)
def totalPOut (bits : Encoding) : BitVec 8 := sumCount 7 (pOut bits)

def externalMissing (bits : Encoding) : BitVec 8 := 28 - totalPToZ bits

def effectiveAtRowSize (s v1 v2 v3 v4 : BitVec 8) : BitVec 8 :=
  if s == 0 then 0 else if s == 1 then v1 else if s == 2 then v2
  else if s == 3 then v3 else v4

/-- The individual effective-target bound for four auxiliaries.  Entry `(m,s)`
is the minimum number of distinct effective targets outside `P ∪ Z` reached through
an `s`-element direct `Z` neighborhood when the total P→Z defect is `m`.
The apparently large entries in impossible cells (`4-s > m`) are harmless
and make the table a total Boolean function. -/
def individualEffectiveLower (bits : Encoding) (p : Nat) : BitVec 8 :=
  let m := externalMissing bits
  let s := pZOut bits p
  if m == 0 then effectiveAtRowSize s 11 9 8 7
  else if m == 1 then effectiveAtRowSize s 10 8 7 7
  else if m == 2 then effectiveAtRowSize s 9 8 7 6
  else if m == 3 then effectiveAtRowSize s 8 7 7 6
  else if m == 4 then effectiveAtRowSize s 7 7 6 6
  else if m == 5 then effectiveAtRowSize s 6 6 6 6
  else if m == 6 then effectiveAtRowSize s 5 6 6 5
  else if m == 7 then effectiveAtRowSize s 4 5 5 5
  else if m == 8 then effectiveAtRowSize s 3 5 5 5
  else if m == 9 then effectiveAtRowSize s 2 4 5 5
  else effectiveAtRowSize s 1 4 4 4

def pEffectiveCondition (bits : Encoding) (p : Nat) : Bool :=
  (pSecondPCount bits p + individualEffectiveLower bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pZOut bits p)

def internalMissing (bits : Encoding) : BitVec 8 := 21 - totalPOut bits

/-- Triangular almost-tournament king bound. -/
def sharpKingLower (beta : BitVec 8) : BitVec 8 :=
  if beta == 0 then 6 else if beta.ule 2 then 5 else if beta.ule 5 then 4
  else if beta.ule 9 then 3 else if beta.ule 14 then 2
  else if beta.ule 20 then 1 else 0

def sharpKing (bits : Encoding) : Bool :=
  any 7 fun p => (sharpKingLower (internalMissing bits)).ule
    (pOut bits p + pSecondPCount bits p)

def pRowKey (bits : Encoding) (p : Nat) : BitVec 16 :=
  (pZOut bits p).zeroExtend 16 * 4096 +
    (directCount bits (8 + p)).zeroExtend 16 * 256 +
    (pOut bits p).zeroExtend 16 * 16 + (pHOut bits p).zeroExtend 16

def orderedP (bits : Encoding) : Bool :=
  all 6 fun p => (pRowKey bits (p + 1)).ule (pRowKey bits p)

def zColumnCode (bits : Encoding) (z : Nat) : BitVec 8 :=
  count 7 fun p => pToZ bits p z && decide (p < 8)

def orderedZ (bits : Encoding) : Bool :=
  all 3 fun z => (zColumnCode bits (z + 1)).ule (zColumnCode bits z)

/-- Common graph projection for the computational complement. -/
def broadCore (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits && fixedA bits &&
  everyXReached bits && allZReached bits &&
  (3 : BitVec 8).ule (count 8 fun q =>
    let a := q / 4
    let x := q % 4
    aArc bits (1 + a) (3 + x)) &&
  aMinimumAndDegree bits && all 8 (aNonSeymour bits) &&
  pMinimumDegree bits && all 7 (pNonSeymour bits) &&
  all 7 (pEffectiveCondition bits) &&
  orderedP bits && orderedZ bits

/-- The scalar bounds supplied by the graph bridge in the four-`Z` row.  If
`m` is the P→Z defect, then `m ≤ 10`, `25 ≤ e(H,P)`, and the usual defect
count gives `e(H,P) + m ≤ 35`.  Keeping the last bound profile-sensitive is
important: `e(H,P) ≤ 29` is valid in the `m = 6` slice, not across the row. -/
def zFourCore (bits : Encoding) : Bool :=
  broadCore bits && (3 : BitVec 8).ule (externalMissing bits) &&
    (externalMissing bits).ule 10 &&
    (25 : BitVec 8).ule (totalHToP bits) &&
    (totalHToP bits + externalMissing bits).ule 35

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourCore
