import SeymourEight.Certificates.BSixKThree.CoreDefs

/-!
# Compact cores for `r = 6`, `x = 2`

The local vertices are `A = 0..7`, `P = 8..13`, and the unique vertex of
`Q` at 14.  A separate six-column array records `P` incidences to the
external targets.  Only the non-Seymour inequalities for A-indices `0..5`
are needed.
-/

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core

open SeymourEight.BSixKThreeCore

def localOut (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 15 (arc u)

def internalA (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 8 (arc u)

def outB (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 7 fun j ↦ arc u (8 + j)

def reachedLocal (arc : Nat → Nat → Bool) (u t : Nat) : Bool :=
  anyN 15 fun m ↦ decide (m ≠ u) && decide (m ≠ t) && arc u m && arc m t

def secondLocal (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 15 fun t ↦ decide (t ≠ u) && !arc u t && reachedLocal arc u t

def reachedExternal (arc externalArc : Nat → Nat → Bool)
    (u t : Nat) : Bool :=
  anyN 6 fun i ↦ arc u (8 + i) && externalArc i t

def representedSecondCount (active : Nat)
    (arc externalArc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  secondLocal arc u + sumN active (reachedExternal arc externalArc u)

def pivotRow (arc : Nat → Nat → Bool) (u : Nat) : Bool :=
  (3 : BitVec 8).ule (internalA arc u) &&
    ((3 : BitVec 8).ult (internalA arc u) ||
      (6 : BitVec 8).ule (outB arc u))

def qReached (arc : Nat → Nat → Bool) : Bool :=
  anyN 3 (fun i ↦ arc (1 + i) 14) ||
    anyN 6 (fun i ↦ arc (8 + i) 14)

def core (active : Nat) (reachedQ : Bool)
    (arc externalArc : Nat → Nat → Bool) : Bool :=
  (allN 15 fun i ↦ !arc i i && allN 15 fun j ↦
    decide (i = j) || !(arc i j && arc j i)) &&
  (allN 15 fun j ↦
    arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 14)) &&
  (allN 3 fun i ↦ allN 2 fun j ↦ !arc (1 + i) (6 + j)) &&
  (allN 6 fun i ↦ allN 2 fun j ↦ !arc (8 + i) (6 + j)) &&
  (qReached arc == reachedQ) &&
  (allN 5 fun h ↦ pivotRow arc (1 + h) &&
    (8 : BitVec 8).ule (localOut arc (1 + h))) &&
  (allN 6 fun p ↦ (8 : BitVec 8).ule
    (localOut arc (8 + p) + sumN active (externalArc p))) &&
  (allN 6 fun i ↦
    (representedSecondCount active arc externalArc i).ult
      (localOut arc i))

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core
