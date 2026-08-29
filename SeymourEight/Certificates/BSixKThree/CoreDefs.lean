import Std.Tactic.BVDecide

/-!
# Finite obstruction cores for the `(|B|, k) = (6, 3)` case

The fourteen local vertices are ordered as
`a₁, A₁ (3 vertices), X, R, P, Q`.  The separate array `externalArc`
records arcs from `P` to the represented external second neighbours of `a₁`.

The arithmetic reduction leaves four maximal cores.  Smaller values of the
external-neighbour count embed in these cores by padding `externalArc` with
false columns.
-/

namespace SeymourEight.BSixKThreeCore

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def sumN : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, f => sumN n f + bitCount (f n)

def allN : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allN n f && f n

def anyN : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => anyN n f || f n

def sumCountsN : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, f => sumCountsN n f + f n

def localOut (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 14 (arc u)

def internalA (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 8 (arc u)

def outB (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 6 fun j => arc u (8 + j)

def reachedLocal (arc : Nat → Nat → Bool) (u t : Nat) : Bool :=
  anyN 14 fun m => decide (m ≠ u) && decide (m ≠ t) && arc u m && arc m t

def secondLocal (arc : Nat → Nat → Bool) (u : Nat) : BitVec 8 :=
  sumN 14 fun t => decide (t ≠ u) && !arc u t && reachedLocal arc u t

def reachedExternal (r : Nat) (arc externalArc : Nat → Nat → Bool)
    (u t : Nat) : Bool :=
  anyN r fun i => arc u (8 + i) && externalArc i t

def representedSecondCount (r w : Nat) (arc externalArc : Nat → Nat → Bool)
    (u : Nat) : BitVec 8 :=
  secondLocal arc u + sumN w (reachedExternal r arc externalArc u)

def pivotRow (r : Nat) (arc : Nat → Nat → Bool) (u : Nat) : Bool :=
  (3 : BitVec 8).ule (internalA arc u) &&
    ((3 : BitVec 8).ult (internalA arc u) ||
      (r : BitVec 8).ule (outB arc u))

/-- The common finite model.  Parameters are `|P|`, `|X|`, and the number of
represented external columns respectively. -/
def core (r x w : Nat) (arc externalArc : Nat → Nat → Bool) : Bool :=
  (allN 14 fun i => !arc i i && allN 14 fun j =>
    decide (i = j) || !(arc i j && arc j i)) &&
  (allN 14 fun j =>
    arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 8 + r)) &&
  (allN 3 fun i => allN (4 - x) fun j => !arc (1 + i) (4 + x + j)) &&
  (allN r fun i => allN (4 - x) fun j => !arc (8 + i) (4 + x + j)) &&
  (allN 3 fun i => pivotRow r arc (1 + i)) &&
  (allN x fun i => pivotRow r arc (4 + i)) &&
  (allN x fun i => (8 : BitVec 8).ule (localOut arc (4 + i))) &&
  (allN r fun i => (8 : BitVec 8).ule
    (localOut arc (8 + i) + sumN w (externalArc i))) &&
  (allN 3 fun i =>
    (representedSecondCount r w arc externalArc (1 + i)).ult
      (localOut arc (1 + i)))

/-- Valid redundant consequences used to make the largest SAT certificate
tractable: pivot/minimum-degree rows, reachability of every represented target,
and the two aggregate degree bounds from the counting reduction. -/
def xFourCore (arc externalArc : Nat → Nat → Bool) : Bool :=
  core 6 4 4 arc externalArc &&
  (allN 8 fun i => pivotRow 6 arc i) &&
  (allN 8 fun i => (8 : BitVec 8).ule (localOut arc i)) &&
  (allN 4 fun j => anyN 3 (fun i => arc (1 + i) (4 + j)) ||
    anyN 6 (fun i => arc (8 + i) (4 + j))) &&
  (allN 6 fun j => anyN 8 fun i => arc i (8 + j)) &&
  (allN 4 fun j => anyN 6 fun i => externalArc i j) &&
  (31 : BitVec 8).ule (sumCountsN 7 fun i => outB arc (1 + i)) &&
  (22 : BitVec 8).ule (sumCountsN 6 fun i => sumN 4 (externalArc i))

end SeymourEight.BSixKThreeCore
