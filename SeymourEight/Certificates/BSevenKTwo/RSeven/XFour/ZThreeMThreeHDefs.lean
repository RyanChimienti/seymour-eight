import Std.Tactic.BVDecide

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeHCore

abbrev Encoding := BitVec 36

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

def hArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (6 * i + j)

def tournament (bits : Encoding) : Bool := all 6 fun i => all 6 fun j =>
  decide (i = j) || (hArc bits i j != hArc bits j i)

def xOutH (bits : Encoding) (x : Nat) : BitVec 8 :=
  count 6 (hArc bits (x + 2))

def xReach (bits : Encoding) (x target : Nat) : Bool :=
  hArc bits (x + 2) (target + 2) || any 6 fun middle =>
    decide (middle ≠ x + 2) && decide (middle ≠ target + 2) &&
      hArc bits (x + 2) middle && hArc bits middle (target + 2)

def xReachCount (bits : Encoding) (x : Nat) : BitVec 8 :=
  count 4 fun target => decide (target ≠ x) && xReach bits x target

def xCondition (bits : Encoding) (x : Nat) : Bool :=
  let b := 6 - xOutH bits x
  (1 : BitVec 8).ule b &&
    (if b == 1 then true else if b.ule 3 then (xReachCount bits x).ule 1
      else xReachCount bits x == 0)

def core (bits : Encoding) : Bool :=
  tournament bits && all 4 (xCondition bits)

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeHCore
