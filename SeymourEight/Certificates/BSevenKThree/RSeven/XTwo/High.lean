import SeymourEight.Shared.InnerDegreeThree

/-! A tiny eight-vertex certificate closing both `z ≥ 6` rows. -/

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.HighCore

open Shared.FiniteCore Shared.InnerDegreeThree

def fixedPivotRow (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun target => arc 0 target == decide (1 ≤ target ∧ target ≤ 3)

def rUnreached (arc : Nat → Nat → Bool) : Bool :=
  all 3 fun a => all 2 fun r => !arc (1 + a) (6 + r)

def highCore (arc : Nat → Nat → Bool) : Bool :=
  oriented arc && fixedPivotRow arc && minimumThree arc && rUnreached arc &&
    all 3 (fun a => (secondCount arc (1 + a) + 6).ult 10)

set_option maxRecDepth 100000
set_option maxHeartbeats 512000000 in
-- Expanding the quantified eight-vertex Boolean core exceeds the default budget.
theorem high_unsat (arc : Nat → Nat → Bool) : highCore arc = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [highCore, fixedPivotRow, rUnreached, oriented, minimumThree,
      outCount, secondCount, second, reaches, all, any, count, bitCount]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.HighCore
