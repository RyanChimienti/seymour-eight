import SeymourEight.Certificates.BSevenKThree.RFive.XTwo.CoreDefs

/-!
# The rigid `A₁` triangle is internally Seymour

This tiny reusable check isolates the purely eight-vertex fact used by the
hard `(y,z)=(2,3)` bridge.  The pivot has precisely the three `A₁`
outneighbors, every `A₁` row has internal degree three, and no `A₁`
vertex points into the two-vertex remainder `R`.
-/

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core

open SeymourEight.BSixKThreeCore

set_option maxRecDepth 100000 in
theorem aOne_inner_of_rigid (arc : Nat → Nat → Bool) :
    !((allN 8 fun i ↦ !arc i i && allN 8 fun j ↦
        decide (i = j) || !(arc i j && arc j i)) &&
      (allN 8 fun j ↦ arc 0 j == decide (1 ≤ j && j ≤ 3)) &&
      (allN 3 fun i ↦ allN 2 fun j ↦ !arc (1 + i) (6 + j)) &&
      (allN 8 fun i ↦ (3 : BitVec 8).ule (internalA arc i)) &&
      (allN 3 fun i ↦ degreeThree arc (1 + i))) ||
      (allN 3 fun i ↦ degreeThreeInner arc (1 + i)) = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [degreeThreeInner, innerSeymour, degreeThree, innerSecondCount,
    innerSecond, innerReaches, internalA, sumN, allN, anyN, bitCount]
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core
