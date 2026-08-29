import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.Tactic

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Shared.FiniteCore

set_option maxRecDepth 100000

set_option maxHeartbeats 512000000 in
theorem pMinimumDegreeFive_implies_degreeSum (bits : Encoding) :
    (!(all 6 fun p => (8 : BitVec 8).ule
        (pOut bits p + pHOut bits p + pEOut 5 bits p)) ||
      (48 : BitVec 8).ule
        (totalPOut bits + totalPToH bits + totalPToE 5 bits)) = true := by
  rSixXTwoNoRoot_decide

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
