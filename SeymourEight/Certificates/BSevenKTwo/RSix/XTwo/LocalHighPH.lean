import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.Tactic

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

set_option maxRecDepth 100000

set_option maxHeartbeats 512000000 in
theorem microCZeroNonHard_unsat (bits : Encoding) :
    microCZeroNonHard bits = false := by
  rSixXTwoNoRoot_decide

set_option maxHeartbeats 512000000 in
theorem microCOneHighPH_unsat (bits : Encoding) :
    microCOneHighPH bits = false := by
  rSixXTwoNoRoot_decide

set_option maxHeartbeats 512000000 in
theorem microCTwoHighPH_unsat (bits : Encoding) :
    microCTwoHighPH bits = false := by
  rSixXTwoNoRoot_decide

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
