import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHRangeTactic

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

set_option maxRecDepth 100000

set_option maxHeartbeats 512000000 in
theorem microHEffectiveLowPH_two_range_unsat
    (m : BitVec 2) (bits : Encoding) :
    microHEffectiveLowPHSelectedMissing 2 6 3 m bits = false := by
  rSixXTwoNoRoot_range_decide

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
