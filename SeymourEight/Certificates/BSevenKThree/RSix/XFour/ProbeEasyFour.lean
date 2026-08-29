import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Tactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem probeEasyFour (arc pToZ : Nat → Nat → Bool) :
    commonCore 0 4 arc pToZ = false := by
  r6x4_no_root_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
