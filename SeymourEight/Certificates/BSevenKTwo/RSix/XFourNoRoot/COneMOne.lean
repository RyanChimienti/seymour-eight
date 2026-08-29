import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.Tactic

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core

set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
theorem cOne_mOne_aZero_bZero_unsat (bits : Encoding) :
    coreCase 1 1 0 0 bits = false := by
  solve_r_six_x_four_no_root

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core
