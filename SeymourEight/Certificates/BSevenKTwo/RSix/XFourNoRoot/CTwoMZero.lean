import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.Tactic

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core

set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
theorem cTwo_mZero_aZero_bZero_unsat (bits : Encoding) :
    coreCase 2 0 0 0 bits = false := by
  solve_r_six_x_four_no_root

set_option maxHeartbeats 20000000 in
theorem cTwo_mZero_aOne_bZero_unsat (bits : Encoding) :
    coreCase 2 0 1 0 bits = false := by
  solve_r_six_x_four_no_root

set_option maxHeartbeats 20000000 in
theorem cTwo_mZero_aZero_bOne_unsat (bits : Encoding) :
    coreCase 2 0 0 1 bits = false := by
  solve_r_six_x_four_no_root

set_option maxHeartbeats 20000000 in
theorem cTwo_mZero_aTwo_bZero_unsat (bits : Encoding) :
    coreCase 2 0 2 0 bits = false := by
  solve_r_six_x_four_no_root

set_option maxHeartbeats 20000000 in
theorem cTwo_mZero_aOne_bOne_unsat (bits : Encoding) :
    coreCase 2 0 1 1 bits = false := by
  solve_r_six_x_four_no_root

set_option maxHeartbeats 20000000 in
theorem cTwo_mZero_aZero_bTwo_unsat (bits : Encoding) :
    coreCase 2 0 0 2 bits = false := by
  solve_r_six_x_four_no_root

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core
