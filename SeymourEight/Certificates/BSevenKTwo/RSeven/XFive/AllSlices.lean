import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.Tactic

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 256000000 in
theorem allSlices_impossible (bits : Encoding) : suffixCore bits = false := by
  solve_x_five_no_root

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core
