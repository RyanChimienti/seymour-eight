import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.Tactic

namespace SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 256000000 in
theorem four_impossible (bits : Encoding) : smallCore 4 bits = false := by
  solve_x_two_no_root

end SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core
