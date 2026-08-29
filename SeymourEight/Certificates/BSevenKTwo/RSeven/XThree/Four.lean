import SeymourEight.Certificates.BSevenKTwo.RSeven.XThree.Tactic

namespace SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 256000000 in
theorem four_impossible (bits : Encoding) : smallCore 4 bits = false := by
  solve_x_three_no_root

end SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core
