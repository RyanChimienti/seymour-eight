import SeymourEight.Certificates.BSevenKThree.RSeven.XTwo.Tactic

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 512000000 in
theorem five_unsat (bits : Encoding) : core 5 bits = false := by
  solve_x_two_core

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Core
