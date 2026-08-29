import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.Tactic

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore

set_option maxRecDepth 100000
set_option maxHeartbeats 512000000 in
theorem five_unsat (bits : Core.Encoding) : symmetricCore 5 bits = false := by
  solve_x_three_core

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore
