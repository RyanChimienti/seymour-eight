import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.ExpansionTactic

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore

set_option maxRecDepth 100000
set_option maxHeartbeats 512000000 in
theorem six_unsat (bits : Core.Encoding) : core 6 bits = false := by
  solve_expansion_core

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore
