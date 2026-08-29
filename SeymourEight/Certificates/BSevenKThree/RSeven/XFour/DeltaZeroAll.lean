import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.RemainingTactic
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.LowDeltaDefs

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore

set_option maxRecDepth 100000
set_option maxHeartbeats 256000000 in
theorem deltaZeroAll_unsat (bits : Core.Encoding) :
    deltaZeroAllLeaf bits = false := by
  simp only [deltaZeroAllLeaf, directScalarCut]
  solve_remaining_box

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore
