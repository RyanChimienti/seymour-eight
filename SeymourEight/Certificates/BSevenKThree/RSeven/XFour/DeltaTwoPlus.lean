import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.RemainingTactic

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore

set_option maxRecDepth 100000
set_option maxHeartbeats 256000000 in
-- Every parent with at least two missing pairs in `A`.
theorem deltaTwoPlus_unsat (bits : Core.Encoding) :
    boxLeaf 0 12 2 4 0 6 bits = false := by
  solve_remaining_box

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore
