import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.FourTactic

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourCore

set_option maxRecDepth 100000
set_option maxHeartbeats 512000000 in
-- The whole four-target scalar simplex, using the shifted five-column defect.
theorem all_unsat (bits : Core.Encoding) :
    boxLeaf 7 12 0 4 0 5 bits = false := by
  solve_four_box

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourCore
