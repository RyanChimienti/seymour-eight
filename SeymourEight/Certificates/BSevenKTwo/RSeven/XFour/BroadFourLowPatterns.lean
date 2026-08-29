import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourLowCutTactic

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore

open BroadFourCore

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem selectedLowPattern_unsat (mode : BitVec 3) (bits : Encoding) :
    selectedLowPatternCore mode bits = false := by
  simp only [selectedLowPatternCore, selectedLowPattern, fullPToZ,
    pZMissingOne, pZMissingExactly]
  solve_low_cut

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore
