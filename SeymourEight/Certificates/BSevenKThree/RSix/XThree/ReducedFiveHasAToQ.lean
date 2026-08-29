import SeymourEight.Certificates.BSevenKThree.RSix.XThree.ReducedQSplitDefs

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem five_reduced_has_a_to_q (bits : Encoding) :
    reducedFiveHasAToQ bits = false := by
  r6x3_reduced_q_split_simp
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core
