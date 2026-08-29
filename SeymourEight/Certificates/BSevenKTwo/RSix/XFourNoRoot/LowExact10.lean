import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactTactic

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

set_option maxRecDepth 100000

set_option maxHeartbeats 30000000 in
theorem lowExact10_unsat (bits : Encoding) :
    lowExactCore10All 20 bits = false := by
  solve_low_exact

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
