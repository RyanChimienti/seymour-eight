import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactTactic

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

set_option maxRecDepth 100000

set_option maxHeartbeats 30000000 in
theorem lowExact01_unsat (bits : Encoding) : lowExactCore01All bits = false := by
  solve_low_exact

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
