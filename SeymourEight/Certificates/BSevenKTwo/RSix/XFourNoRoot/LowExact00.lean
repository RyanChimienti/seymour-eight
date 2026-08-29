import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactTactic

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

set_option maxRecDepth 100000

set_option maxHeartbeats 30000000 in
theorem lowExact00_unsat (bits : Encoding) : lowExactCore00 bits = false := by
  solve_low_exact

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
