import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Unreached

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- The five-external-target unreached obstruction is a finite 197-bit decision.
theorem five_unsat (bits : Encoding) : reducedCore 5 bits = false := by
  r6x3_unreached_simp
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedCore
