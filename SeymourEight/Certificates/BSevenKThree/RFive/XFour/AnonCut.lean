import SeymourEight.Certificates.BSevenKThree.RFive.XFour.AnonCutTactic

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem anonCutCounterexample_false (arc pToZ : Nat → Nat → Bool) :
    anonCutCounterexample arc pToZ = false := by
  r5x4_anon_cut_decide

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
