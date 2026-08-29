import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeNormalization
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowNormalization

open ZThreeCore ZThreeLowCore ZThreeNormalization

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 512000000 in
theorem mZeroExternal_of_total (bits : Encoding)
    (hTotal : (totalPToZ bits == 21) = true) :
    mZeroExternal bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [totalPToZ, mZeroExternal, pZPattern, pToZ, all, count, bitCount,
     beq_iff_eq] at hTotal ⊢
  bv_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 512000000 in
theorem mOneExternal_of_ordered (bits : Encoding)
    (hTotal : (totalPToZ bits == 20) = true)
    (hRows : orderedExternalRows bits = true)
    (hZ : orderedExternalZ bits = true) :
    mOneExternal bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [totalPToZ, mOneExternal, orderedExternalRows, orderedExternalZ,
     zOrbitKey, zIn, pZPattern, pZOut, pToZ, all, count, bitCount,
     beq_iff_eq] at hTotal hRows hZ ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowNormalization
