import SeymourEight.Certificates.BSevenKThree.RSix.XFour.AuxiliaryDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryCore

open Shared.FiniteCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The nested anonymous signature family has exactly the requested four
marginals whenever every named auxiliary outdegree is at most eight. -/
theorem auxiliaryExact_canonical (auxArc : Nat → Nat → Bool)
    (hNamed : (all 4 fun i => (auxNamedOut auxArc i).ule 8) = true) :
    auxiliaryExact auxArc (canonicalSignature auxArc) = true := by
  simp only [auxiliaryExact, canonicalSignature, canonicalSlotHasMask,
    canonicalOutsideNeed, count4, bitCount4, auxOutsideOut,
    signatureValue, maskHas,
    auxNamedOut, sumCount, count, bitCount, all] at hNamed ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryCore
