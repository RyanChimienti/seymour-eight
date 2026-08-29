import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

open Shared.FiniteCore

set_option maxHeartbeats 30000000 in
-- This small finite implication uses kernel-checked bit-vector normalization.
/-- The row and auxiliary-column orders canonically locate the unique missing
`P → E` incidence once all six encoded `P` degrees are eight. -/
theorem canonicalPEOneMissing_of_ordered (bits : Encoding)
    (hP : orderedP bits = true) (hE : orderedETail bits = true)
    (hPE : (count 18 (fun n => pToE bits (n / 3) (n % 3)) == 17) = true)
    (hDeg : (all 6 fun p => pOut bits p == 8) = true) :
    canonicalPEOneMissing bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [canonicalPEOneMissing, orderedP, orderedETail, pRowKey,
    pEOut, pHOut, pPOut, pOut, pLocalArc, pToE, pToH, pArc,
    directedIndex, Shared.FiniteCore.count, Shared.FiniteCore.all,
    Shared.FiniteCore.bitCount, Bool.and_eq_true, Bool.or_eq_true] at *
  bv_decide (config := { maxSteps := 1000000000, timeout := 1200, acNf := true })

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
