import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Shared.FiniteCore

/-- The exact five-column effective condition, with the total missing count
represented by a two-bit selector rather than duplicated as a family index. -/
def pEffectiveConditionFiveSelected (m : BitVec 2) (bits : Encoding)
    (p : Nat) : Bool :=
  (pSecondPCount bits p +
      individualEffectiveLowerFiveAt (m.zeroExtend 8) (pEOut 5 bits p) + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut 5 bits p)

/-- One selected-missing-count range replaces the exact `m` partition.  The
last conjunct is the redundant sum of the six minimum-degree inequalities. -/
def microHEffectiveLowPHSelectedMissing (c bound maxM : Nat)
    (m : BitVec 2) (bits : Encoding) : Bool :=
  microHCore c bits && all 6 (pEffectiveConditionFiveSelected m bits) &&
  distinguishedAOne bits &&
  (totalPToH bits).ule (BitVec.ofNat 8 bound) &&
  externalMissing 5 bits == m.zeroExtend 8 &&
  m.ule (BitVec.ofNat 2 maxM) &&
  (48 : BitVec 8).ule
    (totalPOut bits + totalPToH bits + totalPToE 5 bits)

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
