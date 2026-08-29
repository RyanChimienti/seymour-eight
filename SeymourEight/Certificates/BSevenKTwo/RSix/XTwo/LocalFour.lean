import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Lean Parser Tactic

set_option maxRecDepth 100000

macro "microFour_decide" : tactic =>
  `(tactic|
    unfold microFourDistinguished microFour distinguishedAOne <;>
    simp only [Shared.FiniteCore.all] <;>
    unfold hRestrictedNonSeymourFour hRestrictedSecondCountFour
      pMicroNonSeymourFour pSecondEMicroCoreCount hDirectCore hSecondQCore
      hSecondZCount aOneSecondH aOneSecondP aOneSecondT
      pSecondPCount pSecondHMicroCount pSecondTCount reachesPH
      everyXReached orientedP orientedPH orientedHH pOut pHOut hPOut pEOut
      totalPToE totalPToH totalHToP aOneToQ hToQCore <;>
    simp (config := { maxSteps := 1000000000 }) only
      [Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
        Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
        Shared.FiniteCore.all] <;>
    unfold hArc xToT aToQ pToE hToP pToH pArc directedIndex aArc <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

set_option maxHeartbeats 512000000 in
theorem microFourDistinguished_one_unsat (bits : Encoding) :
    microFourDistinguished 1 bits = false := by
  microFour_decide

set_option maxHeartbeats 512000000 in
theorem microFourDistinguished_two_unsat (bits : Encoding) :
    microFourDistinguished 2 bits = false := by
  microFour_decide

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
