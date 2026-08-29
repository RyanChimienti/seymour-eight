import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHRangeDefs
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.Tactic

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Lean Parser Tactic

macro "rSixXTwoNoRoot_range_decide" : tactic =>
  `(tactic|
    (simp only [microHEffectiveLowPHSelectedMissing, Shared.FiniteCore.all,
      pEffectiveConditionFiveSelected]) <;>
    rSixXTwoNoRoot_decide)

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
