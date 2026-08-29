import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.All
import Mathlib.Tactic.IntervalCases

namespace SeymourEight.FourZUnionEight

set_option maxHeartbeats 1000000 in
theorem core_unsat (missing degreeSum : Nat) (hMissing : missing ≤ 1)
    (hDegreeLower : 56 ≤ degreeSum)
    (hDegreeUpper : degreeSum ≤ 63 - missing)
    (bits : BitVec 105) : core missing degreeSum bits = false := by
  interval_cases missing <;> interval_cases degreeSum <;>
    first
    | omega
    | simp only [core_m0_d56_unsat, core_m0_d57_unsat, core_m0_d58_unsat,
        core_m0_d59_unsat, core_m0_d60_unsat, core_m0_d61_unsat,
        core_m0_d62_unsat, core_m0_d63_unsat, core_m1_d56_unsat,
        core_m1_d57_unsat, core_m1_d58_unsat, core_m1_d59_unsat,
        core_m1_d60_unsat, core_m1_d61_unsat, core_m1_d62_unsat]

end SeymourEight.FourZUnionEight
