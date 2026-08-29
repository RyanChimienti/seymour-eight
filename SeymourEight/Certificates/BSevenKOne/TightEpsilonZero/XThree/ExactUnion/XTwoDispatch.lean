import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D56XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D57XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D58XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D59XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D60XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D61XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D62XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M0D63XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D56XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D57XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D58XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D59XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D60XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D61XTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Rows.M1D62XTwo

import Mathlib.Tactic.IntervalCases

namespace SeymourEight.FourZExactSeven

theorem core_m0_xTwo_exact_unsat (degreeSum : Nat)
    (hLower : 56 ≤ degreeSum) (hUpper : degreeSum ≤ 63)
    (bits : BitVec 214) : core 0 degreeSum .xTwo bits = false := by
  interval_cases degreeSum <;>
    simp only [core_m0_d56_xTwo_unsat, core_m0_d57_xTwo_unsat,
      core_m0_d58_xTwo_unsat, core_m0_d59_xTwo_unsat,
      core_m0_d60_xTwo_unsat, core_m0_d61_xTwo_unsat,
      core_m0_d62_xTwo_unsat, core_m0_d63_xTwo_unsat]

theorem core_m1_xTwo_exact_unsat (degreeSum : Nat)
    (hLower : 56 ≤ degreeSum) (hUpper : degreeSum ≤ 62)
    (bits : BitVec 214) : core 1 degreeSum .xTwo bits = false := by
  interval_cases degreeSum <;>
    simp only [core_m1_d56_xTwo_unsat, core_m1_d57_xTwo_unsat,
      core_m1_d58_xTwo_unsat, core_m1_d59_xTwo_unsat,
      core_m1_d60_xTwo_unsat, core_m1_d61_xTwo_unsat,
      core_m1_d62_xTwo_unsat]

end SeymourEight.FourZExactSeven
