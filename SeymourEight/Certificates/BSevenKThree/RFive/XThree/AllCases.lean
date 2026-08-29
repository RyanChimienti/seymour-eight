import SeymourEight.Certificates.BSevenKThree.RFive.XThree.Tactic

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
/-- One finite check for the disjunction of all three feasible `(y,z)` modes. -/
theorem all_cases_unsat (bits : Encoding) :
    (core 1 3 bits || core 2 1 bits || core 2 2 bits) = false := by
  r5x3_simp
  bv_decide (config := { timeout := 1200, acNf := true, maxSteps := 1000000000 })

theorem one_three_unsat (bits : Encoding) : core 1 3 bits = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have hall := all_cases_unsat bits
  simp [h] at hall

theorem two_one_unsat (bits : Encoding) : core 2 1 bits = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have hall := all_cases_unsat bits
  simp [h] at hall

theorem two_two_unsat (bits : Encoding) : core 2 2 bits = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have hall := all_cases_unsat bits
  simp [h] at hall

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core
