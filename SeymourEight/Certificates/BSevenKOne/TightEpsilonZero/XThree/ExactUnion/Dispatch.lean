import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.All
import Mathlib.Tactic.IntervalCases

namespace SeymourEight.FourZExactSeven

set_option maxHeartbeats 2000000 in
/-- Dispatch the fourteen degree-range certificates and the retained `.xTwo`
exact rows using the genuine total `P`-degree sum and canonical overlap type. -/
theorem core_unsat (missing degreeSum : Nat) (overlap : OverlapType)
    (hMissing : missing ≤ 1) (hLower : 56 ≤ degreeSum)
    (hUpper : degreeSum ≤ 63 - missing) (bits : BitVec 214) :
    core missing degreeSum overlap bits = false := by
  let degreeCode : BitVec 3 := BitVec.ofNat 3 (degreeSum - 56)
  have hCodeLt : degreeSum - 56 < 8 := by omega
  have hCode : degreeCode.toNat = degreeSum - 56 := by
    simp [degreeCode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCodeLt]
  have hDegree : 56 + degreeCode.toNat = degreeSum := by omega
  interval_cases missing
  · cases overlap
    · simpa only [hDegree] using core_m0_none_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m0_xOne_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m0_aOne_degree_range_unsat degreeCode bits
    · exact core_m0_xTwo_exact_unsat degreeSum hLower (by omega) bits
    · simpa only [hDegree] using core_m0_aXOne_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m0_xThree_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m0_aXTwo_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m0_aXThree_degree_range_unsat degreeCode bits
  · cases overlap
    · simpa only [hDegree] using core_m1_none_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m1_xOne_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m1_aOne_degree_range_unsat degreeCode bits
    · exact core_m1_xTwo_exact_unsat degreeSum hLower (by omega) bits
    · simpa only [hDegree] using core_m1_aXOne_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m1_xThree_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m1_aXTwo_degree_range_unsat degreeCode bits
    · simpa only [hDegree] using core_m1_aXThree_degree_range_unsat degreeCode bits
end SeymourEight.FourZExactSeven
