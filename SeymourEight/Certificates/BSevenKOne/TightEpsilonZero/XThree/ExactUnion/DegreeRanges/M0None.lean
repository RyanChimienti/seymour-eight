import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.DegreeRangeTactic

namespace SeymourEight.FourZExactSeven

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem core_m0_none_degree_range_unsat (degreeCode : BitVec 3)
    (bits : BitVec 214) :
    core 0 (56 + degreeCode.toNat) .none bits = false := by
  four_z_exact_degree_range_decide

end SeymourEight.FourZExactSeven
