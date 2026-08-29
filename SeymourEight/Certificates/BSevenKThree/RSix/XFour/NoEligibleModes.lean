import SeymourEight.Certificates.BSevenKThree.RSix.XFour.NoEligibleTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem noEligibleModes_false (mode : BitVec 2)
    (raw pToZ : Nat → Nat → Bool) :
    noEligibleModeLeaf mode raw pToZ = false := by
  simp only [noEligibleModeLeaf, APRigid.pRigidArc]
  r6x4_no_eligible_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
