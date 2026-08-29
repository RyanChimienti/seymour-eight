import SeymourEight.Certificates.BSevenKThree.RSix.XFour.PositiveAlphaRangeDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core HDeletion Rigid

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem aRigidPositiveAlphaRange_false (raw pToZ : Nat → Nat → Bool) :
    aRigidPositiveAlphaRange raw pToZ = false := by
  simp only [aRigidPositiveAlphaRange, eligibleCapacityCut,
    aRigidPositiveSlice, capacityTwoToFive, eligibleHCount]
  r6x4_rigid_h_deletion_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
