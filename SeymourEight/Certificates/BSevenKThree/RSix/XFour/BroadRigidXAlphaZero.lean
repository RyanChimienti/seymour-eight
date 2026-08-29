import SeymourEight.Certificates.BSevenKThree.RSix.XFour.BroadRigidXTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem broadRigidXAlphaZero_false (raw pToZ : Nat → Nat → Bool) :
    broadRigidXAlphaZeroLeaf raw pToZ = false := by
  r6x4_broad_rigid_x_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
