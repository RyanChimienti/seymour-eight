import SeymourEight.Certificates.BSevenKThree.RSix.XFour.D501PositiveDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Positive

open Lean Parser Tactic
open APRigid StrongDual

macro "r6x4_d501_positive_decide" : tactic =>
  `(tactic|
    simp only [d501PositiveLeaf, eligibleHCount, pRigidArc] <;>
    r6x4_rigid_h_deletion_decide)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Positive
