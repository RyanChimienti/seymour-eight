import SeymourEight.Certificates.BSevenKThree.RSix.XFour.BroadRigidXDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

open Lean Parser Tactic

macro "r6x4_broad_rigid_x_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000 }) only
      [broadRigidXAlphaZeroLeaf,
        HDeletion.xQDeletionConditions] <;>
    r6x4_rigid_h_deletion_decide)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
