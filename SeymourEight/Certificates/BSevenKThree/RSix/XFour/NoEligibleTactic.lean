import SeymourEight.Certificates.BSevenKThree.RSix.XFour.NoEligibleDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Tactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Lean Parser Tactic
open Core

macro "r6x4_no_eligible_decide" : tactic =>
  `(tactic|
    simp only [noEligibleCapacityLeaf, noEligibleLowCapacityLeaf,
      noEligibleComponentLeaf, aRigidNoEligibleComponentLeaf,
      pRigidNoEligibleComponentLeaf, apRigidNoEligibleComponentLeaf,
      Rigid.aRigidArc, Rigid.fixedArc, APRigid.pRigidArc,
      eligibleHCount] <;>
    r6x4_no_root_decide)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
