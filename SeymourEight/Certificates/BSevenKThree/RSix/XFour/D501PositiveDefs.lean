import SeymourEight.Certificates.BSevenKThree.RSix.XFour.APRigidDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Positive

open HDeletion Rigid StrongDual APRigid

def d501PositiveLeaf (raw pToZ : Nat → Nat → Bool) : Bool :=
  hDeletionLeaf 5 0 1 0 (aRigidArc (pRigidArc raw)) pToZ &&
    (3 : BitVec 8).ule (eligibleHCount (aRigidArc (pRigidArc raw)))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Positive
