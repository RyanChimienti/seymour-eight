import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ReducedCapacityDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.APRigidDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open APRigid

def apRigidPositiveSlice
    (alphaLower alphaUpper betaLower betaUpper mLower mUpper : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  aRigidPositiveSlice alphaLower alphaUpper betaLower betaUpper mLower mUpper
    (pRigidArc raw) pToZ

/-- The positive-alpha `delta=2` range has `beta=0`, so its P block is a
tournament and can be reconstructed from one bit per unordered pair. -/
def pRigidPositiveAlphaDeltaTwoLeaf
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  positiveAlphaDeltaLeaf 2 (pRigidArc raw) pToZ

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
