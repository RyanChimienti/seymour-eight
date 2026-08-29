import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Shared.FiniteCore Core Rigid

def eligibleHCount (arc : Nat → Nat → Bool) : BitVec 8 :=
  count 7 fun h ↦ aDegree arc (1 + h) == 8 && aToQ arc (1 + h)

def strongARigidDualLeaf
    (m alphaValue betaValue etaValue hqValue crossValue eligibleLower : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  aRigidDualHDeletionLeaf m alphaValue betaValue etaValue hqValue crossValue
      raw pToZ &&
    (BitVec.ofNat 8 eligibleLower).ule (eligibleHCount (aRigidArc raw))

def strongRigidDualLeaf
    (m alphaValue betaValue etaValue hqValue crossValue eligibleLower : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  rigidDualHDeletionLeaf m alphaValue betaValue etaValue hqValue crossValue
      raw pToZ &&
    (BitVec.ofNat 8 eligibleLower).ule (eligibleHCount (rigidArc raw))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
