import SeymourEight.Certificates.BSevenKThree.RSix.XFour.StrongDualDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.APRigid

open Rigid StrongDual

def pRigidArc (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  if 8 ≤ i ∧ i < 14 ∧ 8 ≤ j ∧ j < 14 then
    if i = j then false
    else if i < j then raw i j
    else !raw j i
  else raw i j

def strongAPRigidDualLeaf
    (m alphaValue betaValue etaValue hqValue crossValue eligibleLower : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  strongARigidDualLeaf m alphaValue betaValue etaValue hqValue crossValue
    eligibleLower (pRigidArc raw) pToZ

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.APRigid
