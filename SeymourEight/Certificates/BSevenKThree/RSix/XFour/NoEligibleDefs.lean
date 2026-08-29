import SeymourEight.Certificates.BSevenKThree.RSix.XFour.APRigidDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core
open Rigid APRigid

/-- The residual branch in which no vertex of `H` supports the sound
one-arc deletion reduction.  Only capacities four and five require a
certificate; at lower capacity, the degree/dual identities rule this branch
out arithmetically. -/
def noEligibleCapacityLeaf (capacity : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    eligibleHCount arc == 0

def noEligibleLowCapacityLeaf (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ &&
    (2 : BitVec 8).ule (capacityDefect arc pToZ) &&
    (capacityDefect arc pToZ).ule 3 && eligibleHCount arc == 0

/-- An exact scalar component of the no-eligible branch. -/
def noEligibleComponentLeaf (mValue deltaValue alphaValue betaValue : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 mValue &&
    aMissing arc == BitVec.ofNat 8 deltaValue &&
    alpha 1 arc == BitVec.ofNat 8 alphaValue &&
    internalMissing arc == BitVec.ofNat 8 betaValue &&
    eligibleHCount arc == 0

def aRigidNoEligibleComponentLeaf
    (mValue deltaValue alphaValue betaValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  noEligibleComponentLeaf mValue deltaValue alphaValue betaValue
    (aRigidArc raw) pToZ

def pRigidNoEligibleComponentLeaf
    (mValue deltaValue alphaValue betaValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  noEligibleComponentLeaf mValue deltaValue alphaValue betaValue
    (pRigidArc raw) pToZ

def apRigidNoEligibleComponentLeaf
    (mValue deltaValue alphaValue betaValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  noEligibleComponentLeaf mValue deltaValue alphaValue betaValue
    (aRigidArc (pRigidArc raw)) pToZ

/-- Four-mode quotient of the remaining no-eligible cells.
The mode selects `(m, alpha, beta) = (0,4,0), (1,4,0), (0,4,1),
(0,5,0)`.  The P tournament is reconstructed exactly in the three
`beta = 0` modes and left explicit in the sole `beta = 1` mode. -/
def noEligibleModeLeaf (mode : BitVec 2)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  let arc := aRigidArc (fun i j =>
    if mode == 2 then raw i j else pRigidArc raw i j)
  let m : BitVec 8 := if mode == 1 then 1 else 0
  let a : BitVec 8 := if mode == 3 then 5 else 4
  let b : BitVec 8 := if mode == 2 then 1 else 0
  commonCore 1 3 arc pToZ &&
    externalMissing 1 3 arc pToZ == m &&
    aMissing arc == 0 && alpha 1 arc == a &&
    internalMissing arc == b && eligibleHCount arc == 0

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
