import SeymourEight.Certificates.BSevenKThree.RSix.XFour.StrongDualDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core HDeletion

def capacityTwoToFive (arc pToZ : Nat → Nat → Bool) : Bool :=
  (2 : BitVec 8).ule (capacityDefect arc pToZ) &&
    (capacityDefect arc pToZ).ule 5

/-- All positive-A-defect, alpha-zero cases at capacities two through five. -/
def alphaZeroPositiveDeltaLeaf (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && hQDeletionConditions arc pToZ &&
    capacityTwoToFive arc pToZ && alpha 1 arc == 0 &&
    (1 : BitVec 8).ule (aMissing arc) && (aMissing arc).ule 2

/-- The positive-alpha eligible branch at a fixed positive A-defect. -/
def positiveAlphaDeltaLeaf (delta : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && hQDeletionConditions arc pToZ &&
    capacityTwoToFive arc pToZ &&
    aMissing arc == BitVec.ofNat 8 delta &&
    (1 : BitVec 8).ule (alpha 1 arc) &&
    (1 : BitVec 8).ule (eligibleHCount arc)

def positiveAlphaDeltaOneSlice (alphaLower alphaUpper : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  positiveAlphaDeltaLeaf 1 arc pToZ &&
    (BitVec.ofNat 8 alphaLower).ule (alpha 1 arc) &&
    (alpha 1 arc).ule (BitVec.ofNat 8 alphaUpper)

/-- A delta-zero positive-alpha rectangle, evaluated on the compressed
orientation table for `A`. -/
def aRigidPositiveSlice
    (alphaLower alphaUpper betaLower betaUpper mLower mUpper : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  let arc := Rigid.aRigidArc raw
  commonCore 1 3 arc pToZ && hQDeletionConditions arc pToZ &&
    capacityTwoToFive arc pToZ && aMissing arc == 0 &&
    (BitVec.ofNat 8 alphaLower).ule (alpha 1 arc) &&
    (alpha 1 arc).ule (BitVec.ofNat 8 alphaUpper) &&
    (BitVec.ofNat 8 betaLower).ule (internalMissing arc) &&
    (internalMissing arc).ule (BitVec.ofNat 8 betaUpper) &&
    (BitVec.ofNat 8 mLower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 mUpper) &&
    (1 : BitVec 8).ule (eligibleHCount arc)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
