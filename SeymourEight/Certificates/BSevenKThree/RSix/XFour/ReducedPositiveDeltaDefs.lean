import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ReducedCapacityDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core HDeletion

/-- The entire positive A-defect portion of capacities two through five.
The final three inequalities are redundant natural-number consequences of
the capacity identity, but make those bounds explicit to the SAT solver. -/
def reducedPositiveDeltaLeaf (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && hQDeletionConditions arc pToZ &&
    capacityTwoToFive arc pToZ &&
    (1 : BitVec 8).ule (aMissing arc) && (aMissing arc).ule 2 &&
    (externalMissing 1 3 arc pToZ).ule 5 &&
    (alpha 1 arc + internalMissing arc).ule 3

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
