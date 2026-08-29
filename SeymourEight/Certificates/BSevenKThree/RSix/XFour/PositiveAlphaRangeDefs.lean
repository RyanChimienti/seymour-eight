import SeymourEight.Certificates.BSevenKThree.RSix.XFour.EligibleCut
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ReducedCapacityDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Rigid

/-- All positive-alpha, delta-zero capacity-two-through-five cases, strengthened
by the universally valid eligible-vertex capacity cut. -/
def aRigidPositiveAlphaRange
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  aRigidPositiveSlice 1 5 0 5 0 5 raw pToZ &&
    eligibleCapacityCut (aRigidArc raw)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
