import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidXDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

open Core HDeletion

/-- All `delta = alpha = 0` rows, with no restriction on external or internal
missingness.  Four degree-eight H vertices are forced, so one lies in X. -/
def broadRigidXAlphaZeroLeaf (raw pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 (rigidArc raw) pToZ &&
    xQDeletionConditions (rigidArc raw) pToZ &&
    aMissing (rigidArc raw) == 0 && alpha 1 (rigidArc raw) == 0

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
