import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.XHDeletionDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

open HDeletion

def rigidXHDeletionLeaf (m alphaValue betaValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  xHDeletionLeaf m 0 alphaValue betaValue (rigidArc raw) pToZ

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
