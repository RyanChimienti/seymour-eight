import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionDefs

/-!
# H-to-Q deletion constraints restricted to the four X vertices

In the rigid `alpha = delta = 0` rows at least four of the seven H vertices
have degree eight.  Since A1 has only three vertices, it is enough to retain
the deletion circuits for X (H indices 3 through 6).
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletion

open Shared.FiniteCore Core

def xQDeletionConditions (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 4 fun x ↦
    let h := 3 + x
    !(aDegree arc (1 + h) == 8 && aToQ arc (1 + h)) ||
      (7 : BitVec 8).ule (hDeleteQCount arc pToZ h)

def xHDeletionLeaf (m delta alphaValue betaValue : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && xQDeletionConditions arc pToZ &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc == BitVec.ofNat 8 alphaValue &&
    internalMissing arc == BitVec.ofNat 8 betaValue

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletion
