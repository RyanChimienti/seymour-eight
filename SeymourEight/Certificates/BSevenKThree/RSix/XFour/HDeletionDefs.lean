import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CoreDefs

/-!
# Degree-eight deletion constraints for vertices of `H`

When a labelled vertex of `H` has exact outdegree eight and points to the
unique vertex of `Q`, delete that arc.  All remaining first neighbours and
all their outgoing targets are represented by the 18-vertex projected core,
so the degree-seven theorem forces at least seven represented targets.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletion

open Shared.FiniteCore Core

def hDeleteQSecond (arc pToZ : Nat → Nat → Bool)
    (h target : Nat) : Bool :=
  let source := 1 + h
  decide (target ≠ source) &&
    !(decide (target ≠ 14) && coreArc 3 arc pToZ source target) &&
    any 14 fun middle ↦
      decide (middle ≠ source) && decide (middle ≠ target) &&
        coreArc 3 arc pToZ source middle &&
        coreArc 3 arc pToZ middle target

def hDeleteQCount (arc pToZ : Nat → Nat → Bool) (h : Nat) : BitVec 8 :=
  count 18 (hDeleteQSecond arc pToZ h)

def hQDeletionConditions (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 7 fun h ↦
    !(aDegree arc (1 + h) == 8 && aToQ arc (1 + h)) ||
      (7 : BitVec 8).ule (hDeleteQCount arc pToZ h)

def hDeletionLeaf (m delta alphaValue betaValue : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && hQDeletionConditions arc pToZ &&
    externalMissing 1 3 arc pToZ == BitVec.ofNat 8 m &&
    aMissing arc == BitVec.ofNat 8 delta &&
    alpha 1 arc == BitVec.ofNat 8 alphaValue &&
    internalMissing arc == BitVec.ofNat 8 betaValue

def dualHDeletionLeaf
    (m delta alphaValue betaValue etaValue hqValue crossValue : Nat)
    (arc pToZ : Nat → Nat → Bool) : Bool :=
  hDeletionLeaf m delta alphaValue betaValue arc pToZ &&
    etaH arc == BitVec.ofNat 8 etaValue &&
    hQDefect 1 arc == BitVec.ofNat 8 hqValue &&
    crossMissing arc == BitVec.ofNat 8 crossValue

def highAlphaZeroLeaf (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ && hQDeletionConditions arc pToZ &&
    capacityDefect arc pToZ == 6 &&
    (4 : BitVec 8).ule (externalMissing 1 3 arc pToZ) &&
    alpha 1 arc == 0

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletion
