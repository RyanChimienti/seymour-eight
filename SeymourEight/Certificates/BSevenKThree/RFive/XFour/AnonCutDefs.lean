import SeymourEight.Certificates.BSevenKThree.RFive.XFour.SharpDefs

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

open Shared.FiniteCore

/-- Lower bound on anonymous out-neighbors of one Q vertex obtained from its
retained indegree and minimum outdegree. -/
def qIndividualAnonymousLower (arc : Nat → Nat → Bool) (q : Nat) : BitVec 8 :=
  if (qIn arc q).ule 7 then 0 else qIn arc q - 7

/-- Anonymous second-neighbor contribution selected by the Q-incidence pattern
of an A source. -/
def selectedAnonLower (arc : Nat → Nat → Bool) (a : Nat) : BitVec 8 :=
  if aToQ arc a 0 then
    if aToQ arc a 1 then qAnonymousSharpLower arc
    else qIndividualAnonymousLower arc 0
  else if aToQ arc a 1 then qIndividualAnonymousLower arc 1
  else 0

def aNonSeymourSelectedAnon (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 8 fun a =>
    (projectedSecondCount 1 arc pToZ a + selectedAnonLower arc a).ult
      (aDegree arc a)

/-- Only the graph-sound premises used by the aggregate anonymous-neighbor
cut.  In particular, this omits the expensive induced and deletion cores. -/
def selectedResidualCore (arc pToZ : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && fixedAOne arc &&
    noPToAOne arc && qInB arc && qReachStatus 2 arc && everyXReached arc &&
    aConditions arc && pConditions 1 arc pToZ &&
    degreeThreeClassification arc && threeInnerWitnesses arc &&
    degreeAndDualConditions 2 arc && aNonSeymourSelectedAnon arc pToZ &&
    orderedP 1 arc pToZ && orderedAClasses arc && orderedQ arc

/-- Counterexample to the aggregate anonymous-neighbor cut. -/
def anonCutCounterexample (arc pToZ : Nat → Nat → Bool) : Bool :=
  selectedResidualCore arc pToZ &&
    !((4 : BitVec 8).ule
      (etaH arc + externalMissing 1 arc pToZ + hQDefect 2 arc))

/-! Counterexample to the independent degree/dual upper cut. -/
def anonUpperCutCounterexample (arc pToZ : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && aConditions arc &&
    pConditions 1 arc pToZ && degreeAndDualConditions 2 arc &&
    !((etaH arc + externalMissing 1 arc pToZ + hQDefect 2 arc).ule 3)

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
