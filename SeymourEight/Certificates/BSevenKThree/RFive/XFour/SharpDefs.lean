import SeymourEight.Certificates.BSevenKThree.RFive.XFour.CoreDefs

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

open Shared.FiniteCore

/-- The exact lower bound obtained from `11 ≤ d + 2 |U|`, where `U` is the
set of anonymous out-neighbors of the two `Q` vertices.  It is factored out of
`commonCore` because only the `y ≥ 2` families require it. -/
def qAnonymousSharpLower (arc : Nat → Nat → Bool) : BitVec 8 :=
  let d := hQDefect 2 arc + qMissing arc
  if d == 0 then 6 else if d.ule 2 then 5 else if d.ule 4 then 4
  else if d.ule 6 then 3 else if d.ule 8 then 2
  else if d.ule 10 then 1 else 0

def aNonSeymourSharp (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 8 fun a ↦
    (projectedSecondCount 1 arc pToZ a +
      (if reachesBothQFromA arc a then qAnonymousSharpLower arc else 0)).ult
        (aDegree arc a)

def pNonSeymourSharp (arc pToZ : Nat → Nat → Bool) : Bool :=
  all 5 fun p ↦
    (projectedSecondCount 1 arc pToZ (8 + p) +
      (if reachesBothQFromP arc p then qAnonymousSharpLower arc else 0)).ult
        (pDegree 1 arc pToZ p)

def sharpResidualCore (arc pToZ : Nat → Nat → Bool) : Bool :=
  commonCore 2 1 arc pToZ && aNonSeymourSharp arc pToZ &&
    pNonSeymourSharp arc pToZ

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
