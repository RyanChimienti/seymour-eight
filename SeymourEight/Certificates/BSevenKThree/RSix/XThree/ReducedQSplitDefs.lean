import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Reduced

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

open Shared.FiniteCore

def hasAToQ (arc : Nat → Nat → Bool) : Bool :=
  any 7 fun i => arc (1 + i) 14

def reducedFiveHasAToQ (bits : Encoding) : Bool :=
  reducedCore 4 bits && hasAToQ (encodedArc bits)

def reducedFiveNoAToQ (bits : Encoding) : Bool :=
  reducedCore 4 bits && !hasAToQ (encodedArc bits)

macro "r6x3_reduced_q_split_simp" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only
    [reducedFiveHasAToQ, reducedFiveNoAToQ, hasAToQ] <;>
  r6x3_reduced_simp)

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core
