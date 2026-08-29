import SeymourEight.Certificates.BSevenKThree.RSix.XFour.StrongDualDefs

/-!
# A cheap counting consequence for eligible H vertices

If all labelled A vertices have degree at least eight, then the total H
degree excess bounds the number of H vertices whose degree is greater than
eight.  The H--Q defect separately bounds those which do not point to Q.
Consequently at least `7 - etaH - hQDefect` H vertices have degree exactly
eight and point to Q.  Keeping this as a small isolated Boolean certificate
lets the larger obstruction certificates use the bound for propagation.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core Shared.FiniteCore

def eligibleConsequence (arc : Nat → Nat → Bool) : Bool :=
  !aConditions arc ||
    !(etaH arc + hQDefect 1 arc).ule 7 ||
    (7 - etaH arc - hQDefect 1 arc).ule (eligibleHCount arc)

def etaBoundConsequence (arc : Nat → Nat → Bool) : Bool :=
  !aConditions arc || (etaH arc).ule 49

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem eligibleConsequence_true (arc : Nat → Nat → Bool) :
    eligibleConsequence arc = true := by
  simp (config := { maxSteps := 1000000 }) only
    [eligibleConsequence, eligibleHCount, aConditions, etaH, totalHOut,
      hQDefect, totalHToQ, aDegree, hPOut, aBOut, aPOut, aOut, aToQ,
      aToP, aArc, sumCount, count, bitCount, all]
  bv_decide (config := { timeout := 1200, acNf := true })

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem etaBoundConsequence_true (arc : Nat → Nat → Bool) :
    etaBoundConsequence arc = true := by
  simp (config := { maxSteps := 1000000 }) only
    [etaBoundConsequence, aConditions, etaH, totalHOut, aDegree, hPOut,
      aBOut, aPOut, aOut, aToQ, aToP, aArc, sumCount, count, bitCount, all]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
