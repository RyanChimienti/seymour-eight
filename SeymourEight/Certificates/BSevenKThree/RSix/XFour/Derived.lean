import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Tactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

open Shared.FiniteCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The aggregate `H` inequalities are Boolean consequences of orientation
and the pointwise `A` degree bounds, so they need no graph-level counting
bridge and are certified only once. -/
theorem degreeAndDual_of_local (y : Nat) (arc : Nat → Nat → Bool)
    (hy : y = 0 ∨ y = 1)
    (hA : orientedA arc = true) (hPH : orientedPH arc = true)
    (hFixed : fixedAOne arc = true) (hX : everyXReached arc = true)
    (hQ : qReachStatus y arc = true)
    (hMin : aConditions arc = true) :
    degreeAndDualConditions y arc = true := by
  rcases hy with rfl | rfl <;>
  simp only [orientedA, orientedPH, fixedAOne, everyXReached, qReachStatus,
    aConditions, degreeAndDualConditions,
    aMissing, alpha, etaH, hQDefect, crossMissing, totalAOut, totalPToH,
    totalHToP, totalHToQ, totalHOut, aDegree, aBOut, aOut, aPOut, pHOut,
    hPOut, aArc, aToP, pToA, aToQ, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all] at hA hPH hFixed hX hQ hMin ⊢ <;>
  bv_decide (config := { timeout := 300, acNf := true })

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The sharp almost-tournament king bound for the six labelled `P`
vertices. -/
theorem sharpKing_of_orientedP (arc : Nat → Nat → Bool)
    (hP : orientedP arc = true) : sharpKing arc = true := by
  simp only [orientedP, sharpKing, sharpKingLower, internalMissing, totalPOut,
    pOut, pSecondPCount, strictSecondLocal, reachesLocal, pArc,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all] at hP ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
