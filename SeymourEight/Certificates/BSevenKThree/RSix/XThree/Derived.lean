import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Tactic

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

open Shared.FiniteCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The aggregate `H` arithmetic is a finite consequence of the local
orientation, reachability, and minimum-degree conditions. -/
theorem arithmetic_of_local (zCount : Nat) (arc : Nat → Nat → Bool)
    (hA : orientedA arc = true) (hAPQ : orientedAPQ arc = true)
    (hFixed : fixedPivot arc = true) (hX : everyXReached arc = true)
    (hR : rUnreached arc = true) (hQ : qReached arc = true)
    (hMin : aMinimumAndPivot arc = true) :
    arithmetic zCount arc = true := by
  simp only [orientedA, orientedAPQ, fixedPivot, everyXReached, rUnreached,
    qReached, aMinimumAndPivot, arithmetic, degreeGain, qDefect, alpha,
    tau, etaH, crossMissing, aMissing, totalAOut, totalHToP, totalPToH,
    totalHOut, aOut, aPOut, aBOut, pHOut, hPOut,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all] at hA hAPQ hFixed hX hR hQ hMin ⊢
  bv_decide (config := { timeout := 600, acNf := true })

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The sharp almost-tournament king bound for the six labelled `P`
vertices. -/
theorem sharpKing_of_orientedP (arc : Nat → Nat → Bool)
    (hP : orientedP arc = true)
    (hLoops : all 6 (fun p => !arc (8 + p) (8 + p)) = true) :
    sharpKing arc = true := by
  simp only [orientedP, sharpKing, sharpKingLower, beta, totalPOut, pOut,
    pSecondP, strictSecond, reaches, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all] at hP hLoops ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core
