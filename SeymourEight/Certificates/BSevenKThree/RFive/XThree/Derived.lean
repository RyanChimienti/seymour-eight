import SeymourEight.Certificates.BSevenKThree.RFive.XThree.Tactic

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core

open Shared.FiniteCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The aggregate defect identities and capacity bounds follow from the
local orientation, reachability, and minimum-degree constraints. -/
theorem arithmetic_of_local (y zCount : Nat) (bits : Encoding)
    (hA : orientedA (encodedArc bits) = true)
    (hP : orientedP (encodedArc bits) = true)
    (hPH : orientedPH (encodedArc bits) = true)
    (_hFixed : fixedPivot (encodedArc bits) = true)
    (hX : everyXReached (encodedArc bits) = true)
    (hR : rUnreached (encodedArc bits) = true)
    (hQB : qInB (encodedArc bits) = true)
    (hQR : qReachStatus y (encodedArc bits) = true)
    (hMin : aMinimumAndPivot (encodedArc bits) = true)
    (hPMin : pMinimum zCount (encodedArc bits) = true) :
    ((y = 1 ∧ zCount = 3) ∨ (y = 2 ∧ (zCount = 1 ∨ zCount = 2))) →
      arithmetic y zCount (encodedArc bits) = true := by
  intro hyz
  rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
  simp only [orientedA, orientedP, orientedPH, fixedPivot, everyXReached, rUnreached,
    qInB, qReachStatus, qReached, aMinimumAndPivot, pMinimum, arithmetic, beta, alpha,
    etaH, tau, qDefect, crossMissing, aMissing, externalMissing, capacity,
    totalAOut, totalHToP, totalPToH, totalPOut, totalHToQ, totalHOut,
    totalPAux, totalPDegree, aOut, aPOut, aQOut, aBOut, pOut,
    pHOut, pAuxOut, pDegree, hPOut, hQOut,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all, encodedArc, directedIndex]
      at hA hP hPH _hFixed hX hR hQB hQR hMin hPMin ⊢ <;>
  bv_decide (config := { timeout := 600, acNf := true })

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The sharp king bound for an oriented graph on the five labelled P
vertices. -/
theorem sharpKing_of_orientedP (bits : Encoding)
    (hP : orientedP (encodedArc bits) = true)
    (_hLoops : all 5 (fun p ↦ !encodedArc bits (8 + p) (8 + p)) = true) :
    sharpKing (encodedArc bits) = true := by
  simp only [orientedP, sharpKing, sharpKingLower, beta, totalPOut, pOut,
    pSecondP, strictSecond, reaches, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all, encodedArc, directedIndex]
      at hP _hLoops ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core
