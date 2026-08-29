import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.CoreDefs
import Mathlib.Tactic.NormNum

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.ParameterBound

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core

set_option maxRecDepth 100000
/-- The total excess of the seven `P` rows is
`12 - (m + 3 * delta + alpha + beta)`. -/
def parameterBound (bits : Encoding) : Bool :=
  (externalMissing 5 bits + (12 - totalPToH bits) +
    internalMissing bits).ule 12

/-- The same aggregate bound in a wide bit-vector, expressed in the natural
defect coordinates so that later dispatch arithmetic cannot wrap. -/
def scalarDefectBound (bits : Encoding) : Bool :=
  ((externalMissing 5 bits).zeroExtend 16 +
    3 * (aMissing bits).zeroExtend 16 +
    (alpha bits).zeroExtend 16 +
    (internalMissing bits).zeroExtend 16).ule 12

set_option maxHeartbeats 10000000 in
-- Summing the seven minimum-degree inequalities gives the aggregate bound.
theorem parameterBound_of_pMinimum (bits : Encoding)
    (hP : orientedP bits = true)
    (hPH : (totalPToH bits).ule 12 = true)
    (hMin : pMinimumDegree 5 bits = true) :
    parameterBound bits = true := by
  simp only [orientedP, pMinimumDegree, parameterBound, externalMissing, internalMissing,
    totalPToZ, totalPToH, totalPOut, pOut, pHOut, pZOut,
    pArc, pToH, pToZ, pDirectedIndex, sumCount, count, bitCount, all]
      at hP hPH hMin ⊢
  bv_decide (config := { timeout := 300, acNf := true })

set_option maxHeartbeats 10000000 in
-- Direct wide formulation of the summed seven-row degree inequality.
theorem scalarDefectBound_of_pMinimum (bits : Encoding)
    (hA : orientedA bits = true)
    (hP : orientedP bits = true)
    (hPH : (totalPToH bits + 3 * aMissing bits).ule 12 = true)
    (hMin : pMinimumDegree 5 bits = true) :
    scalarDefectBound bits = true := by
  simp only [orientedA, orientedP, pMinimumDegree, scalarDefectBound, externalMissing,
    internalMissing, alpha, aMissing, totalPToZ, totalPToH, totalPOut, pOut, pHOut,
    pZOut, aOut, pArc, pToH, pToZ, aArc, pDirectedIndex, hDirectedIndex,
    sumCount, count, bitCount, all]
      at hA hP hPH hMin ⊢
  bv_decide (config := { timeout := 300, acNf := true })

/-- Natural-number view of the wide scalar bound. -/
theorem scalarDefectBound_toNat (bits : Encoding)
    (h : scalarDefectBound bits = true) :
    (externalMissing 5 bits).toNat + 3 * (aMissing bits).toNat +
      (alpha bits).toNat + (internalMissing bits).toNat ≤ 12 := by
  simp only [scalarDefectBound, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_mul] at h
  have hThree : (3 : BitVec 16).toNat = 3 := by decide
  have hTwelve : (12 : BitVec 16).toNat = 12 := by decide
  rw [hThree, hTwelve] at h
  have hm := (externalMissing 5 bits).isLt
  have hdelta := (aMissing bits).isLt
  have halpha := (alpha bits).isLt
  have hbeta := (internalMissing bits).isLt
  norm_num at h hm hdelta halpha hbeta
  omega

set_option maxHeartbeats 1000000 in
-- Rewrite the aggregate row bound in the natural defect coordinates.
theorem scalar_defect_bound (bits : Encoding)
    (hCross : (totalPToH bits + 3 * aMissing bits).ule 12 = true)
    (hBound : parameterBound bits = true) :
    (externalMissing 5 bits + 3 * aMissing bits + alpha bits +
      internalMissing bits).ule 12 = true := by
  simp only [parameterBound, alpha] at hBound ⊢
  generalize externalMissing 5 bits = m at hBound ⊢
  generalize totalPToH bits = ph at hCross hBound ⊢
  generalize aMissing bits = delta at hCross ⊢
  generalize internalMissing bits = beta at hBound ⊢
  bv_decide

set_option maxHeartbeats 10000000 in
-- The two largest coarse parent families have internal defect at most nine.
theorem hard_defect_le_nine (bits : Encoding)
    (hP : orientedP bits = true)
    (hPH : (totalPToH bits).ule 12 = true)
    (hMin : pMinimumDegree 5 bits = true)
    (hm : (3 : BitVec 8).ule (externalMissing 5 bits) = true)
    (hDelta : aMissing bits = 0) :
    (alpha bits + internalMissing bits).ule 9 = true := by
  generalize hDeltaVar : aMissing bits = delta at hDelta ⊢
  simp only [orientedP, pMinimumDegree, externalMissing, internalMissing,
    alpha, totalPToZ, totalPToH, totalPOut, pOut, pHOut, pZOut,
    pArc, pToH, pToZ, pDirectedIndex, sumCount, count, bitCount, all]
      at hP hPH hMin hm hDelta ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.ParameterBound
