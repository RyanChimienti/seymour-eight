import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.HighDefect.Range
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.HighDefect.RangeBridge

namespace SeymourEight.FourZHighDefect

open FiveZExactRisk

/-- The graph-facing exact parameters lie in one aggregate Boolean range. -/
theorem highDefectCoreAtMissingDegree_unsat (missing degreeSum : Nat)
    (hMissingLower : 2 ≤ missing) (hMissingUpper : missing ≤ 7)
    (hDegreeLower : 56 ≤ degreeSum)
    (hDegreeUpper : degreeSum ≤ 63 - missing) (bits : BitVec 218) :
    highDefectCoreAtMissingDegree missing degreeSum bits = false := by
  by_contra hNotFalse
  have hExact : highDefectCoreAtMissingDegree missing degreeSum bits = true :=
    Bool.eq_true_of_not_eq_false hNotFalse
  have hExactParts := hExact
  simp only [highDefectCoreAtMissingDegree, highDefectCoreAtMissing,
    Bool.and_eq_true, decide_eq_true_eq] at hExactParts
  have hCore : highDefectCore bits = true := hExactParts.1.1
  have hParts := hCore
  simp only [highDefectCore, Bool.and_eq_true] at hParts
  have hCompact := compactAOneDeletionExpands_of_fixed_of_expands bits
    hParts.1.1.1.1.1.1 hParts.1.1.1.1.1.2
  have hMissingEq : totalMissingPZ bits = BitVec.ofNat 8 missing := by
    exact hExactParts.1.2
  have hDegreeEq : pDegreeSum bits = BitVec.ofNat 8 degreeSum := by
    exact hExactParts.2
  have hMissingUpperBV : (totalMissingPZ bits).ule 7 = true := by
    rw [hMissingEq]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : missing < 256)]
    exact hMissingUpper
  have hDegreeLowerBV : (56 : BitVec 8).ule (pDegreeSum bits) = true := by
    rw [hDegreeEq]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : degreeSum < 256)]
    exact hDegreeLower
  have hCapacityBV :
      (pDegreeSum bits + totalMissingPZ bits).ule 63 = true := by
    have hSum : degreeSum + missing ≤ 63 := by omega
    rw [hDegreeEq, hMissingEq]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    norm_num [Nat.mod_eq_of_lt (by omega : degreeSum < 256),
      Nat.mod_eq_of_lt (by omega : missing < 256),
      Nat.mod_eq_of_lt (by omega : degreeSum + missing < 256)]
    exact hSum
  have hRange : highDefectRangeCore bits = true := by
    simp only [highDefectRangeCore, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hParts.1.1.1.1.1.1, hCompact⟩,
      hMissingUpperBV⟩, hParts.1.1.1.1.2⟩, hParts.1.1.1.2⟩,
      hParts.1.1.2⟩, hParts.1.2⟩, hParts.2⟩, hDegreeLowerBV⟩,
      hCapacityBV⟩
  rw [highDefectRangeCore_unsat bits] at hRange
  contradiction

end SeymourEight.FourZHighDefect
