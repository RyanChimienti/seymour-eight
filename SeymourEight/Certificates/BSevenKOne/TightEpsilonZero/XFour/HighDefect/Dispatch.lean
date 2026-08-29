import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.NearCompression

/-! # Checked dispatch for every high-defect `x = 4` row -/

namespace SeymourEight.ThreeZHighDefectDispatch

open ThreeZHighDefect ThreeZHighDefectCompression ThreeZNearCompression
  ThreeZSaturated ThreeZNearSaturated FiveZExactRisk

theorem m3_a0_b0_false (bits : BitVec 218)
    (h : highDefectCoreAtDefects 3 0 0 bits = true)
    (hDegrees : all 7 (fun p => ThreeZHighDefect.pDegree bits p == 8) = true) : False := by
  have hc := saturated_m3_of_general bits h
  have hFields := h
  simp only [highDefectCoreAtDefects, pCompatibleAtDefect,
    phCompatibleAtDefect, if_pos] at hFields
  have ⟨h4, _⟩ := Bool.and_eq_true_iff.mp hFields
  have ⟨_, hp⟩ := Bool.and_eq_true_iff.mp h4
  have hCompressedDegrees : all 7
      (fun p => ThreeZSaturated.pDegree (saturatedBits bits) p == 8) = true := by
    rw [ThreeZHighDefectCompression.all_eq_true_iff] at hDegrees ⊢
    intro p hpLt
    simpa [ThreeZHighDefectCompression.pDegree_eq bits hp p hpLt] using
      hDegrees p hpLt
  have hCompact := ThreeZSaturated.compactCore_of_full_of_pDegreeEight
    3 17 (saturatedBits bits) (by simpa [saturatedCoreAtMissing] using hc)
    hCompressedDegrees
  have hCompact' : compactSaturatedCoreAtMissing 3
      (saturatedBits bits) = true := by
    simpa [compactSaturatedCoreAtMissing] using hCompact
  rw [saturatedCore_m3_unsat] at hCompact'
  contradiction

theorem m2_a0_b0_false (bits : BitVec 218)
    (h : highDefectCoreAtDefects 2 0 0 bits = true) : False := by
  have hc := saturated_m2_of_general bits h
  rw [saturatedCore_m2_unsat] at hc
  contradiction

theorem m2_a1_b0_false (bits : BitVec 218)
    (h : highDefectCoreAtDefects 2 1 0 bits = true)
    (hDegrees : all 7 (fun p => ThreeZHighDefect.pDegree bits p == 8) = true) : False := by
  have hFields := h
  simp only [highDefectCoreAtDefects, pCompatibleAtDefect,
    phCompatibleAtDefect, if_pos, if_neg (by decide : (1 : Nat) ≠ 0)] at hFields
  have ⟨h4, _⟩ := Bool.and_eq_true_iff.mp hFields
  have ⟨_, hpComplete⟩ := Bool.and_eq_true_iff.mp h4
  have hcompat : phOneComplete bits = true ∨ phComplete bits = true := by
    have hc := (Bool.and_eq_true_iff.mp h).2
    simp only [phCompatibleAtDefect, if_neg (by decide : (1 : Nat) ≠ 0),
      if_pos, Bool.or_eq_true] at hc
    exact hc
  rcases hcompat with hOne | hComplete
  · have hc := near_a1_b0_of_general bits h hOne
    have hpEq := ThreeZNearCompression.pArc_false_eq bits hpComplete
    have hpoEq := ThreeZNearCompression.pToH_true_eq bits hOne
    have hCompressedDegrees : all 7 (fun p =>
        ThreeZNearSaturated.pDegree true false (nearBits bits) p == 8) = true := by
      rw [ThreeZHighDefectCompression.all_eq_true_iff] at hDegrees ⊢
      intro p hpLt
      simpa [ThreeZNearCompression.pDegree_eq true false bits hpEq hpoEq p hpLt]
        using hDegrees p hpLt
    have hCompact := ThreeZNearSaturated.compactCore_of_full_of_pDegreeEight
      true false (nearBits bits) hc hCompressedDegrees
    rw [nearSaturatedCore_a1_b0_unsat] at hCompact
    contradiction
  · have hc := saturated_m2_ph16_of_general bits h hComplete
    have hCompressedDegrees : all 7
        (fun p => ThreeZSaturated.pDegree (saturatedBits bits) p == 8) = true := by
      rw [ThreeZHighDefectCompression.all_eq_true_iff] at hDegrees ⊢
      intro p hpLt
      simpa [ThreeZHighDefectCompression.pDegree_eq bits hpComplete p hpLt]
        using hDegrees p hpLt
    have hCompact := ThreeZSaturated.compactCore_of_full_of_pDegreeEight
      2 16 (saturatedBits bits) hc hCompressedDegrees
    rw [saturatedCore_m2_ph16_unsat] at hCompact
    contradiction

theorem m2_a0_b1_false (bits : BitVec 218)
    (h : highDefectCoreAtDefects 2 0 1 bits = true)
    (hDegrees : all 7 (fun p => ThreeZHighDefect.pDegree bits p == 8) = true) : False := by
  have hFields := h
  simp only [highDefectCoreAtDefects, pCompatibleAtDefect,
    phCompatibleAtDefect, if_pos, if_neg (by decide : (1 : Nat) ≠ 0)] at hFields
  have ⟨h4, _⟩ := Bool.and_eq_true_iff.mp hFields
  have ⟨_, hpOne⟩ := Bool.and_eq_true_iff.mp h4
  have hc := near_a0_b1_of_general bits h
  have hpEq := ThreeZNearCompression.pArc_true_eq bits hpOne
  have hpoEq := ThreeZNearCompression.pToH_false_eq bits
  have hCompressedDegrees : all 7 (fun p =>
      ThreeZNearSaturated.pDegree false true (nearBits bits) p == 8) = true := by
    rw [ThreeZHighDefectCompression.all_eq_true_iff] at hDegrees ⊢
    intro p hpLt
    simpa [ThreeZNearCompression.pDegree_eq false true bits hpEq hpoEq p hpLt]
      using hDegrees p hpLt
  have hCompact := ThreeZNearSaturated.compactCore_of_full_of_pDegreeEight
    false true (nearBits bits) hc hCompressedDegrees
  rw [nearSaturatedCore_a0_b1_unsat] at hCompact
  contradiction

end SeymourEight.ThreeZHighDefectDispatch
