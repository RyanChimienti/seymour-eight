import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.SaturatedCoreDefs
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.NearSaturatedCoreDefs
import Mathlib.Tactic.IntervalCases

namespace SeymourEight

open FiveZExactRisk

private theorem all_eq_true_iff_range (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · have : i = n := by omega
          simpa [this] using hn
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

namespace ThreeZSaturated

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000 in
theorem deletionExpansionCount_eq_compact (bits : Encoding)
    (hNoR : all 2 (fun q => !aArc bits 1 (q + 6)) = true)
    (deleted : Nat) (hd : deleted < 8) :
    deletionExpansionCount bits deleted =
      compactDeletionExpansionCount bits deleted := by
  have hR6 := (all_eq_true_iff_range 2 _).mp hNoR 0 (by omega)
  have hR7 := (all_eq_true_iff_range 2 _).mp hNoR 1 (by omega)
  simp only [Bool.not_eq_true'] at hR6 hR7
  interval_cases deleted <;>
    simp (config := { maxSteps := 1000000 })
      [deletionExpansionCount, deletionReached, retainedAfterDelete,
        compactDeletionExpansionCount, reachedFromRetainedNeighbor,
        deletionExternalTarget, aOneNeighbor, coreArc, pToA, count, any,
        hR6, hR7]
  all_goals ac_rfl

theorem compactAOneDeletionExpands_of_fixed_of_expands (bits : Encoding)
    (hFixed : fixedStructure bits = true)
    (hExpands : aOneDeletionExpands bits = true) :
    compactAOneDeletionExpands bits = true := by
  have hNoR : all 2 (fun q => !aArc bits 1 (q + 6)) = true := by
    simp_all only [fixedStructure, Bool.and_eq_true]
  rw [compactAOneDeletionExpands, all_eq_true_iff_range]
  rw [aOneDeletionExpands, all_eq_true_iff_range] at hExpands
  intro deleted hd
  simpa [deletionExpansionCount_eq_compact bits hNoR deleted hd] using
    hExpands deleted hd

theorem compactCore_of_full_of_pDegreeEight (missing pToHTotal : Nat)
    (bits : Encoding)
    (hFull : saturatedCoreAtMissingPToH missing pToHTotal bits = true)
    (hDegrees : all 7 (fun p => pDegree bits p == 8) = true) :
    compactSaturatedCoreAtMissingPToH missing pToHTotal bits = true := by
  simp only [saturatedCoreAtMissingPToH, Bool.and_eq_true] at hFull
  rcases hFull with ⟨⟨⟨⟨⟨⟨⟨hFixed, hExpands⟩, hToH⟩, hMissing⟩,
    hNonA⟩, hNonPOld⟩, hOrderedP⟩, hOrderedZ⟩
  have hCompact := compactAOneDeletionExpands_of_fixed_of_expands bits
    hFixed hExpands
  simp only [compactSaturatedCoreAtMissingPToH, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hFixed, hCompact⟩, hToH⟩, hMissing⟩, hDegrees⟩,
    hNonA⟩, hNonPOld⟩, hOrderedP⟩, hOrderedZ⟩

end ThreeZSaturated

namespace ThreeZNearSaturated

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000 in
theorem deletionExpansionCount_eq_compact (alphaOne betaOne : Bool)
    (bits : Encoding)
    (hNoR : all 2 (fun q => !aArc bits 1 (q + 6)) = true)
    (deleted : Nat) (hd : deleted < 8) :
    deletionExpansionCount alphaOne betaOne bits deleted =
      compactDeletionExpansionCount alphaOne betaOne bits deleted := by
  have hR6 := (all_eq_true_iff_range 2 _).mp hNoR 0 (by omega)
  have hR7 := (all_eq_true_iff_range 2 _).mp hNoR 1 (by omega)
  simp only [Bool.not_eq_true'] at hR6 hR7
  interval_cases deleted <;>
    simp (config := { maxSteps := 1000000 })
      [deletionExpansionCount, deletionReached, retainedAfterDelete,
        compactDeletionExpansionCount, reachedFromRetainedNeighbor,
        deletionExternalTarget, aOneNeighbor, coreArc, pToA, count, any,
        hR6, hR7]
  all_goals ac_rfl

theorem compactAOneDeletionExpands_of_fixed_of_expands
    (alphaOne betaOne : Bool) (bits : Encoding)
    (hFixed : fixedStructure alphaOne betaOne bits = true)
    (hExpands : aOneDeletionExpands alphaOne betaOne bits = true) :
    compactAOneDeletionExpands alphaOne betaOne bits = true := by
  have hNoR : all 2 (fun q => !aArc bits 1 (q + 6)) = true := by
    simp_all only [fixedStructure, Bool.and_eq_true]
  rw [compactAOneDeletionExpands, all_eq_true_iff_range]
  rw [aOneDeletionExpands, all_eq_true_iff_range] at hExpands
  intro deleted hd
  simpa [deletionExpansionCount_eq_compact alphaOne betaOne bits hNoR deleted hd]
    using hExpands deleted hd

theorem compactCore_of_full_of_pDegreeEight (alphaOne betaOne : Bool)
    (bits : Encoding)
    (hFull : nearSaturatedCore alphaOne betaOne bits = true)
    (hDegrees : all 7
      (fun p => pDegree alphaOne betaOne bits p == 8) = true) :
    compactNearSaturatedCore alphaOne betaOne bits = true := by
  simp only [nearSaturatedCore, Bool.and_eq_true] at hFull
  rcases hFull with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPhCode, hPCode⟩, hFixed⟩, hExpands⟩,
    hToH⟩, hToP⟩, hMissing⟩, hNonA⟩, hNonPOld⟩, hOrderedP⟩, hOrderedZ⟩
  have hCompact := compactAOneDeletionExpands_of_fixed_of_expands
    alphaOne betaOne bits hFixed hExpands
  simp only [compactNearSaturatedCore, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPhCode, hPCode⟩, hFixed⟩, hCompact⟩,
    hToH⟩, hToP⟩, hMissing⟩, hDegrees⟩, hNonA⟩, hNonPOld⟩,
    hOrderedP⟩, hOrderedZ⟩

end ThreeZNearSaturated

end SeymourEight
