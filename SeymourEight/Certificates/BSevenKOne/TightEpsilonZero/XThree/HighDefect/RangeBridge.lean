import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.HighDefect.RangeDefs
import Mathlib.Tactic.IntervalCases

namespace SeymourEight.FourZHighDefect

open FiveZExactRisk

set_option maxRecDepth 100000

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

set_option maxHeartbeats 5000000 in
theorem deletionExpansionCount_eq_compact (bits : BitVec 218)
    (hNoR : all 3 (fun q => !aArc bits 1 (q + 5)) = true)
    (deleted : Nat) (hd : deleted < 8) :
    deletionExpansionCount bits deleted =
      compactDeletionExpansionCount bits deleted := by
  have hR5 := (all_eq_true_iff_range 3 _).mp hNoR 0 (by omega)
  have hR6 := (all_eq_true_iff_range 3 _).mp hNoR 1 (by omega)
  have hR7 := (all_eq_true_iff_range 3 _).mp hNoR 2 (by omega)
  simp only [Bool.not_eq_true'] at hR5 hR6 hR7
  interval_cases deleted <;>
    simp (config := { maxSteps := 1000000 })
      [deletionExpansionCount, deletionReached, retainedAfterDelete,
        compactDeletionExpansionCount, reachedFromRetainedNeighbor,
        deletionExternalTarget, aOneNeighbor, coreArc, pToA, count, any,
        hR5, hR6, hR7]
  all_goals ac_rfl

theorem compactAOneDeletionExpands_of_fixed_of_expands (bits : BitVec 218)
    (hFixed : fixedStructure bits = true)
    (hExpands : aOneDeletionExpands bits = true) :
    compactAOneDeletionExpands bits = true := by
  have hNoR : all 3 (fun q => !aArc bits 1 (q + 5)) = true := by
    simp_all only [fixedStructure, Bool.and_eq_true]
  rw [compactAOneDeletionExpands, all_eq_true_iff_range]
  rw [aOneDeletionExpands, all_eq_true_iff_range] at hExpands
  intro deleted hd
  simpa [deletionExpansionCount_eq_compact bits hNoR deleted hd] using
    hExpands deleted hd

end SeymourEight.FourZHighDefect
