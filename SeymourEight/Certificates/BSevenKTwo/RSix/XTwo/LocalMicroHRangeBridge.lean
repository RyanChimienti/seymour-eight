import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHDegreeSum
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHRangeDefs

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Shared.FiniteCore

theorem microHEffectiveLowPHMissing_to_selected
    (c bound maxM m : Nat) (bits : Encoding)
    (hmMax : m ≤ maxM) (hmax : maxM < 4)
    (h : microHEffectiveLowPHMissing c bound m bits = true) :
    microHEffectiveLowPHSelectedMissing c bound maxM
      (BitVec.ofNat 2 m) bits = true := by
  have hm4 : m < 4 := lt_of_le_of_lt hmMax hmax
  have hWidth : (BitVec.ofNat 2 m).zeroExtend 8 = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hm4]
  simp only [microHEffectiveLowPHMissing, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hCore, hEff⟩, hDist⟩, hPH⟩, hMissing⟩
  have hMin : all 6 (fun p => (8 : BitVec 8).ule
      (pOut bits p + pHOut bits p + pEOut 5 bits p)) = true := by
    simp only [microHCore, Bool.and_eq_true] at hCore
    aesop
  have hDegree := pMinimumDegreeFive_implies_degreeSum bits
  simp only [hMin, Bool.not_true, Bool.false_or] at hDegree
  have hEffSelected : all 6
      (pEffectiveConditionFiveSelected (BitVec.ofNat 2 m) bits) = true := by
    rw [all_eq_true_iff] at hEff ⊢
    intro p hp
    have hpEff := hEff p hp
    simpa [pEffectiveConditionFiveAt, pEffectiveConditionFiveSelected,
      hWidth] using hpEff
  have hSelectedMax : (BitVec.ofNat 2 m).ule
      (BitVec.ofNat 2 maxM) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm4,
      Nat.mod_eq_of_lt hmax, hmMax]
  simp only [microHEffectiveLowPHSelectedMissing, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hCore, hEffSelected⟩, hDist⟩, hPH⟩,
    by simpa [hWidth] using hMissing⟩, hSelectedMax⟩, hDegree⟩

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
