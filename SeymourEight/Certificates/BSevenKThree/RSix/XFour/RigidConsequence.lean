import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

open Shared.FiniteCore Core

theorem alphaZeroPremise_agrees (arc : Nat → Nat → Bool) :
    alphaZeroPremise arc = true → alphaZeroAgreement arc = true := by
  intro h
  simp only [alphaZeroPremise, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hFixed, hNoP⟩, hQ⟩, hHP⟩
  rw [alphaZeroAgreement, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [alphaZeroArc]
  split
  · rename_i hBranch
    have hi0 : i = 0 := hBranch.1
    subst i
    rw [fixedAOne, all_eq_true_iff] at hFixed
    have hf : arc 0 j =
        decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 14) := by
      simpa only [beq_iff_eq] using hFixed j hj
    rw [hf]
    simp
  split
  · rename_i hBranch
    rw [noPToAOne, all_eq_true_iff] at hNoP
    have hp := hNoP (i - 8) (by omega)
    have hiEq : 8 + (i - 8) = i := by omega
    have hjEq : j = 0 := by omega
    subst j
    simpa [pToA, hiEq] using hp
  split
  · simp
  split
  · rename_i hBranch
    rw [hpDirectionsComplete, all_eq_true_iff] at hHP
    have hp := hHP (i - 8) (by omega)
    rw [all_eq_true_iff] at hp
    have hh := hp (j - 1) (by omega)
    have hiEq : 8 + (i - 8) = i := by omega
    have hjEq : 1 + (j - 1) = j := by omega
    simp only [pToA, aToP, hiEq, hjEq, beq_iff_eq] at hh
    cases hij : arc i j <;> cases hji : arc j i <;> simp_all
  split
  · rename_i hBranch
    rw [hQComplete, all_eq_true_iff] at hQ
    have hh := hQ (i - 1) (by omega)
    have hiEq : 1 + (i - 1) = i := by omega
    have hjEq : j = 14 := hBranch.2.2
    simpa [aToQ, hiEq, hjEq] using hh
  simp

theorem rigidPremise_agrees (arc : Nat → Nat → Bool) :
    rigidPremise arc = true → rigidAgreement arc = true := by
  intro h
  simp only [rigidPremise, Bool.and_eq_true] at h
  rcases h with ⟨hAlphaZero, hA⟩
  have hAlphaAgree := alphaZeroPremise_agrees arc hAlphaZero
  rw [rigidAgreement, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [rigidArc]
  split
  · rename_i hBothA
    rw [aDirectionsComplete, all_eq_true_iff] at hA
    have hiA := hA i hBothA.1
    simp only [Bool.and_eq_true] at hiA
    rw [all_eq_true_iff] at hiA
    have hij := hiA.2 j hBothA.2
    by_cases hi0 : i = 0
    · simp only [hi0, if_true]
      simp only [alphaZeroPremise, Bool.and_eq_true] at hAlphaZero
      have hFixed := hAlphaZero.1.1.1
      rw [fixedAOne, all_eq_true_iff] at hFixed
      have hf : arc 0 j =
          decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 14) := by
        simpa only [beq_iff_eq] using hFixed j (by omega)
      rw [hf]
      simp
      omega
    · rw [if_neg hi0]
      by_cases hj0 : j = 0
      · rw [if_pos hj0]
        simp only [alphaZeroPremise, Bool.and_eq_true] at hAlphaZero
        have hFixed := hAlphaZero.1.1.1
        rw [fixedAOne, all_eq_true_iff] at hFixed
        have hFixedI := hFixed i (by omega)
        simp only [aArc] at hij
        cases hii : arc i 0 <;> cases h0i : arc 0 i <;> simp_all <;> omega
      · rw [if_neg hj0]
        by_cases hijEq : i = j
        · subst j
          simpa [aArc] using hiA.1
        · rw [if_neg hijEq]
          by_cases hijLt : i < j
          · simp [hijLt]
          · rw [if_neg hijLt]
            have hji : j < i := by omega
            simp only [hijEq, decide_false, Bool.false_or, aArc,
              beq_iff_eq] at hij
            cases hij' : arc i j <;> cases hji' : arc j i <;> simp_all
  · rw [alphaZeroAgreement, all_eq_true_iff] at hAlphaAgree
    have hi' := hAlphaAgree i hi
    rw [all_eq_true_iff] at hi'
    exact hi' j hj

theorem aRigidPremise_agrees (arc : Nat → Nat → Bool) :
    aRigidPremise arc = true → aRigidAgreement arc = true := by
  intro h
  simp only [aRigidPremise, fixedPremise, Bool.and_eq_true] at h
  rcases h with ⟨⟨hFixed, hNoP⟩, hA⟩
  rw [aRigidAgreement, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [aRigidArc]
  split
  · rename_i hBothA
    rw [aDirectionsComplete, all_eq_true_iff] at hA
    have hiA := hA i hBothA.1
    simp only [Bool.and_eq_true] at hiA
    rw [all_eq_true_iff] at hiA
    have hij := hiA.2 j hBothA.2
    by_cases hi0 : i = 0
    · simp only [hi0, if_true]
      rw [fixedAOne, all_eq_true_iff] at hFixed
      have hf : arc 0 j =
          decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 14) := by
        simpa only [beq_iff_eq] using hFixed j (by omega)
      rw [hf]
      simp
      omega
    · rw [if_neg hi0]
      by_cases hj0 : j = 0
      · rw [if_pos hj0]
        rw [fixedAOne, all_eq_true_iff] at hFixed
        have hFixedI := hFixed i (by omega)
        simp only [aArc] at hij
        cases hii : arc i 0 <;> cases h0i : arc 0 i <;> simp_all <;> omega
      · rw [if_neg hj0]
        by_cases hijEq : i = j
        · subst j
          simpa [aArc] using hiA.1
        · rw [if_neg hijEq]
          by_cases hijLt : i < j
          · simp [hijLt]
          · rw [if_neg hijLt]
            have hji : j < i := by omega
            simp only [hijEq, decide_false, Bool.false_or, aArc,
              beq_iff_eq] at hij
            cases hij' : arc i j <;> cases hji' : arc j i <;> simp_all
  · rw [fixedArc]
    split
    · rename_i hBranch
      have hi0 : i = 0 := hBranch.1
      subst i
      rw [fixedAOne, all_eq_true_iff] at hFixed
      have hf : arc 0 j =
          decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 14) := by
        simpa only [beq_iff_eq] using hFixed j hj
      rw [hf]
      simp
    split
    · rename_i hBranch
      rw [noPToAOne, all_eq_true_iff] at hNoP
      have hp := hNoP (i - 8) (by omega)
      have hiEq : 8 + (i - 8) = i := by omega
      have hjEq : j = 0 := by omega
      subst j
      simpa [pToA, hiEq] using hp
    simp

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
