import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.FourAll
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.ParameterBound
import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.Assembly

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourDispatcher

open Shared.FiniteCore Core

private theorem ule_true_of_toNat {a b : BitVec 8} (h : a.toNat ≤ b.toNat) :
    a.ule b = true := by
  simpa [BitVec.ule_eq_decide] using h

theorem externalMissing_ge_seven (bits : Encoding)
    (hInactive : inactiveZZero 4 bits = true) :
    7 ≤ (externalMissing 5 bits).toNat := by
  simp only [inactiveZZero, all_eq_true_iff] at hInactive
  have hRow : ∀ p < 7, (pZOut 5 bits p).toNat ≤ 4 := by
    intro p hp
    have hZero : pToZ bits p 4 = false := by
      simpa using hInactive p hp 0 (by omega)
    have hEq : pZOut 5 bits p = pZOut 4 bits p := by
      simp [pZOut, count, hZero, bitCount]
    rw [hEq, pZOut, toNat_count 4 _ (by omega)]
    calc
      (∑ i ∈ Finset.range 4, (bitCount (pToZ bits p i)).toNat) ≤
          ∑ _i ∈ Finset.range 4, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases pToZ bits p i <;> decide
      _ = 4 := by simp
  have hSum : (∑ i ∈ Finset.range 7, (pZOut 5 bits i).toNat) ≤ 28 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range 7, 4 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hRow i (Finset.mem_range.mp hi)
      _ = 28 := by simp
  have hTotal : (totalPToZ 5 bits).toNat =
      ∑ i ∈ Finset.range 7, (pZOut 5 bits i).toNat := by
    rw [totalPToZ, SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Assembly.toNat_sumCount,
      Nat.mod_eq_of_lt (hSum.trans_lt (by omega))]
  rw [externalMissing, BitVec.toNat_sub, hTotal]
  norm_num [BitVec.toNat_ofNat]
  omega

theorem impossible (bits : Encoding)
    (hCore : FourCore.symmetricCore bits = true) : False := by
  have hCommon : FourCore.commonCore bits = true := by
    have h := hCore
    simp only [FourCore.symmetricCore, Bool.and_eq_true] at h
    exact h.1
  have hOrA : orientedA bits = true := by
    simp only [FourCore.commonCore, Bool.and_eq_true] at hCommon
    aesop
  have hOrP : orientedP bits = true := by
    simp only [FourCore.commonCore, Bool.and_eq_true] at hCommon
    aesop
  have hInactive : inactiveZZero 4 bits = true := by
    simp only [FourCore.commonCore, Bool.and_eq_true] at hCommon
    aesop
  have hPMinFour : pMinimumDegree 4 bits = true := by
    simp only [FourCore.commonCore, Bool.and_eq_true] at hCommon
    aesop
  have hDual : degreeAndDualConditions bits = true := by
    simp only [FourCore.commonCore, Bool.and_eq_true] at hCommon
    aesop
  have hCross : (totalPToH bits + 3 * aMissing bits).ule 12 = true := by
    simp only [degreeAndDualConditions, Bool.and_eq_true] at hDual
    aesop
  have hPMinFive : pMinimumDegree 5 bits = true := by
    simp only [pMinimumDegree, inactiveZZero, all_eq_true_iff] at hPMinFour hInactive ⊢
    intro p hp
    have hZero : pToZ bits p 4 = false := by
      simpa using hInactive p hp 0 (by omega)
    have hEq : pZOut 5 bits p = pZOut 4 bits p := by
      simp [pZOut, count, hZero, bitCount]
    rw [hEq]
    exact hPMinFour p hp
  have hScalar := ParameterBound.scalarDefectBound_of_pMinimum bits
    hOrA hOrP hCross hPMinFive
  have hNat := ParameterBound.scalarDefectBound_toNat bits hScalar
  let m := (externalMissing 5 bits).toNat
  let delta := (aMissing bits).toNat
  let d := (alpha bits + internalMissing bits).toNat
  have hmLo : 7 ≤ m := externalMissing_ge_seven bits hInactive
  have hmHi : m ≤ 12 := by dsimp [m]; omega
  have hdelta : delta ≤ 4 := by dsimp [delta]; omega
  have hd : d ≤ 5 := by
    dsimp [m, delta, d] at hmLo ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hBox : FourCore.boxLeaf 7 12 0 4 0 5 bits = true := by
    have h1 : (7 : BitVec 8).ule (externalMissing 5 bits) = true :=
      ule_true_of_toNat (by simpa [m] using hmLo)
    have h2 : (externalMissing 5 bits).ule (12 : BitVec 8) = true :=
      ule_true_of_toNat (by simpa [m] using hmHi)
    have h3 : (0 : BitVec 8).ule (aMissing bits) = true := ule_true_of_toNat (by simp)
    have h4 : (aMissing bits).ule (4 : BitVec 8) = true :=
      ule_true_of_toNat (by simpa [delta] using hdelta)
    have h5 : (0 : BitVec 8).ule (alpha bits + internalMissing bits) = true :=
      ule_true_of_toNat (by simp)
    have h6 : (alpha bits + internalMissing bits).ule (5 : BitVec 8) = true :=
      ule_true_of_toNat (by simpa [d] using hd)
    simp only [FourCore.boxLeaf, hCore, Bool.true_and, Bool.and_eq_true]
    aesop
  rw [FourCore.all_unsat bits] at hBox
  contradiction

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FourDispatcher
