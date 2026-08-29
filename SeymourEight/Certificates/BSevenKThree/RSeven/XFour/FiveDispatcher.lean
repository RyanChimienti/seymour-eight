import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.ParameterBound
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.DeltaTwoPlus
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.DeltaZeroAll
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.DeltaOneAll

set_option linter.style.header false

/-!
# Exhaustive dispatcher for the five-target core

The scalar capacity bound reduces the core to a small natural-parameter
simplex, which is dispatched to the corresponding obstruction theorems.
-/

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FiveDispatcher

open Core SymmetricCore RemainingCore

private theorem ule_true_of_toNat {a b : BitVec 8} (h : a.toNat ≤ b.toNat) :
    a.ule b = true := by
  simpa only [BitVec.ule_eq_decide, decide_eq_true_eq] using h

private theorem boxLeaf_true (bits : Encoding)
    (hCore : symmetricCore bits = true)
    (mLo mHi deltaLo deltaHi dLo dHi : Nat)
    (hmLo : mLo ≤ (externalMissing 5 bits).toNat)
    (hmHi : (externalMissing 5 bits).toNat ≤ mHi)
    (hdeltaLo : deltaLo ≤ (aMissing bits).toNat)
    (hdeltaHi : (aMissing bits).toNat ≤ deltaHi)
    (hdLo : dLo ≤ (alpha bits + internalMissing bits).toNat)
    (hdHi : (alpha bits + internalMissing bits).toNat ≤ dHi)
    (hmLoSmall : mLo < 256) (hmHiSmall : mHi < 256)
    (hdeltaLoSmall : deltaLo < 256) (hdeltaHiSmall : deltaHi < 256)
    (hdLoSmall : dLo < 256) (hdHiSmall : dHi < 256) :
    boxLeaf mLo mHi deltaLo deltaHi dLo dHi bits = true := by
  have h1 : (BitVec.ofNat 8 mLo).ule (externalMissing 5 bits) = true := by
    apply ule_true_of_toNat
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmLoSmall] using hmLo
  have h2 : (externalMissing 5 bits).ule (BitVec.ofNat 8 mHi) = true := by
    apply ule_true_of_toNat
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmHiSmall] using hmHi
  have h3 : (BitVec.ofNat 8 deltaLo).ule (aMissing bits) = true := by
    apply ule_true_of_toNat
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdeltaLoSmall] using hdeltaLo
  have h4 : (aMissing bits).ule (BitVec.ofNat 8 deltaHi) = true := by
    apply ule_true_of_toNat
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdeltaHiSmall] using hdeltaHi
  have h5 : (BitVec.ofNat 8 dLo).ule (alpha bits + internalMissing bits) = true := by
    apply ule_true_of_toNat
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdLoSmall] using hdLo
  have h6 : (alpha bits + internalMissing bits).ule (BitVec.ofNat 8 dHi) = true := by
    apply ule_true_of_toNat
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdHiSmall] using hdHi
  simp only [boxLeaf, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hCore, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

private theorem directScalarCut_true (bits : Encoding)
    (hScalar : ParameterBound.scalarDefectBound bits = true) :
    directScalarCut bits = true := by
  simp only [ParameterBound.scalarDefectBound, directScalarCut] at hScalar ⊢
  generalize externalMissing 5 bits = m at hScalar ⊢
  generalize aMissing bits = delta at hScalar ⊢
  generalize alpha bits = a at hScalar ⊢
  generalize internalMissing bits = b at hScalar ⊢
  bv_decide

theorem impossible (bits : Encoding)
    (hCore : symmetricCore bits = true) : False := by
  have hFacts := hCore
  simp only [symmetricCore, Core.commonCore, Bool.and_eq_true] at hFacts
  have hOrA : orientedA bits = true := by aesop
  have hOrP : orientedP bits = true := by aesop
  have hPMin : pMinimumDegree 5 bits = true := by aesop
  have hCross : (totalPToH bits + 3 * aMissing bits).ule 12 = true := by
    have hDual : degreeAndDualConditions bits = true := by aesop
    simp only [degreeAndDualConditions, Bool.and_eq_true] at hDual
    exact hDual.1.1.2
  have hScalar := ParameterBound.scalarDefectBound_of_pMinimum bits
    hOrA hOrP hCross hPMin
  have hDirectCut := directScalarCut_true bits hScalar
  have hBound := ParameterBound.scalarDefectBound_toNat bits hScalar
  let m := (externalMissing 5 bits).toNat
  let delta := (aMissing bits).toNat
  let d := (alpha bits + internalMissing bits).toNat
  have hdNat : d = (alpha bits).toNat + (internalMissing bits).toNat := by
    dsimp [d]
    have ha := (alpha bits).isLt
    have hb := (internalMissing bits).isLt
    exact Nat.mod_eq_of_lt (by omega)
  have hCapacity : m + 3 * delta + d ≤ 12 := by
    dsimp [m, delta]
    rw [hdNat]
    omega
  have hBox : ∀ mLo mHi deltaLo deltaHi dLo dHi,
      mLo ≤ m → m ≤ mHi → deltaLo ≤ delta → delta ≤ deltaHi →
      dLo ≤ d → d ≤ dHi →
      mLo < 256 → mHi < 256 → deltaLo < 256 → deltaHi < 256 →
      dLo < 256 → dHi < 256 →
      boxLeaf mLo mHi deltaLo deltaHi dLo dHi bits = true := by
    intro mLo mHi deltaLo deltaHi dLo dHi hmLo hmHi hdeltaLo hdeltaHi
      hdLo hdHi hmLoSmall hmHiSmall hdeltaLoSmall hdeltaHiSmall hdLoSmall hdHiSmall
    exact boxLeaf_true bits hCore mLo mHi deltaLo deltaHi dLo dHi hmLo hmHi
      hdeltaLo hdeltaHi hdLo hdHi hmLoSmall hmHiSmall hdeltaLoSmall
      hdeltaHiSmall hdLoSmall hdHiSmall
  have falseOfBox {mLo mHi deltaLo deltaHi dLo dHi : Nat}
      (hLeaf : boxLeaf mLo mHi deltaLo deltaHi dLo dHi bits = true)
      (hUnsat : boxLeaf mLo mHi deltaLo deltaHi dLo dHi bits = false) : False := by
    rw [hUnsat] at hLeaf
    exact Bool.false_ne_true hLeaf
  by_cases hDeltaTwo : 2 ≤ delta
  · exact falseOfBox (hBox 0 12 2 4 0 6 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)) (deltaTwoPlus_unsat bits)
  have hDeltaCases : delta = 0 ∨ delta = 1 := by omega
  rcases hDeltaCases with hDeltaZero | hDeltaOne
  · have hLeaf : deltaZeroAllLeaf bits = true := by
      simp only [deltaZeroAllLeaf, Bool.and_eq_true]
      exact ⟨hBox 0 12 0 0 0 12 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), hDirectCut⟩
    rw [deltaZeroAll_unsat bits] at hLeaf
    exact Bool.false_ne_true hLeaf
  · have hLeaf : deltaOneAllLeaf bits = true := by
      simp only [deltaOneAllLeaf, Bool.and_eq_true]
      exact ⟨hBox 0 9 1 1 0 9 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), hDirectCut⟩
    rw [deltaOneAll_unsat bits] at hLeaf
    exact Bool.false_ne_true hLeaf

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.FiveDispatcher
