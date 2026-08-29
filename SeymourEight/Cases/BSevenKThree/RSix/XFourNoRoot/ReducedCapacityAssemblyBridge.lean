import SeymourEight.Certificates.BSevenKThree.RSix.XFour.APReducedCapacityDefs

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ReducedCapacityAssemblyBridge

open Core HDeletion StrongDual Rigid

theorem ofNat_ule_ofNat_true (a b : Nat)
    (ha : a < 256) (hb : b < 256) (hab : a ≤ b) :
    (BitVec.ofNat 8 a).ule (BitVec.ofNat 8 b) = true := by
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

set_option linter.flexible false in
/-- Assemble a compressed delta-zero leaf from Boolean facts already proved
about the graph arc table.  Keeping this generic Boolean plumbing outside the
graph proof avoids repeatedly elaborating a large dependent local closure. -/
theorem aRigidPositiveSlice_true
    (aLow aHigh bLow bHigh mLow mHigh : Nat)
    (raw pToZ : Nat → Nat → Bool)
    (hArc : aRigidArc raw = raw)
    (hCommon : commonCore 1 3 raw pToZ = true)
    (hDelete : hQDeletionConditions raw pToZ = true)
    (hCapacity : capacityTwoToFive raw pToZ = true)
    (hDelta : aMissing raw = 0)
    (haLow : (BitVec.ofNat 8 aLow).ule (alpha 1 raw) = true)
    (haHigh : (alpha 1 raw).ule (BitVec.ofNat 8 aHigh) = true)
    (hbLow : (BitVec.ofNat 8 bLow).ule (internalMissing raw) = true)
    (hbHigh : (internalMissing raw).ule (BitVec.ofNat 8 bHigh) = true)
    (hmLow : (BitVec.ofNat 8 mLow).ule
      (externalMissing 1 3 raw pToZ) = true)
    (hmHigh : (externalMissing 1 3 raw pToZ).ule
      (BitVec.ofNat 8 mHigh) = true)
    (hEligible : (1 : BitVec 8).ule (eligibleHCount raw) = true) :
    aRigidPositiveSlice aLow aHigh bLow bHigh mLow mHigh raw pToZ = true := by
  simp [aRigidPositiveSlice, hArc, hCommon, hDelete, hCapacity, hDelta,
    haLow, haHigh, hbLow, hbHigh, hmLow, hmHigh]
  exact hEligible

theorem aRigidPositiveSlice_true_of_values
    (aLow aHigh bLow bHigh mLow mHigh alphaValue betaValue m : Nat)
    (raw pToZ : Nat → Nat → Bool)
    (hArc : aRigidArc raw = raw)
    (hCommon : commonCore 1 3 raw pToZ = true)
    (hDelete : hQDeletionConditions raw pToZ = true)
    (hCapacity : capacityTwoToFive raw pToZ = true)
    (hDelta : aMissing raw = 0)
    (hAlpha : alpha 1 raw = BitVec.ofNat 8 alphaValue)
    (hBeta : internalMissing raw = BitVec.ofNat 8 betaValue)
    (hExternal : externalMissing 1 3 raw pToZ = BitVec.ofNat 8 m)
    (haLow : aLow ≤ alphaValue) (haHigh : alphaValue ≤ aHigh)
    (hbLow : bLow ≤ betaValue) (hbHigh : betaValue ≤ bHigh)
    (hmLow : mLow ≤ m) (hmHigh : m ≤ mHigh)
    (haLowSmall : aLow < 256) (haHighSmall : aHigh < 256)
    (hbLowSmall : bLow < 256) (hbHighSmall : bHigh < 256)
    (hmLowSmall : mLow < 256) (hmHighSmall : mHigh < 256)
    (hAlphaSmall : alphaValue < 256) (hBetaSmall : betaValue < 256)
    (hMSmall : m < 256)
    (hEligible : (1 : BitVec 8).ule (eligibleHCount raw) = true) :
    aRigidPositiveSlice aLow aHigh bLow bHigh mLow mHigh raw pToZ = true := by
  apply aRigidPositiveSlice_true aLow aHigh bLow bHigh mLow mHigh raw pToZ
    hArc hCommon hDelete hCapacity hDelta
  · rw [hAlpha]
    exact ofNat_ule_ofNat_true aLow alphaValue haLowSmall hAlphaSmall haLow
  · rw [hAlpha]
    exact ofNat_ule_ofNat_true alphaValue aHigh hAlphaSmall haHighSmall haHigh
  · rw [hBeta]
    exact ofNat_ule_ofNat_true bLow betaValue hbLowSmall hBetaSmall hbLow
  · rw [hBeta]
    exact ofNat_ule_ofNat_true betaValue bHigh hBetaSmall hbHighSmall hbHigh
  · rw [hExternal]
    exact ofNat_ule_ofNat_true mLow m hmLowSmall hMSmall hmLow
  · rw [hExternal]
    exact ofNat_ule_ofNat_true m mHigh hMSmall hmHighSmall hmHigh
  · exact hEligible

theorem contradiction_of_aRigidPositiveSlice
    (aLow aHigh bLow bHigh mLow mHigh alphaValue betaValue m : Nat)
    (hFalse : ∀ raw pToZ : Nat → Nat → Bool,
      aRigidPositiveSlice aLow aHigh bLow bHigh mLow mHigh raw pToZ = false)
    (raw pToZ : Nat → Nat → Bool)
    (hArc : aRigidArc raw = raw)
    (hCommon : commonCore 1 3 raw pToZ = true)
    (hDelete : hQDeletionConditions raw pToZ = true)
    (hCapacity : capacityTwoToFive raw pToZ = true)
    (hDelta : aMissing raw = 0)
    (hAlpha : alpha 1 raw = BitVec.ofNat 8 alphaValue)
    (hBeta : internalMissing raw = BitVec.ofNat 8 betaValue)
    (hExternal : externalMissing 1 3 raw pToZ = BitVec.ofNat 8 m)
    (haLow : aLow ≤ alphaValue) (haHigh : alphaValue ≤ aHigh)
    (hbLow : bLow ≤ betaValue) (hbHigh : betaValue ≤ bHigh)
    (hmLow : mLow ≤ m) (hmHigh : m ≤ mHigh)
    (haLowSmall : aLow < 256) (haHighSmall : aHigh < 256)
    (hbLowSmall : bLow < 256) (hbHighSmall : bHigh < 256)
    (hmLowSmall : mLow < 256) (hmHighSmall : mHigh < 256)
    (hAlphaSmall : alphaValue < 256) (hBetaSmall : betaValue < 256)
    (hMSmall : m < 256)
    (hEligible : (1 : BitVec 8).ule (eligibleHCount raw) = true) : False := by
  have hLeaf := aRigidPositiveSlice_true_of_values aLow aHigh bLow bHigh
    mLow mHigh alphaValue betaValue m raw pToZ hArc hCommon hDelete hCapacity
    hDelta hAlpha hBeta hExternal haLow haHigh hbLow hbHigh hmLow hmHigh
    haLowSmall haHighSmall hbLowSmall hbHighSmall hmLowSmall hmHighSmall
    hAlphaSmall hBetaSmall hMSmall hEligible
  rw [hFalse _ _] at hLeaf
  contradiction

set_option linter.flexible false in
theorem positiveAlphaDeltaLeaf_true
    (deltaValue : Nat) (arc pToZ : Nat → Nat → Bool)
    (hCommon : commonCore 1 3 arc pToZ = true)
    (hDelete : hQDeletionConditions arc pToZ = true)
    (hCapacity : capacityTwoToFive arc pToZ = true)
    (hDelta : aMissing arc = BitVec.ofNat 8 deltaValue)
    (hAlpha : (1 : BitVec 8).ule (alpha 1 arc) = true)
    (hEligible : (1 : BitVec 8).ule (eligibleHCount arc) = true) :
    positiveAlphaDeltaLeaf deltaValue arc pToZ = true := by
  simp [positiveAlphaDeltaLeaf, hCommon, hDelete, hCapacity, hDelta]
  exact ⟨hAlpha, hEligible⟩

theorem pRigidPositiveAlphaDeltaTwoLeaf_true
    (raw pToZ : Nat → Nat → Bool)
    (hArc : APRigid.pRigidArc raw = raw)
    (hBase : positiveAlphaDeltaLeaf 2 raw pToZ = true) :
    pRigidPositiveAlphaDeltaTwoLeaf raw pToZ = true := by
  simpa [pRigidPositiveAlphaDeltaTwoLeaf, hArc] using hBase

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ReducedCapacityAssemblyBridge
