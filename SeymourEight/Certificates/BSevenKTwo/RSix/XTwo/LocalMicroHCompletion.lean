import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHTwoRange
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHRangeBridge

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

open Shared.FiniteCore

private abbrev BV8 := BitVec 8

/-- Complete the four represented `H → q` incidences.  These are the only
bits on which the capacity parameter in `microHCore` depends. -/
def completeHToQ (bits : Encoding) : Encoding :=
  bits ||| ((15 : Encoding) <<< 190)

theorem getLsbD_complete_low (bits : Encoding) (i : Nat) (hi : i < 190) :
    (completeHToQ bits).getLsbD i = bits.getLsbD i := by
  rw [completeHToQ, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp [hi]

theorem aArc_complete (bits : Encoding) (i j : Nat)
    (hi : i < 8) (hj : j < 8) :
    aArc (completeHToQ bits) i j = aArc bits i j := by
  simp only [aArc]
  rw [getLsbD_complete_low bits (8 * i + j) (by omega)]

theorem pArc_complete (bits : Encoding) (i j : Nat)
    (hi : i < 6) (hj : j < 6) :
    pArc (completeHToQ bits) i j = pArc bits i j := by
  simp only [pArc]
  rw [getLsbD_complete_low bits (64 + directedIndex i j) (by
    simp [directedIndex]
    split <;> omega)]

theorem pToH_complete (bits : Encoding) (p h : Nat)
    (hp : p < 6) (hh : h < 4) :
    pToH (completeHToQ bits) p h = pToH bits p h := by
  simp only [pToH]
  rw [getLsbD_complete_low bits (94 + 4 * p + h) (by omega)]

theorem hToP_complete (bits : Encoding) (h p : Nat)
    (hh : h < 4) (hp : p < 6) :
    hToP (completeHToQ bits) h p = hToP bits h p := by
  simp only [hToP]
  rw [getLsbD_complete_low bits (118 + 6 * h + p) (by omega)]

theorem pToE_complete (bits : Encoding) (p e : Nat)
    (hp : p < 6) (he : e < 5) :
    pToE (completeHToQ bits) p e = pToE bits p e := by
  simp only [pToE]
  rw [getLsbD_complete_low bits (142 + 5 * p + e) (by omega)]

theorem hArc_complete (bits : Encoding) (h k : Nat)
    (hh : h < 4) (hk : k < 4) :
    hArc (completeHToQ bits) h k = hArc bits h k := by
  simp only [hArc]
  exact aArc_complete bits (1 + h) (1 + k) (by omega) (by omega)

theorem xToT_complete (bits : Encoding) (x t : Nat)
    (hx : x < 2) (ht : t < 4) :
    xToT (completeHToQ bits) x t = xToT bits x t := by
  simp only [xToT]
  apply aArc_complete
  · omega
  · split <;> omega

theorem aOneSecondH_complete (bits : Encoding) (a h : Nat)
    (ha : a < 4) (hh : h < 4) :
    aOneSecondH (completeHToQ bits) a h = aOneSecondH bits a h := by
  by_cases h2 : 2 ≤ a <;>
    simp (disch := omega) [aOneSecondH, any, hArc_complete,
      hToP_complete, pToH_complete, xToT_complete, h2]

theorem aOneSecondP_complete (bits : Encoding) (a p : Nat)
    (ha : a < 4) (hp : p < 6) :
    aOneSecondP (completeHToQ bits) a p = aOneSecondP bits a p := by
  by_cases h2 : 2 ≤ a <;>
    simp (disch := omega) [aOneSecondP, any, hArc_complete,
      hToP_complete, pArc_complete, xToT_complete, h2]

theorem aOneSecondZ_complete (bits : Encoding) (a z : Nat)
    (ha : a < 4) (hz : z < 4) :
    aOneSecondZ (completeHToQ bits) a z = aOneSecondZ bits a z := by
  simp (disch := omega) [aOneSecondZ, any, hToP_complete,
    pToE_complete]

theorem aOneSecondT_complete (bits : Encoding) (a t : Nat)
    (ha : a < 4) (ht : t < 4) :
    aOneSecondT (completeHToQ bits) a t = aOneSecondT bits a t := by
  simp (disch := omega) [aOneSecondT, any, hArc_complete,
    xToT_complete]

theorem hToQCore_complete (bits : Encoding) (c h : Nat) (hh : h < 4) :
    hToQCore c (completeHToQ bits) h = true := by
  have hs : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;>
    simp [hToQCore, aToQ, completeHToQ]

theorem pOut_complete (bits : Encoding) (p : Nat) (hp : p < 6) :
    pOut (completeHToQ bits) p = pOut bits p := by
  simp (disch := omega) [pOut, count, pArc_complete]

theorem pHOut_complete (bits : Encoding) (p : Nat) (hp : p < 6) :
    pHOut (completeHToQ bits) p = pHOut bits p := by
  simp (disch := omega) [pHOut, count, pToH_complete]

theorem hPOut_complete (bits : Encoding) (h : Nat) (hh : h < 4) :
    hPOut (completeHToQ bits) h = hPOut bits h := by
  simp (disch := omega) [hPOut, count, hToP_complete]

theorem pEOut_complete (bits : Encoding) (p : Nat) (hp : p < 6) :
    pEOut 5 (completeHToQ bits) p = pEOut 5 bits p := by
  simp (disch := omega) [pEOut, count, pToE_complete]

theorem totalPOut_complete (bits : Encoding) :
    totalPOut (completeHToQ bits) = totalPOut bits := by
  simp (disch := omega) [totalPOut, sumCount, pOut_complete]

theorem totalPToH_complete (bits : Encoding) :
    totalPToH (completeHToQ bits) = totalPToH bits := by
  simp (disch := omega) [totalPToH, sumCount, pHOut_complete]

theorem totalHToP_complete (bits : Encoding) :
    totalHToP (completeHToQ bits) = totalHToP bits := by
  simp (disch := omega) [totalHToP, sumCount, hPOut_complete]

theorem totalPToE_complete (bits : Encoding) :
    totalPToE 5 (completeHToQ bits) = totalPToE 5 bits := by
  simp (disch := omega) [totalPToE, sumCount, pEOut_complete]

theorem externalMissing_complete (bits : Encoding) :
    externalMissing 5 (completeHToQ bits) = externalMissing 5 bits := by
  simp only [externalMissing, totalPToE_complete]

theorem orientedP_complete (bits : Encoding) :
    orientedP (completeHToQ bits) = orientedP bits := by
  simp (disch := omega) [orientedP, all, pArc_complete]

theorem orientedPH_complete (bits : Encoding) :
    orientedPH (completeHToQ bits) = orientedPH bits := by
  simp (disch := omega) [orientedPH, all, pToH_complete, hToP_complete]

theorem orientedHH_complete (bits : Encoding) :
    orientedHH (completeHToQ bits) = orientedHH bits := by
  simp (disch := omega) [orientedHH, all, hArc_complete]

theorem everyXReached_complete (bits : Encoding) :
    everyXReached (completeHToQ bits) = everyXReached bits := by
  simp (disch := omega) [everyXReached, all, any, aArc_complete,
    pToH_complete]

theorem distinguishedAOne_complete (bits : Encoding) :
    distinguishedAOne (completeHToQ bits) = distinguishedAOne bits := by
  simp (disch := omega) [distinguishedAOne, count, hArc_complete]

theorem reachesPH_complete (bits : Encoding) (p q : Nat)
    (hp : p < 6) (hq : q < 6) :
    reachesPH (completeHToQ bits) p q = reachesPH bits p q := by
  simp (disch := omega) [reachesPH, any, pToA, aToP,
    pArc_complete, pToH_complete, hToP_complete]

theorem pSecondPCount_complete (bits : Encoding) (p : Nat) (hp : p < 6) :
    pSecondPCount (completeHToQ bits) p = pSecondPCount bits p := by
  simp (disch := omega) [pSecondPCount, count, pArc_complete,
    reachesPH_complete]

theorem pEffectiveConditionFiveSelected_complete
    (m : BitVec 2) (bits : Encoding) (p : Nat) (hp : p < 6) :
    pEffectiveConditionFiveSelected m (completeHToQ bits) p =
      pEffectiveConditionFiveSelected m bits p := by
  simp only [pEffectiveConditionFiveSelected, pSecondPCount_complete bits p hp,
    pOut_complete bits p hp, pHOut_complete bits p hp,
    pEOut_complete bits p hp]

private def hSecondBase (bits : Encoding) (h : Nat) : BV8 :=
  count 4 (aOneSecondH bits h) + count 6 (aOneSecondP bits h) +
    count 4 (aOneSecondZ bits h) + count 4 (aOneSecondT bits h)

private def hDirectBase (bits : Encoding) (h : Nat) : BV8 :=
  count 4 (hArc bits h) + hPOut bits h +
    (if h < 2 then 0 else count 4 (xToT bits (h - 2)))

private theorem hSecondBase_complete (bits : Encoding) (h : Nat)
    (hh : h < 4) :
    hSecondBase (completeHToQ bits) h = hSecondBase bits h := by
  simp (disch := omega) [hSecondBase, count, aOneSecondH_complete,
    aOneSecondP_complete, aOneSecondZ_complete, aOneSecondT_complete]

private theorem hDirectBase_complete (bits : Encoding) (h : Nat)
    (hh : h < 4) :
    hDirectBase (completeHToQ bits) h = hDirectBase bits h := by
  simp (disch := omega) [hDirectBase, count, hArc_complete,
    hPOut_complete, xToT_complete]

private theorem hSecondBase_le (bits : Encoding) (h : Nat) :
    (hSecondBase bits h).ule 18 = true := by
  simp only [hSecondBase, count, bitCount]
  bv_decide

private theorem hDirectBase_le (bits : Encoding) (h : Nat) :
    (hDirectBase bits h).ule 14 = true := by
  by_cases h2 : h < 2 <;>
    simp only [hDirectBase, hPOut, h2, ↓reduceIte, count, bitCount] <;>
    bv_decide

private theorem restricted_mono_arith (s d : BV8) (q sec : Bool)
    (hs : s.ule 18 = true) (hd : d.ule 14 = true)
    (hlt : (s + bitCount sec).ult (d + bitCount q) = true) :
    (s + 0).ult (d + 1) = true := by
  simp only [bitCount] at hlt ⊢
  bv_decide

private theorem hRestrictedSecondCountCore_eq (c : Nat) (bits : Encoding)
    (h : Nat) :
    hRestrictedSecondCountCore c bits h =
      hSecondBase bits h + bitCount (hSecondQCore c bits h) := by
  rfl

private theorem hDirectCore_eq (c : Nat) (bits : Encoding) (h : Nat) :
    hDirectCore c bits h =
      hDirectBase bits h + bitCount (hToQCore c bits h) := by
  simp only [hDirectCore, hDirectBase]
  ac_rfl

private theorem hRestricted_complete (c : Nat) (bits : Encoding)
    (h : Nat) (hh : h < 4)
    (hr : hRestrictedNonSeymourCore c bits h = true) :
    hRestrictedNonSeymourCore 2 (completeHToQ bits) h = true := by
  have hs := hSecondBase_le bits h
  have hd := hDirectBase_le bits h
  rw [hRestrictedNonSeymourCore, hRestrictedSecondCountCore_eq,
    hDirectCore_eq] at hr ⊢
  rw [hSecondBase_complete bits h hh, hDirectBase_complete bits h hh,
    hToQCore_complete bits 2 h hh]
  simp only [hSecondQCore, hToQCore_complete bits 2 h hh, Bool.not_true,
    Bool.false_and, bitCount, Bool.false_eq_true,
    ↓reduceIte]
  exact restricted_mono_arith _ _ _ _ hs hd hr

private theorem hArcCount_complete (bits : Encoding) (h : Nat) (hh : h < 4) :
    count 4 (hArc (completeHToQ bits) h) = count 4 (hArc bits h) := by
  simp (disch := omega) [count, hArc_complete]

private theorem hPOut_le (bits : Encoding) (h : Nat) :
    (hPOut bits h).ule 6 = true := by
  simp only [hPOut, count, bitCount]
  bv_decide

private theorem degree_mono (d : BV8) (q : Bool)
    (hd : d.ule 14 = true)
    (hs : (8 : BV8).ule (d + bitCount q) = true) :
    (8 : BV8).ule (d + 1) = true := by
  simp only [bitCount] at hs ⊢
  bv_decide

private theorem pivot_mono (d : BV8) (q : Bool)
    (hd : d.ule 6 = true)
    (hs : (6 : BV8).ule (d + bitCount q) = true) :
    (6 : BV8).ule (d + 1) = true := by
  simp only [bitCount] at hs ⊢
  bv_decide

private theorem aOneToQ_complete (bits : Encoding) :
    aOneToQ (completeHToQ bits) = 2 := by
  simp [aOneToQ, count, bitCount, aToQ, completeHToQ]

private theorem zReached_complete (bits : Encoding) :
    all 4 (fun z => any 6 fun p => pToE (completeHToQ bits) p (1 + z)) =
      all 4 (fun z => any 6 fun p => pToE bits p (1 + z)) := by
  simp (disch := omega) [all, any, pToE_complete]

private theorem pMinimum_complete (bits : Encoding) :
    all 6 (fun p => (8 : BV8).ule
      (pOut (completeHToQ bits) p + pHOut (completeHToQ bits) p +
        pEOut 5 (completeHToQ bits) p)) =
    all 6 (fun p => (8 : BV8).ule
      (pOut bits p + pHOut bits p + pEOut 5 bits p)) := by
  simp (disch := omega) [all, pOut_complete, pHOut_complete,
    pEOut_complete]

private theorem effectiveAll_complete (m : BitVec 2) (bits : Encoding) :
    all 6 (pEffectiveConditionFiveSelected m (completeHToQ bits)) =
      all 6 (pEffectiveConditionFiveSelected m bits) := by
  simp (disch := omega) [all, pEffectiveConditionFiveSelected_complete]

private theorem microHCore_complete_of_lower (c : Nat) (bits : Encoding)
    (hc : microHCore c bits = true)
    (h14 : (14 : BV8).ule (totalHToP bits) = true) :
    microHCore 2 (completeHToQ bits) = true := by
  simp only [microHCore, Bool.and_eq_true] at hc ⊢
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hOP, hOPH⟩, hOHH⟩,
    hPivot⟩, hDirect⟩, hX⟩, _hReach⟩, hZ⟩, hPMin⟩, hRestr⟩,
    _hCount⟩, _hLower⟩, hUpper⟩
  have hPivot' : all 2 (fun a =>
      (2 : BV8).ule (count 4 (hArc (completeHToQ bits) a)) &&
      (!(count 4 (hArc (completeHToQ bits) a) == 2) ||
        (6 : BV8).ule (hPOut (completeHToQ bits) a +
          bitCount (hToQCore 2 (completeHToQ bits) a)))) = true := by
    rw [all_eq_true_iff] at hPivot ⊢
    intro a ha
    have hs := hPivot a ha
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
    rcases hs with ⟨hcnt, hcase⟩
    rw [hArcCount_complete bits a (by omega),
      hPOut_complete bits a (by omega),
      hToQCore_complete bits 2 a (by omega)]
    refine ⟨hcnt, ?_⟩
    rcases hcase with hneq | hdeg
    · exact Or.inl hneq
    · exact Or.inr (pivot_mono (hPOut bits a) (hToQCore c bits a)
        (hPOut_le bits a) hdeg)
  have hDirect' : all 4 (fun h =>
      (8 : BV8).ule (hDirectCore 2 (completeHToQ bits) h)) = true := by
    rw [all_eq_true_iff] at hDirect ⊢
    intro h hh
    have hs := hDirect h hh
    rw [hDirectCore_eq] at hs ⊢
    rw [hDirectBase_complete bits h hh,
      hToQCore_complete bits 2 h hh]
    simp only [bitCount]
    exact degree_mono (hDirectBase bits h) (hToQCore c bits h)
      (hDirectBase_le bits h) hs
  have hRestr' : all 4
      (hRestrictedNonSeymourCore 2 (completeHToQ bits)) = true := by
    rw [all_eq_true_iff] at hRestr ⊢
    intro h hh
    exact hRestricted_complete c bits h hh (hRestr h hh)
  have hOP' : orientedP (completeHToQ bits) = true := by
    rw [orientedP_complete]
    exact hOP
  have hOPH' : orientedPH (completeHToQ bits) = true := by
    rw [orientedPH_complete]
    exact hOPH
  have hOHH' : orientedHH (completeHToQ bits) = true := by
    rw [orientedHH_complete]
    exact hOHH
  have hX' : everyXReached (completeHToQ bits) = true := by
    rw [everyXReached_complete]
    exact hX
  have hReach' : ((decide (0 < 2) ||
      any 6 (fun p => pToE (completeHToQ bits) p 0)) ||
      any 2 (fun x => hToQCore 2 (completeHToQ bits) (2 + x))) = true := by
    simp
  have hZ' : all 4 (fun z => any 6 fun p =>
      pToE (completeHToQ bits) p (1 + z)) = true := by
    rw [zReached_complete]
    exact hZ
  have hPMin' : all 6 (fun p => (8 : BV8).ule
      (pOut (completeHToQ bits) p + pHOut (completeHToQ bits) p +
        pEOut 5 (completeHToQ bits) p)) = true := by
    rw [pMinimum_complete]
    exact hPMin
  have hCount' : (aOneToQ (completeHToQ bits) ==
      BitVec.ofNat 8 2) = true := by
    simpa using aOneToQ_complete bits
  have hLower' : (BitVec.ofNat 8 (16 - 2)).ule
      (totalHToP (completeHToQ bits)) = true := by
    rw [totalHToP_complete]
    exact h14
  have hUpper' : (totalHToP (completeHToQ bits) +
      externalMissing 5 (completeHToQ bits)).ule 21 = true := by
    rw [totalHToP_complete, externalMissing_complete]
    exact hUpper
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hOP', hOPH'⟩, hOHH'⟩, hPivot'⟩,
    hDirect'⟩, hX'⟩, hReach'⟩, hZ'⟩, hPMin'⟩, hRestr'⟩,
    hCount'⟩, hLower'⟩, hUpper'⟩

private theorem core_lower (c : Nat) (bits : Encoding)
    (hc : microHCore c bits = true) :
    (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) = true := by
  simp only [microHCore, Bool.and_eq_true] at hc
  aesop

private theorem le14_of_le16 (x : BV8)
    (h : (16 : BV8).ule x = true) : (14 : BV8).ule x = true := by
  bv_decide

private theorem le14_of_le15 (x : BV8)
    (h : (15 : BV8).ule x = true) : (14 : BV8).ule x = true := by
  bv_decide

private theorem le6_of_le3 (x : BV8)
    (h : x.ule 3 = true) : x.ule 6 = true := by
  bv_decide

private theorem le6_of_le5 (x : BV8)
    (h : x.ule 5 = true) : x.ule 6 = true := by
  bv_decide

private theorem le3_of_le2 (x : BitVec 2)
    (_h : x.ule 2 = true) : x.ule 3 = true := by
  bv_decide

private theorem selected_zero_complete (bits : Encoding)
    (hs : microHEffectiveLowPHSelectedMissing 0 3 0 0 bits = true) :
    microHEffectiveLowPHSelectedMissing 2 6 3 0
      (completeHToQ bits) = true := by
  simp only [microHEffectiveLowPHSelectedMissing, Bool.and_eq_true] at hs ⊢
  rcases hs with ⟨⟨⟨⟨⟨⟨hCore, hEff⟩, hDist⟩, hPH⟩, hMissing⟩,
    _hMax⟩, hDegree⟩
  have h16 : (16 : BV8).ule (totalHToP bits) = true := by
    simpa using core_lower 0 bits hCore
  have hCore' := microHCore_complete_of_lower 0 bits hCore
    (le14_of_le16 _ h16)
  have hEff' : all 6 (pEffectiveConditionFiveSelected 0
      (completeHToQ bits)) = true := by
    rw [effectiveAll_complete]
    exact hEff
  have hDist' : distinguishedAOne (completeHToQ bits) = true := by
    rw [distinguishedAOne_complete]
    exact hDist
  have hPH' : (totalPToH (completeHToQ bits)).ule 6 = true := by
    rw [totalPToH_complete]
    exact le6_of_le3 _ hPH
  have hMissing' : (externalMissing 5 (completeHToQ bits) ==
      (0 : BitVec 2).zeroExtend 8) = true := by
    rw [externalMissing_complete]
    exact hMissing
  have hMax' : (0 : BitVec 2).ule (BitVec.ofNat 2 3) = true := by decide
  have hDegree' : (48 : BV8).ule
      (totalPOut (completeHToQ bits) + totalPToH (completeHToQ bits) +
        totalPToE 5 (completeHToQ bits)) = true := by
    rw [totalPOut_complete, totalPToH_complete, totalPToE_complete]
    exact hDegree
  exact ⟨⟨⟨⟨⟨⟨hCore', hEff'⟩, hDist'⟩, hPH'⟩, hMissing'⟩,
    hMax'⟩, hDegree'⟩

private theorem selected_one_complete (m : BitVec 2) (bits : Encoding)
    (hs : microHEffectiveLowPHSelectedMissing 1 5 2 m bits = true) :
    microHEffectiveLowPHSelectedMissing 2 6 3 m
      (completeHToQ bits) = true := by
  simp only [microHEffectiveLowPHSelectedMissing, Bool.and_eq_true] at hs ⊢
  rcases hs with ⟨⟨⟨⟨⟨⟨hCore, hEff⟩, hDist⟩, hPH⟩, hMissing⟩,
    hMax⟩, hDegree⟩
  have h15 : (15 : BV8).ule (totalHToP bits) = true := by
    simpa using core_lower 1 bits hCore
  have hCore' := microHCore_complete_of_lower 1 bits hCore
    (le14_of_le15 _ h15)
  have hEff' : all 6 (pEffectiveConditionFiveSelected m
      (completeHToQ bits)) = true := by
    rw [effectiveAll_complete]
    exact hEff
  have hDist' : distinguishedAOne (completeHToQ bits) = true := by
    rw [distinguishedAOne_complete]
    exact hDist
  have hPH' : (totalPToH (completeHToQ bits)).ule 6 = true := by
    rw [totalPToH_complete]
    exact le6_of_le5 _ hPH
  have hMissing' : (externalMissing 5 (completeHToQ bits) ==
      m.zeroExtend 8) = true := by
    rw [externalMissing_complete]
    exact hMissing
  have hMax' : m.ule (BitVec.ofNat 2 3) = true := le3_of_le2 _ hMax
  have hDegree' : (48 : BV8).ule
      (totalPOut (completeHToQ bits) + totalPToH (completeHToQ bits) +
        totalPToE 5 (completeHToQ bits)) = true := by
    rw [totalPOut_complete, totalPToH_complete, totalPToE_complete]
    exact hDegree
  exact ⟨⟨⟨⟨⟨⟨hCore', hEff'⟩, hDist'⟩, hPH'⟩, hMissing'⟩,
    hMax'⟩, hDegree'⟩

theorem microHEffectiveLowPH_zero_m0_unsat (bits : Encoding) :
    microHEffectiveLowPHMissing 0 3 0 bits = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hs := microHEffectiveLowPHMissing_to_selected 0 3 0 0 bits
    (by omega) (by omega) h
  have ht := selected_zero_complete bits hs
  rw [microHEffectiveLowPH_two_range_unsat 0 (completeHToQ bits)] at ht
  exact Bool.false_ne_true ht

theorem microHEffectiveLowPH_one_range_unsat
    (m : BitVec 2) (bits : Encoding) :
    microHEffectiveLowPHSelectedMissing 1 5 2 m bits = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have ht := selected_one_complete m bits h
  rw [microHEffectiveLowPH_two_range_unsat m (completeHToQ bits)] at ht
  exact Bool.false_ne_true ht

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
