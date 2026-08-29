import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.Residual
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ThetaFourCoreDefs
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

namespace RepeatedSharedOmissionCore

abbrev Encoding := ThetaFourCore.Encoding

end RepeatedSharedOmissionCore

open RepeatedSharedOmissionCore

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def pUpperBit (p : Fin 7 → V) : Nat → Bool
  | 0 => decide (R (p 0) (p 1))
  | 1 => decide (R (p 0) (p 2))
  | 2 => decide (R (p 0) (p 3))
  | 3 => decide (R (p 0) (p 4))
  | 4 => decide (R (p 0) (p 5))
  | 5 => decide (R (p 0) (p 6))
  | 6 => decide (R (p 1) (p 2))
  | 7 => decide (R (p 1) (p 3))
  | 8 => decide (R (p 1) (p 4))
  | 9 => decide (R (p 1) (p 5))
  | 10 => decide (R (p 1) (p 6))
  | 11 => decide (R (p 2) (p 3))
  | 12 => decide (R (p 2) (p 4))
  | 13 => decide (R (p 2) (p 5))
  | 14 => decide (R (p 2) (p 6))
  | 15 => decide (R (p 3) (p 4))
  | 16 => decide (R (p 3) (p 5))
  | 17 => decide (R (p 3) (p 6))
  | 18 => decide (R (p 4) (p 5))
  | 19 => decide (R (p 4) (p 6))
  | 20 => decide (R (p 5) (p 6))
  | _ => false

def coreBitAt (p : Fin 7 → V) (a : Fin 8 → V) (z : Fin 4 → V)
    (n : Nat) : Bool :=
  if hnA : n < 64 then
    decide (R (a ⟨n / 8, by omega⟩) (a ⟨n % 8, Nat.mod_lt _ (by omega)⟩))
  else if hnP : n < 85 then pUpperBit R p (n - 64)
  else if hnPH : n < 127 then
    let q := n - 85
    decide (R (p ⟨q / 6, by omega⟩) (a ⟨q % 6 + 1, by omega⟩))
  else if hnPZ : n < 155 then
    let q := n - 127
    decide (R (p ⟨q / 4, by omega⟩) (z ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnRP : n < 162 then
    decide (R (a 7) (p ⟨n - 155, by omega⟩))
  else false

def coreBits (p : Fin 7 → V) (a : Fin 8 → V) (z : Fin 4 → V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 222 => coreBitAt R p a z n))

@[simp] theorem getLsbD_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (n : Nat) (hn : n < 222) :
    (coreBits R p a z).getLsbD n = coreBitAt R p a z n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

private theorem div_index (i j w : Nat) (hj : j < w) : (i * w + j) / w = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j w : Nat) (hj : j < w) : (i * w + j) % w = j :=
  Nat.mul_add_mod_of_lt hj

@[simp] theorem aArc_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    ThetaFourCore.aArc (coreBits R p a z) i j =
      decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [ThetaFourCore.aArc, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (8 * i + j) / 8 = i := by
    simpa [Nat.mul_comm] using div_index i j 8 hj
  have hm : (8 * i + j) % 8 = j := by
    simpa [Nat.mul_comm] using mod_index i j 8 hj
  simp [coreBitAt, show 8 * i + j < 64 by omega, hd, hm]

@[simp] theorem pToH_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (i h : Nat) (hi : i < 7) (hh : h < 6) :
    ThetaFourCore.pToH (coreBits R p a z) i h =
      decide (R (p ⟨i, hi⟩) (a ⟨h + 1, by omega⟩)) := by
  rw [ThetaFourCore.pToH, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (6 * i + h) / 6 = i := by
    simpa [Nat.mul_comm] using div_index i h 6 hh
  have hm : (6 * i + h) % 6 = h := by
    simpa [Nat.mul_comm] using mod_index i h 6 hh
  simp [coreBitAt, show ¬85 + 6 * i + h < 64 by omega,
    show ¬85 + 6 * i + h < 85 by omega,
    show 85 + 6 * i + h < 127 by omega,
    show 85 + 6 * i + h - 85 = 6 * i + h by omega,
    hd, hm]

@[simp] theorem pToZ_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (i j : Nat) (hi : i < 7) (hj : j < 4) :
    ThetaFourCore.pToZ (coreBits R p a z) i j =
      decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [ThetaFourCore.pToZ, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (4 * i + j) / 4 = i := by
    simpa [Nat.mul_comm] using div_index i j 4 hj
  have hm : (4 * i + j) % 4 = j := by
    simpa [Nat.mul_comm] using mod_index i j 4 hj
  simp [coreBitAt, show ¬127 + 4 * i + j < 64 by omega,
    show ¬127 + 4 * i + j < 85 by omega,
    show ¬127 + 4 * i + j < 127 by omega,
    show 127 + 4 * i + j < 155 by omega,
    show 127 + 4 * i + j - 127 = 4 * i + j by omega,
    hd, hm]

@[simp] theorem rToP_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (i : Nat) (hi : i < 7) :
    ThetaFourCore.rToP (coreBits R p a z) i = decide (R (a 7) (p ⟨i, hi⟩)) := by
  rw [ThetaFourCore.rToP, getLsbD_coreBits R p a z _ (by omega)]
  simp [coreBitAt, show ¬155 + i < 64 by omega,
    show ¬155 + i < 85 by omega, show ¬155 + i < 127 by omega,
    show ¬155 + i < 155 by omega, show 155 + i < 162 by omega]

@[simp] theorem signatureCount_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (mask : Nat) (hm : mask < 15) :
    ThetaFourCore.signatureCount (coreBits R p a z) mask = 0 := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  rw [ThetaFourCore.signatureCount, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  by_cases hi4 : i < 4
  · rw [getLsbD_coreBits R p a z _ (by omega)]
    simp [coreBitAt, hi, hi4,
      show ¬162 + 4 * mask + i < 64 by omega,
      show ¬162 + 4 * mask + i < 85 by omega,
      show ¬162 + 4 * mask + i < 127 by omega,
      show ¬162 + 4 * mask + i < 155 by omega,
      show ¬162 + 4 * mask + i < 162 by omega]
  · simp [hi4]

private theorem upper_bit (p : Fin 7 → V) (i j : Nat)
    (hi : i < 7) (hj : j < 7) (hij : i < j) :
    pUpperBit R p (ThetaFourCore.upperIndex i j) =
      decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  interval_cases i <;> interval_cases j <;>
    simp_all [ThetaFourCore.upperIndex, pUpperBit]

theorem pArc_coreBits (p : Fin 7 → V) (a : Fin 8 → V) (z : Fin 4 → V)
    (hLoop : ∀ i : Fin 7, ¬R (p i) (p i))
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (hOriented : ∀ i j : Fin 7, R (p i) (p j) → ¬R (p j) (p i))
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    ThetaFourCore.pArc (coreBits R p a z) i j =
      decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  unfold ThetaFourCore.pArc
  by_cases heq : i = j
  · subst j
    simp [hLoop]
  by_cases hij : i < j
  · rw [if_neg heq, if_pos hij, getLsbD_coreBits R p a z]
    · have hIndex : 64 + ThetaFourCore.upperIndex i j < 85 := by
        interval_cases i <;> interval_cases j <;>
          simp_all [ThetaFourCore.upperIndex]
      rw [show coreBitAt R p a z (64 + ThetaFourCore.upperIndex i j) =
          pUpperBit R p (ThetaFourCore.upperIndex i j) by
        simp [coreBitAt, show ¬64 + ThetaFourCore.upperIndex i j < 64 by omega,
          hIndex]]
      exact upper_bit R p i j hi hj hij
    · interval_cases i <;> interval_cases j <;>
        simp_all [ThetaFourCore.upperIndex]
  · have hji : j < i := by omega
    have hne : j ≠ i := by omega
    rw [if_neg heq, if_neg hij,
      getLsbD_coreBits R p a z _ (by
        interval_cases i <;> interval_cases j <;>
          simp_all [ThetaFourCore.upperIndex])]
    have hIndex : 64 + ThetaFourCore.upperIndex j i < 85 := by
      interval_cases i <;> interval_cases j <;>
        simp_all [ThetaFourCore.upperIndex]
    rw [show coreBitAt R p a z (64 + ThetaFourCore.upperIndex j i) =
        pUpperBit R p (ThetaFourCore.upperIndex j i) by
      simp [coreBitAt, show ¬64 + ThetaFourCore.upperIndex j i < 64 by omega,
        hIndex]]
    rw [upper_bit R p j i hj hi hji]
    rcases hComplete ⟨i, hi⟩ ⟨j, hj⟩ (by exact Fin.ne_of_val_ne heq) with h | h
    · have hn := hOriented ⟨i, hi⟩ ⟨j, hj⟩ h
      simp [h, hn]
    · have hn := hOriented ⟨j, hj⟩ ⟨i, hi⟩ h
      simp [h, hn]

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
