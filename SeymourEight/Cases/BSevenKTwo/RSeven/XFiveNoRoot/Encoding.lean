import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.CoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Encoding

open Core

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (n : Nat) : Bool :=
  if hnA : n < 64 then
    decide (R (a ⟨n / 8, by omega⟩) (a ⟨n % 8, Nat.mod_lt _ (by omega)⟩))
  else if hnP : n < 106 then
    let q := n - 64
    let i := q / 6
    let j0 := q % 6
    let j := if j0 < i then j0 else j0 + 1
    decide (R (p ⟨i, by omega⟩) (p ⟨j, by
      have hj0 : j0 < 6 := Nat.mod_lt _ (by omega)
      dsimp [j]
      split <;> omega⟩))
  else if hnPH : n < 155 then
    let q := n - 106
    decide (R (p ⟨q / 7, by omega⟩)
      (a ⟨q % 7 + 1, by have := Nat.mod_lt q (by omega : 0 < 7); omega⟩))
  else if hnHP : n < 204 then
    let q := n - 155
    decide (R (a ⟨q / 7 + 1, by omega⟩)
      (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPZ : n < 225 then
    let q := n - 204
    decide (R (p ⟨q / 3, by omega⟩)
      (z ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 7 → V) (a : Fin 8 → V) (z : Fin 3 → V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 225 => coreBitAt R p a z n))

@[simp] theorem getLsbD_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 3 → V) (n : Nat) (hn : n < 225) :
    (coreBits R p a z).getLsbD n = coreBitAt R p a z n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

@[simp] theorem aArc_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (coreBits R p a z) i j = decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [aArc, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (8 * i + j) / 8 = i := by omega
  have hm : (8 * i + j) % 8 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  simp [coreBitAt, show 8 * i + j < 64 by omega, hd, hm]

@[simp] theorem pArc_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p a z) i j = decide (i ≠ j ∧ R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [pArc]
  · have hIndex : 64 + directedIndex i j < 106 := by
      unfold directedIndex
      split <;> omega
    rw [pArc, getLsbD_coreBits R p a z _ (by omega)]
    have hDiv : directedIndex i j / 6 = i := by
      unfold directedIndex
      split <;> omega
    have hMod : directedIndex i j % 6 = if j < i then j else j - 1 := by
      by_cases hji : j < i
      · simpa [directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j < 6 by omega)
      · simpa [directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j - 1 < 6 by omega)
    have hTarget :
        (if (if j < i then j else j - 1) < i then
          (if j < i then j else j - 1)
        else (if j < i then j else j - 1) + 1) = j := by
      by_cases hji : j < i
      · simp [hji]
      · have hij' : i < j := by omega
        have hnot : ¬j - 1 < i := by omega
        simp [hji, hnot]
        omega
    simp only [coreBitAt, dif_neg (by omega : ¬64 + directedIndex i j < 64),
      dif_pos hIndex, show 64 + directedIndex i j - 64 = directedIndex i j by omega]
    have hSource : p ⟨directedIndex i j / 6, by omega⟩ = p ⟨i, hi⟩ := by
      apply congrArg p
      exact Fin.ext hDiv
    have hDestination :
        p ⟨if directedIndex i j % 6 < directedIndex i j / 6 then
              directedIndex i j % 6 else directedIndex i j % 6 + 1, by
            have := Nat.mod_lt (directedIndex i j) (by omega : 0 < 6)
            split <;> omega⟩ = p ⟨j, hj⟩ := by
      apply congrArg p
      apply Fin.ext
      simpa [hDiv, hMod] using hTarget
    rw [hSource, hDestination]
    simp [hij]

@[simp] theorem pToH_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 3 → V) (i h : Nat) (hi : i < 7) (hh : h < 7) :
    pToH (coreBits R p a z) i h = decide (R (p ⟨i, hi⟩) (a ⟨h + 1, by omega⟩)) := by
  rw [pToH, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (7 * i + h) / 7 = i := by omega
  have hm : (7 * i + h) % 7 = h := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hh
  simp [coreBitAt, show ¬106 + 7 * i + h < 64 by omega,
    show ¬106 + 7 * i + h < 106 by omega,
    show 106 + 7 * i + h < 155 by omega,
    show 106 + 7 * i + h - 106 = 7 * i + h by omega, hd, hm]

@[simp] theorem hToP_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 3 → V) (h i : Nat) (hh : h < 7) (hi : i < 7) :
    hToP (coreBits R p a z) h i = decide (R (a ⟨h + 1, by omega⟩) (p ⟨i, hi⟩)) := by
  rw [hToP, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (7 * h + i) / 7 = h := by omega
  have hm : (7 * h + i) % 7 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := h) hi
  simp [coreBitAt, show ¬155 + 7 * h + i < 64 by omega,
    show ¬155 + 7 * h + i < 106 by omega,
    show ¬155 + 7 * h + i < 155 by omega,
    show 155 + 7 * h + i < 204 by omega,
    show 155 + 7 * h + i - 155 = 7 * h + i by omega, hd, hm]

@[simp] theorem pToZ_coreBits (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 7) (hj : j < 3) :
    pToZ (coreBits R p a z) i j = decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [pToZ, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (3 * i + j) / 3 = i := by omega
  have hm : (3 * i + j) % 3 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  simp [coreBitAt, show ¬204 + 3 * i + j < 64 by omega,
    show ¬204 + 3 * i + j < 106 by omega,
    show ¬204 + 3 * i + j < 155 by omega,
    show ¬204 + 3 * i + j < 204 by omega,
    show 204 + 3 * i + j < 225 by omega,
    show 204 + 3 * i + j - 204 = 3 * i + j by omega, hd, hm]

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Encoding
