import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.CoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding

open Core

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V)
    (n : Nat) : Bool :=
  if hnX0 : n < 4 then
    decide (R (a ⟨n + 4, by omega⟩) (a 0))
  else if hnHH : n < 46 then
    let q := n - 4
    let i := q / 6
    let j0 := q % 6
    let j := if j0 < i then j0 else j0 + 1
    decide (R (a ⟨i + 1, by omega⟩) (a ⟨j + 1, by
      have hj0 : j0 < 6 := Nat.mod_lt _ (by omega)
      dsimp [j]
      split <;> omega⟩))
  else if hnPP : n < 88 then
    let q := n - 46
    let i := q / 6
    let j0 := q % 6
    let j := if j0 < i then j0 else j0 + 1
    decide (R (p ⟨i, by omega⟩) (p ⟨j, by
      have hj0 : j0 < 6 := Nat.mod_lt _ (by omega)
      dsimp [j]
      split <;> omega⟩))
  else if hnPH : n < 137 then
    let q := n - 88
    decide (R (p ⟨q / 7, by omega⟩)
      (a ⟨q % 7 + 1, by have := Nat.mod_lt q (by omega : 0 < 7); omega⟩))
  else if hnHP : n < 186 then
    let q := n - 137
    decide (R (a ⟨q / 7 + 1, by omega⟩)
      (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPZ : n < 221 then
    let q := n - 186
    let j := q % 5
    if hj : j < zCount then
      decide (R (p ⟨q / 5, by omega⟩) (z ⟨j, hj⟩))
    else false
  else false

def coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) : Core.Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 221 => coreBitAt R p a z n))

@[simp] theorem getLsbD_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (n : Nat) (hn : n < 221) :
    (coreBits R p a z).getLsbD n = coreBitAt R p a z n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

@[simp] theorem xToAOne_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (i : Nat) (hi : i < 4) :
    Core.aArc (coreBits R p a z) (4 + i) 0 =
      decide (R (a ⟨4 + i, by omega⟩) (a 0)) := by
  rw [Core.aArc]
  simp only [show 4 + i ≠ 0 by omega, ↓reduceIte, show ¬4 + i ≤ 3 by omega]
  have hsub : 4 + i - 4 = i := by omega
  rw [hsub, getLsbD_coreBits R p a z i (by omega)]
  simp [coreBitAt, hi, Nat.add_comm]

@[simp] theorem hArc_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (i j : Nat) (hi : i < 7) (hj : j < 7) :
    Core.aArc (coreBits R p a z) (i + 1) (j + 1) =
      decide (i ≠ j ∧ R (a ⟨i + 1, by omega⟩) (a ⟨j + 1, by omega⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [Core.aArc]
  · have hIndex : 4 + Core.hDirectedIndex i j < 46 := by
      unfold Core.hDirectedIndex
      split <;> omega
    rw [Core.aArc]
    simp only [show i + 1 ≠ 0 by omega, ↓reduceIte,
      show j + 1 ≠ 0 by omega, Nat.add_sub_cancel]
    rw [getLsbD_coreBits R p a z _ (by omega)]
    have hDiv : Core.hDirectedIndex i j / 6 = i := by
      unfold Core.hDirectedIndex
      split <;> omega
    have hMod : Core.hDirectedIndex i j % 6 = if j < i then j else j - 1 := by
      by_cases hji : j < i
      · simpa [Core.hDirectedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j < 6 by omega)
      · simpa [Core.hDirectedIndex, hji, Nat.mul_comm] using
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
    simp only [coreBitAt, dif_neg (by omega : ¬4 + Core.hDirectedIndex i j < 4),
      dif_pos hIndex, show 4 + Core.hDirectedIndex i j - 4 =
        Core.hDirectedIndex i j by omega]
    have hSource : a ⟨Core.hDirectedIndex i j / 6 + 1, by omega⟩ =
        a ⟨i + 1, by omega⟩ := by
      apply congrArg a
      exact Fin.ext (by simp [hDiv])
    have hDestination :
        a ⟨(if Core.hDirectedIndex i j % 6 < Core.hDirectedIndex i j / 6 then
              Core.hDirectedIndex i j % 6 else Core.hDirectedIndex i j % 6 + 1) + 1,
            by have := Nat.mod_lt (Core.hDirectedIndex i j) (by omega : 0 < 6)
               split <;> omega⟩ = a ⟨j + 1, by omega⟩ := by
      apply congrArg a
      apply Fin.ext
      simp only [hDiv, hMod]
      rw [hTarget]
    rw [hSource, hDestination]
    simp [hij]

@[simp] theorem pArc_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (i j : Nat) (hi : i < 7) (hj : j < 7) :
    Core.pArc (coreBits R p a z) i j =
      decide (i ≠ j ∧ R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [Core.pArc]
  · have hIndex : 46 + Core.pDirectedIndex i j < 88 := by
      unfold Core.pDirectedIndex
      split <;> omega
    rw [Core.pArc, getLsbD_coreBits R p a z _ (by omega)]
    have hDiv : Core.pDirectedIndex i j / 6 = i := by
      unfold Core.pDirectedIndex
      split <;> omega
    have hMod : Core.pDirectedIndex i j % 6 = if j < i then j else j - 1 := by
      by_cases hji : j < i
      · simpa [Core.pDirectedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j < 6 by omega)
      · simpa [Core.pDirectedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j - 1 < 6 by omega)
    have hTarget :
        (if (if j < i then j else j - 1) < i then
          (if j < i then j else j - 1)
        else (if j < i then j else j - 1) + 1) = j := by
      by_cases hji : j < i
      · simp [hji]
      · have hnot : ¬j - 1 < i := by omega
        simp [hji, hnot]
        omega
    simp only [coreBitAt, dif_neg (by omega : ¬46 + Core.pDirectedIndex i j < 4),
      dif_neg (by omega : ¬46 + Core.pDirectedIndex i j < 46), dif_pos hIndex,
      show 46 + Core.pDirectedIndex i j - 46 = Core.pDirectedIndex i j by omega]
    have hSource : p ⟨Core.pDirectedIndex i j / 6, by omega⟩ = p ⟨i, hi⟩ := by
      apply congrArg p
      exact Fin.ext hDiv
    have hDestination :
        p ⟨if Core.pDirectedIndex i j % 6 < Core.pDirectedIndex i j / 6 then
              Core.pDirectedIndex i j % 6 else Core.pDirectedIndex i j % 6 + 1,
            by have := Nat.mod_lt (Core.pDirectedIndex i j) (by omega : 0 < 6)
               split <;> omega⟩ = p ⟨j, hj⟩ := by
      apply congrArg p
      apply Fin.ext
      simpa [hDiv, hMod] using hTarget
    rw [hSource, hDestination]
    simp [hij]

@[simp] theorem pToH_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (i h : Nat) (hi : i < 7) (hh : h < 7) :
    Core.pToH (coreBits R p a z) i h =
      decide (R (p ⟨i, hi⟩) (a ⟨h + 1, by omega⟩)) := by
  rw [Core.pToH, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (7 * i + h) / 7 = i := by omega
  have hm : (7 * i + h) % 7 = h := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hh
  simp [coreBitAt, show ¬88 + 7 * i + h < 4 by omega,
    show ¬88 + 7 * i + h < 46 by omega, show ¬88 + 7 * i + h < 88 by omega,
    show 88 + 7 * i + h < 137 by omega,
    show 88 + 7 * i + h - 88 = 7 * i + h by omega, hd, hm]

@[simp] theorem hToP_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (h i : Nat) (hh : h < 7) (hi : i < 7) :
    Core.hToP (coreBits R p a z) h i =
      decide (R (a ⟨h + 1, by omega⟩) (p ⟨i, hi⟩)) := by
  rw [Core.hToP, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (7 * h + i) / 7 = h := by omega
  have hm : (7 * h + i) % 7 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := h) hi
  simp [coreBitAt, show ¬137 + 7 * h + i < 4 by omega,
    show ¬137 + 7 * h + i < 46 by omega,
    show ¬137 + 7 * h + i < 88 by omega,
    show ¬137 + 7 * h + i < 137 by omega,
    show 137 + 7 * h + i < 186 by omega,
    show 137 + 7 * h + i - 137 = 7 * h + i by omega, hd, hm]

@[simp] theorem pToZ_coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (i j : Nat) (hi : i < 7)
    (hj5 : j < 5) (hj : j < zCount) :
    Core.pToZ (coreBits R p a z) i j =
      decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [Core.pToZ, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (5 * i + j) / 5 = i := by omega
  have hm : (5 * i + j) % 5 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj5
  simp [coreBitAt, show ¬186 + 5 * i + j < 4 by omega,
    show ¬186 + 5 * i + j < 46 by omega,
    show ¬186 + 5 * i + j < 88 by omega,
    show ¬186 + 5 * i + j < 137 by omega,
    show ¬186 + 5 * i + j < 186 by omega,
    show 186 + 5 * i + j < 221 by omega,
    show 186 + 5 * i + j - 186 = 5 * i + j by omega, hd, hm, hj]

@[simp] theorem pToZ_coreBits_inactive {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V) (i j : Nat) (hi : i < 7)
    (hj5 : j < 5) (hj : ¬j < zCount) :
    Core.pToZ (coreBits R p a z) i j = false := by
  rw [Core.pToZ, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (5 * i + j) / 5 = i := by omega
  have hm : (5 * i + j) % 5 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj5
  simp [coreBitAt, show ¬186 + 5 * i + j < 4 by omega,
    show ¬186 + 5 * i + j < 46 by omega,
    show ¬186 + 5 * i + j < 88 by omega,
    show ¬186 + 5 * i + j < 137 by omega,
    show ¬186 + 5 * i + j < 186 by omega,
    show 186 + 5 * i + j < 221 by omega,
    show 186 + 5 * i + j - 186 = 5 * i + j by omega, hm, hj]

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding
