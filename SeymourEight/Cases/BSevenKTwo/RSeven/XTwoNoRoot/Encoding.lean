import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoNoRoot.Labels
import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.CoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Encoding

open Labels Core

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) (n : Nat) : Bool :=
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
  else if hnPH : n < 134 then
    let q := n - 106
    decide (R (p ⟨q / 4, by omega⟩)
      (a ⟨q % 4 + 1, by have := Nat.mod_lt q (by omega : 0 < 4); omega⟩))
  else if hnHP : n < 162 then
    let q := n - 134
    decide (R (a ⟨q / 7 + 1, by omega⟩)
      (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPZ : n < 204 then
    let q := n - 162
    let j := q % 6
    if hj : j < zCount then
      decide (R (p ⟨q / 6, by omega⟩) (z ⟨j, hj⟩))
    else false
  else if hnRP : n < 225 then
    let q := n - 204
    decide (R (a ⟨q / 7 + 5, by omega⟩)
      (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits {zCount : Nat} (p : Fin 7 → V) (a : Fin 8 → V)
    (z : Fin zCount → V) : Core.Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 225 => coreBitAt R p a z n))

@[simp] theorem getLsbD_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V) (n : Nat) (hn : n < 225) :
    (coreBits R p a z).getLsbD n = coreBitAt R p a z n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

@[simp] theorem aArc_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    Core.aArc (coreBits R p a z) i j = decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [Core.aArc, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (8 * i + j) / 8 = i := by omega
  have hm : (8 * i + j) % 8 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  simp [coreBitAt, show 8 * i + j < 64 by omega, hd, hm]

@[simp] theorem pArc_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    Core.pArc (coreBits R p a z) i j =
      decide (i ≠ j ∧ R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [Core.pArc]
  · have hIndex : 64 + Core.directedIndex i j < 106 := by
      unfold Core.directedIndex
      split <;> omega
    rw [Core.pArc, getLsbD_coreBits R p a z _ (by omega)]
    have hDiv : Core.directedIndex i j / 6 = i := by
      unfold Core.directedIndex
      split <;> omega
    have hMod : Core.directedIndex i j % 6 = if j < i then j else j - 1 := by
      by_cases hji : j < i
      · simpa [Core.directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j < 6 by omega)
      · simpa [Core.directedIndex, hji, Nat.mul_comm] using
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
    simp only [coreBitAt, dif_neg (by omega : ¬64 + Core.directedIndex i j < 64),
      dif_pos hIndex, show 64 + Core.directedIndex i j - 64 =
        Core.directedIndex i j by omega]
    have hSource : p ⟨Core.directedIndex i j / 6, by omega⟩ = p ⟨i, hi⟩ := by
      apply congrArg p
      exact Fin.ext hDiv
    have hDestination :
        p ⟨if Core.directedIndex i j % 6 < Core.directedIndex i j / 6 then
              Core.directedIndex i j % 6 else Core.directedIndex i j % 6 + 1, by
            have := Nat.mod_lt (Core.directedIndex i j) (by omega : 0 < 6)
            split <;> omega⟩ = p ⟨j, hj⟩ := by
      apply congrArg p
      apply Fin.ext
      simpa [hDiv, hMod] using hTarget
    rw [hSource, hDestination]
    simp [hij]

@[simp] theorem pToH_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (i h : Nat) (hi : i < 7) (hh : h < 4) :
    Core.pToH (coreBits R p a z) i h =
      decide (R (p ⟨i, hi⟩) (a ⟨h + 1, by omega⟩)) := by
  rw [Core.pToH, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (4 * i + h) / 4 = i := by omega
  have hm : (4 * i + h) % 4 = h := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hh
  simp [coreBitAt, show ¬106 + 4 * i + h < 64 by omega,
    show ¬106 + 4 * i + h < 106 by omega,
    show 106 + 4 * i + h < 134 by omega,
    show 106 + 4 * i + h - 106 = 4 * i + h by omega, hd, hm]

@[simp] theorem hToP_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (h i : Nat) (hh : h < 4) (hi : i < 7) :
    Core.hToP (coreBits R p a z) h i =
      decide (R (a ⟨h + 1, by omega⟩) (p ⟨i, hi⟩)) := by
  rw [Core.hToP, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (7 * h + i) / 7 = h := by omega
  have hm : (7 * h + i) % 7 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := h) hi
  simp [coreBitAt, show ¬134 + 7 * h + i < 64 by omega,
    show ¬134 + 7 * h + i < 106 by omega,
    show ¬134 + 7 * h + i < 134 by omega,
    show 134 + 7 * h + i < 162 by omega,
    show 134 + 7 * h + i - 134 = 7 * h + i by omega, hd, hm]

@[simp] theorem pToZ_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (i j : Nat) (hi : i < 7) (hj6 : j < 6) (hj : j < zCount) :
    Core.pToZ (coreBits R p a z) i j =
      decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [Core.pToZ, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (6 * i + j) / 6 = i := by omega
  have hm : (6 * i + j) % 6 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj6
  simp [coreBitAt, show ¬162 + 6 * i + j < 64 by omega,
    show ¬162 + 6 * i + j < 106 by omega,
    show ¬162 + 6 * i + j < 134 by omega,
    show ¬162 + 6 * i + j < 162 by omega,
    show 162 + 6 * i + j < 204 by omega,
    show 162 + 6 * i + j - 162 = 6 * i + j by omega, hd, hm, hj]

@[simp] theorem pToZ_coreBits_inactive {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (i j : Nat) (hi : i < 7) (hj6 : j < 6) (hj : ¬j < zCount) :
    Core.pToZ (coreBits R p a z) i j = false := by
  rw [Core.pToZ, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (6 * i + j) / 6 = i := by omega
  have hm : (6 * i + j) % 6 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj6
  simp [coreBitAt, show ¬162 + 6 * i + j < 64 by omega,
    show ¬162 + 6 * i + j < 106 by omega,
    show ¬162 + 6 * i + j < 134 by omega,
    show ¬162 + 6 * i + j < 162 by omega,
    show 162 + 6 * i + j < 204 by omega,
    show 162 + 6 * i + j - 162 = 6 * i + j by omega, hm, hj]

@[simp] theorem rToP_coreBits {zCount : Nat} (p : Fin 7 → V)
    (a : Fin 8 → V) (z : Fin zCount → V)
    (r i : Nat) (hr : r < 3) (hi : i < 7) :
    Core.rToP (coreBits R p a z) r i =
      decide (R (a ⟨r + 5, by omega⟩) (p ⟨i, hi⟩)) := by
  rw [Core.rToP, getLsbD_coreBits R p a z _ (by omega)]
  have hd : (7 * r + i) / 7 = r := by omega
  have hm : (7 * r + i) % 7 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := r) hi
  simp [coreBitAt, show ¬204 + 7 * r + i < 64 by omega,
    show ¬204 + 7 * r + i < 106 by omega,
    show ¬204 + 7 * r + i < 134 by omega,
    show ¬204 + 7 * r + i < 162 by omega,
    show ¬204 + 7 * r + i < 204 by omega,
    show 204 + 7 * r + i < 225 by omega,
    show 204 + 7 * r + i - 204 = 7 * r + i by omega, hd, hm]

end SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Encoding
