import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeCoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Graph encoding for the three-`Z` projected core

This module is deliberately independent of the defect reduction.  It records
the four incidence blocks consumed by `ZThreeCore.Encoding` and proves the
decoder equations once, so the later counting and normalization arguments do
not reason about physical bit positions.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeBridge

open ZThreeCore

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (h : Fin 6 → V) (z : Fin 3 → V)
    (n : Nat) : Bool :=
  if hnP : n < 42 then
    let i := n / 6
    let j0 := n % 6
    let j := if j0 < i then j0 else j0 + 1
    decide (R (p ⟨i, by
      have hi : n / 6 < 7 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      exact hi⟩) (p ⟨j, by
        have hj0 : n % 6 < 6 := Nat.mod_lt _ (by omega)
        have hi : n / 6 < 7 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
        dsimp [j, j0, i]
        split <;> omega⟩))
  else if hnPH : n < 84 then
    let q := n - 42
    decide (R (p ⟨q / 6, by omega⟩)
      (h ⟨q % 6, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 126 then
    let q := n - 84
    decide (R (h ⟨q / 7, by omega⟩)
      (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPZ : n < 147 then
    let q := n - 126
    decide (R (p ⟨q / 3, by omega⟩)
      (z ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 7 → V) (h : Fin 6 → V) (z : Fin 3 → V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 147 ↦ coreBitAt R p h z n))

@[simp] theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 6 → V)
    (z : Fin 3 → V) (n : Nat) (hn : n < 147) :
    (coreBits R p h z).getLsbD n = coreBitAt R p h z n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa using hn) false,
    List.getElem_ofFn]

@[simp] theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 6 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p h z) i j =
      decide (i ≠ j ∧ R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [pArc]
  · have hIndex : directedIndex i j < 42 := by
      unfold directedIndex
      split <;> omega
    rw [pArc, getLsbD_coreBits R p h z (directedIndex i j) (by omega)]
    have hDiv : directedIndex i j / 6 = i := by
      unfold directedIndex
      split <;> omega
    have hMod : directedIndex i j % 6 = if j < i then j else j - 1 := by
      by_cases hji : j < i
      · have hj6 : j < 6 := by omega
        simpa [directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) hj6
      · have hj6 : j - 1 < 6 := by omega
        simpa [directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) hj6
    have hjCode : (if j < i then j else j - 1) < 6 := by
      split <;> omega
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
    have hPSource :
        p ⟨directedIndex i j / 6, by omega⟩ = p ⟨i, hi⟩ := by
      apply congrArg p
      exact Fin.ext hDiv
    have hPTarget :
        p ⟨if directedIndex i j % 6 < directedIndex i j / 6 then
            directedIndex i j % 6 else directedIndex i j % 6 + 1, by
              have hRem : directedIndex i j % 6 < 6 := Nat.mod_lt _ (by omega)
              have hQuot : directedIndex i j / 6 < 7 :=
                (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
              split <;> omega⟩ =
          p ⟨j, hj⟩ := by
      apply congrArg p
      apply Fin.ext
      simpa [hDiv, hMod] using hTarget
    simp only [coreBitAt, dif_pos hIndex]
    rw [hPSource, hPTarget]
    simp [hij]

@[simp] theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 6 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 7) (hj : j < 6) :
    pToH (coreBits R p h z) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  have hIndex : 42 + 6 * i + j < 84 := by omega
  have hSub : 42 + 6 * i + j - 42 = 6 * i + j := by omega
  have hDiv : (6 * i + j) / 6 = i := by omega
  have hMod : (6 * i + j) % 6 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  rw [pToH, getLsbD_coreBits R p h z (42 + 6 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬42 + 6 * i + j < 42),
    dif_pos hIndex, hSub, hDiv, hMod]

@[simp] theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 6 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 6) (hj : j < 7) :
    hToP (coreBits R p h z) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  have hIndex : 84 + 7 * i + j < 126 := by omega
  have hSub : 84 + 7 * i + j - 84 = 7 * i + j := by omega
  have hDiv : (7 * i + j) / 7 = i := by omega
  have hMod : (7 * i + j) % 7 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  rw [hToP, getLsbD_coreBits R p h z (84 + 7 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬84 + 7 * i + j < 42),
    dif_neg (by omega : ¬84 + 7 * i + j < 84), dif_pos hIndex,
    hSub, hDiv, hMod]

@[simp] theorem pToZ_coreBits (p : Fin 7 → V) (h : Fin 6 → V)
    (z : Fin 3 → V) (i j : Nat) (hi : i < 7) (hj : j < 3) :
    pToZ (coreBits R p h z) i j = decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  have hIndex : 126 + 3 * i + j < 147 := by omega
  have hSub : 126 + 3 * i + j - 126 = 3 * i + j := by omega
  have hDiv : (3 * i + j) / 3 = i := by omega
  have hMod : (3 * i + j) % 3 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  rw [pToZ, getLsbD_coreBits R p h z (126 + 3 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬126 + 3 * i + j < 42),
    dif_neg (by omega : ¬126 + 3 * i + j < 84),
    dif_neg (by omega : ¬126 + 3 * i + j < 126), dif_pos hIndex,
    hSub, hDiv, hMod]

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeBridge
