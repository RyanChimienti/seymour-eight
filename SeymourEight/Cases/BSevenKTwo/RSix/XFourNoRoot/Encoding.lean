import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.CoreDefs

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Bridge

open Core

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 6 → V) (h : Fin 6 → V) (e : Fin 3 → V)
    (n : Nat) : Bool :=
  if hnPP : n < 30 then
    let i := n / 5
    let j0 := n % 5
    let j := if j0 < i then j0 else j0 + 1
    decide (R (p ⟨i, by omega⟩) (p ⟨j, by
      have hj0 : j0 < 5 := Nat.mod_lt _ (by omega)
      dsimp [j, j0, i]
      split <;> omega⟩))
  else if hnPH : n < 66 then
    let q := n - 30
    decide (R (p ⟨q / 6, by omega⟩) (h ⟨q % 6, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 102 then
    let q := n - 66
    decide (R (h ⟨q / 6, by omega⟩) (p ⟨q % 6, Nat.mod_lt _ (by omega)⟩))
  else if hnPE : n < 120 then
    let q := n - 102
    decide (R (p ⟨q / 3, by omega⟩) (e ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else if hnPair : n < 122 then
    let a := n - 120
    decide (R (h ⟨a, by omega⟩) (h ⟨1 - a, by omega⟩))
  else if hnAX : n < 130 then
    let q := n - 122
    decide (R (h ⟨q / 4, by omega⟩) (h ⟨2 + q % 4, by omega⟩))
  else if hnAE : n < 136 then
    let q := n - 130
    decide (R (h ⟨q / 3, by omega⟩) (e ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 6 → V) (h : Fin 6 → V) (e : Fin 3 → V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 136 => coreBitAt R p h e n))

@[simp] theorem getLsbD_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (n : Nat) (hn : n < 136) :
    (coreBits R p h e).getLsbD n = coreBitAt R p h e n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn)
      false, List.getElem_ofFn]

private theorem div_index (i j w : Nat) (hj : j < w) :
    (i * w + j) / w = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j w : Nat) (hj : j < w) :
    (i * w + j) % w = j := Nat.mul_add_mod_of_lt hj

@[simp] theorem pArc_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 6) (hj : j < 6) :
    pArc (coreBits R p h e) i j =
      decide (i ≠ j ∧ R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [pArc]
  · have hIndex : directedIndex i j < 30 := by
      unfold directedIndex
      split <;> omega
    rw [pArc, getLsbD_coreBits R p h e (directedIndex i j) (by omega)]
    have hDiv : directedIndex i j / 5 = i := by
      unfold directedIndex
      split <;> omega
    have hMod : directedIndex i j % 5 = if j < i then j else j - 1 := by
      by_cases hji : j < i
      · simpa [directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j < 5 by omega)
      · simpa [directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j - 1 < 5 by omega)
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
    simp only [coreBitAt, dif_pos hIndex]
    have hs : p ⟨directedIndex i j / 5, by omega⟩ = p ⟨i, hi⟩ := by
      apply congrArg p
      exact Fin.ext hDiv
    let targetIndex := if directedIndex i j % 5 < directedIndex i j / 5 then
      directedIndex i j % 5 else directedIndex i j % 5 + 1
    have hTargetIndexLt : targetIndex < 6 := by
      dsimp [targetIndex]
      rw [hDiv, hMod]
      rw [hTarget]
      exact hj
    have ht : p ⟨targetIndex, hTargetIndexLt⟩ = p ⟨j, hj⟩ := by
      apply congrArg p
      apply Fin.ext
      dsimp [targetIndex]
      rw [hDiv, hMod]
      exact hTarget
    rw [hs, ht]
    simp [hij]

@[simp] theorem pToH_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 6) (hj : j < 6) :
    pToH (coreBits R p h e) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  rw [pToH, getLsbD_coreBits R p h e (30 + 6 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬30 + 6 * i + j < 30),
    dif_pos (by omega : 30 + 6 * i + j < 66)]
  have hd : (6 * i + j) / 6 = i := by
    simpa [Nat.mul_comm] using div_index i j 6 hj
  have hm : (6 * i + j) % 6 = j := by
    simpa [Nat.mul_comm] using mod_index i j 6 hj
  simp [show 30 + 6 * i + j - 30 = 6 * i + j by omega, hd, hm]

@[simp] theorem hToP_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 6) (hj : j < 6) :
    hToP (coreBits R p h e) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [hToP, getLsbD_coreBits R p h e (66 + 6 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬66 + 6 * i + j < 30),
    dif_neg (by omega : ¬66 + 6 * i + j < 66),
    dif_pos (by omega : 66 + 6 * i + j < 102)]
  have hd : (6 * i + j) / 6 = i := by
    simpa [Nat.mul_comm] using div_index i j 6 hj
  have hm : (6 * i + j) % 6 = j := by
    simpa [Nat.mul_comm] using mod_index i j 6 hj
  simp [show 66 + 6 * i + j - 66 = 6 * i + j by omega, hd, hm]

@[simp] theorem pToE_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 6) (hj : j < 3) :
    pToE (coreBits R p h e) i j = decide (R (p ⟨i, hi⟩) (e ⟨j, hj⟩)) := by
  rw [pToE, getLsbD_coreBits R p h e (102 + 3 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬102 + 3 * i + j < 30),
    dif_neg (by omega : ¬102 + 3 * i + j < 66),
    dif_neg (by omega : ¬102 + 3 * i + j < 102),
    dif_pos (by omega : 102 + 3 * i + j < 120)]
  have hd : (3 * i + j) / 3 = i := by
    simpa [Nat.mul_comm] using div_index i j 3 hj
  have hm : (3 * i + j) % 3 = j := by
    simpa [Nat.mul_comm] using mod_index i j 3 hj
  simp [show 102 + 3 * i + j - 102 = 3 * i + j by omega, hd, hm]

@[simp] theorem aPair_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 2) (hj : j < 2) :
    aPair (coreBits R p h e) i j =
      decide (i ≠ j ∧ R (h ⟨i, by omega⟩) (h ⟨j, by omega⟩)) := by
  by_cases hij : i = j
  · subst j
    simp [aPair]
  · rw [aPair, getLsbD_coreBits R p h e (120 + i) (by omega)]
    simp only [coreBitAt, dif_neg (by omega : ¬120 + i < 30),
      dif_neg (by omega : ¬120 + i < 66),
      dif_neg (by omega : ¬120 + i < 102),
      dif_neg (by omega : ¬120 + i < 120),
      dif_pos (by omega : 120 + i < 122)]
    have hji : 1 - i = j := by omega
    simp [hij, hji]

@[simp] theorem aToX_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 2) (hj : j < 4) :
    aToX (coreBits R p h e) i j =
      decide (R (h ⟨i, by omega⟩) (h ⟨2 + j, by omega⟩)) := by
  rw [aToX, getLsbD_coreBits R p h e (122 + 4 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬122 + 4 * i + j < 30),
    dif_neg (by omega : ¬122 + 4 * i + j < 66),
    dif_neg (by omega : ¬122 + 4 * i + j < 102),
    dif_neg (by omega : ¬122 + 4 * i + j < 120),
    dif_neg (by omega : ¬122 + 4 * i + j < 122),
    dif_pos (by omega : 122 + 4 * i + j < 130)]
  have hd : (4 * i + j) / 4 = i := by
    simpa [Nat.mul_comm] using div_index i j 4 hj
  have hm : (4 * i + j) % 4 = j := by
    simpa [Nat.mul_comm] using mod_index i j 4 hj
  simp [show 122 + 4 * i + j - 122 = 4 * i + j by omega, hd, hm]

@[simp] theorem aToE_coreBits (p : Fin 6 → V) (h : Fin 6 → V)
    (e : Fin 3 → V) (i j : Nat) (hi : i < 2) (hj : j < 3) :
    aToE (coreBits R p h e) i j =
      decide (R (h ⟨i, by omega⟩) (e ⟨j, hj⟩)) := by
  rw [aToE, getLsbD_coreBits R p h e (130 + 3 * i + j) (by omega)]
  simp only [coreBitAt, dif_neg (by omega : ¬130 + 3 * i + j < 30),
    dif_neg (by omega : ¬130 + 3 * i + j < 66),
    dif_neg (by omega : ¬130 + 3 * i + j < 102),
    dif_neg (by omega : ¬130 + 3 * i + j < 120),
    dif_neg (by omega : ¬130 + 3 * i + j < 122),
    dif_neg (by omega : ¬130 + 3 * i + j < 130),
    dif_pos (by omega : 130 + 3 * i + j < 136)]
  have hd : (3 * i + j) / 3 = i := by
    simpa [Nat.mul_comm] using div_index i j 3 hj
  have hm : (3 * i + j) % 3 = j := by
    simpa [Nat.mul_comm] using mod_index i j 3 hj
  simp [show 130 + 3 * i + j - 130 = 3 * i + j by omega, hd, hm]

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Bridge
