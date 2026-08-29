import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.Labels
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.CoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Encoding

open Labels Core

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]
variable {G : Digraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def coreBitAt {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (n : Nat) : Bool :=
  if hnA : n < 64 then
    decide (R (L.a ⟨n / 8, by omega⟩).1
      (L.a ⟨n % 8, Nat.mod_lt _ (by omega)⟩).1)
  else if hnP : n < 94 then
    let k := n - 64
    let i := k / 5
    let j0 := k % 5
    let j := if j0 < i then j0 else j0 + 1
    decide (R (L.p ⟨i, by omega⟩).1 (L.p ⟨j, by
      have hj0 : j0 < 5 := Nat.mod_lt _ (by omega)
      dsimp [j]
      split <;> omega⟩).1)
  else if hnPH : n < 118 then
    let k := n - 94
    decide (R (L.p ⟨k / 4, by omega⟩).1
      (L.a ⟨k % 4 + 1, by have := Nat.mod_lt k (by omega : 0 < 4); omega⟩).1)
  else if hnHP : n < 142 then
    let k := n - 118
    decide (R (L.a ⟨k / 6 + 1, by omega⟩).1
      (L.p ⟨k % 6, Nat.mod_lt _ (by omega)⟩).1)
  else if hnPE : n < 172 then
    let k := n - 142
    decide (R (L.p ⟨k / 5, by omega⟩).1
      (L.e ⟨k % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnRP : n < 190 then
    let k := n - 172
    decide (R (L.a ⟨k / 6 + 5, by omega⟩).1
      (L.p ⟨k % 6, Nat.mod_lt _ (by omega)⟩).1)
  else if hnAQ : n < 197 then
    decide (R (L.a ⟨n - 190 + 1, by omega⟩).1 q)
  else false

def coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) : Core.Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 197 => coreBitAt R L n))

@[simp] theorem getLsbD_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (n : Nat) (hn : n < 197) :
    (coreBits R L).getLsbD n = coreBitAt R L n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

@[simp] theorem aArc_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (coreBits R L) i j =
      decide (R (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  rw [aArc, getLsbD_coreBits R L _ (by omega)]
  have hd : (8 * i + j) / 8 = i := by omega
  have hm : (8 * i + j) % 8 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  simp [coreBitAt, show 8 * i + j < 64 by omega, hd, hm]

@[simp] theorem pArc_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (i j : Nat) (hi : i < 6) (hj : j < 6) :
    pArc (coreBits R L) i j =
      decide (i ≠ j ∧ R (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1) := by
  by_cases hij : i = j
  · subst j
    simp [pArc]
  · rw [pArc, getLsbD_coreBits R L _ (by
      unfold directedIndex
      split <;> omega)]
    have hIndex : 64 + directedIndex i j < 94 := by
      unfold directedIndex
      split <;> omega
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
    simp only [coreBitAt, dif_neg (by omega : ¬64 + directedIndex i j < 64),
      dif_pos hIndex,
      show 64 + directedIndex i j - 64 = directedIndex i j by omega]
    rw [show L.p ⟨directedIndex i j / 5, by omega⟩ = L.p ⟨i, hi⟩ by
      congr 1; exact Fin.ext hDiv]
    rw [show L.p ⟨if directedIndex i j % 5 < directedIndex i j / 5 then
          directedIndex i j % 5 else directedIndex i j % 5 + 1, by
          have := Nat.mod_lt (directedIndex i j) (by omega : 0 < 5)
          split <;> omega⟩ = L.p ⟨j, hj⟩ by
      congr 1; apply Fin.ext; simpa [hDiv, hMod] using hTarget]
    simp [hij]

@[simp] theorem pToH_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (i h : Nat) (hi : i < 6) (hh : h < 4) :
    pToH (coreBits R L) i h =
      decide (R (L.p ⟨i, hi⟩).1 (L.a ⟨h + 1, by omega⟩).1) := by
  rw [pToH, getLsbD_coreBits R L _ (by omega)]
  have hd : (4 * i + h) / 4 = i := by omega
  have hm : (4 * i + h) % 4 = h := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hh
  simp [coreBitAt, show ¬94 + 4 * i + h < 64 by omega,
    show ¬94 + 4 * i + h < 94 by omega,
    show 94 + 4 * i + h < 118 by omega,
    show 94 + 4 * i + h - 94 = 4 * i + h by omega, hd, hm]

@[simp] theorem hToP_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (h i : Nat) (hh : h < 4) (hi : i < 6) :
    hToP (coreBits R L) h i =
      decide (R (L.a ⟨h + 1, by omega⟩).1 (L.p ⟨i, hi⟩).1) := by
  rw [hToP, getLsbD_coreBits R L _ (by omega)]
  have hd : (6 * h + i) / 6 = h := by omega
  have hm : (6 * h + i) % 6 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := h) hi
  simp [coreBitAt, show ¬118 + 6 * h + i < 64 by omega,
    show ¬118 + 6 * h + i < 94 by omega,
    show ¬118 + 6 * h + i < 118 by omega,
    show 118 + 6 * h + i < 142 by omega,
    show 118 + 6 * h + i - 118 = 6 * h + i by omega, hd, hm]

@[simp] theorem pToE_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (i e : Nat) (hi : i < 6) (he : e < 5) :
    pToE (coreBits R L) i e =
      decide (R (L.p ⟨i, hi⟩).1 (L.e ⟨e, he⟩)) := by
  rw [pToE, getLsbD_coreBits R L _ (by omega)]
  have hd : (5 * i + e) / 5 = i := by omega
  have hm : (5 * i + e) % 5 = e := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) he
  simp [coreBitAt, show ¬142 + 5 * i + e < 64 by omega,
    show ¬142 + 5 * i + e < 94 by omega,
    show ¬142 + 5 * i + e < 118 by omega,
    show ¬142 + 5 * i + e < 142 by omega,
    show 142 + 5 * i + e < 172 by omega,
    show 142 + 5 * i + e - 142 = 5 * i + e by omega, hd, hm]

@[simp] theorem rToP_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (r i : Nat) (hr : r < 3) (hi : i < 6) :
    rToP (coreBits R L) r i =
      decide (R (L.a ⟨r + 5, by omega⟩).1 (L.p ⟨i, hi⟩).1) := by
  rw [rToP, getLsbD_coreBits R L _ (by omega)]
  have hd : (6 * r + i) / 6 = r := by omega
  have hm : (6 * r + i) % 6 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := r) hi
  simp [coreBitAt, show ¬172 + 6 * r + i < 64 by omega,
    show ¬172 + 6 * r + i < 94 by omega,
    show ¬172 + 6 * r + i < 118 by omega,
    show ¬172 + 6 * r + i < 142 by omega,
    show ¬172 + 6 * r + i < 172 by omega,
    show 172 + 6 * r + i < 190 by omega,
    show 172 + 6 * r + i - 172 = 6 * r + i by omega, hd, hm]

@[simp] theorem aToQ_coreBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (a : Nat) (ha : a < 8) :
    aToQ (coreBits R L) a =
      decide (a ≠ 0 ∧ R (L.a ⟨a, ha⟩).1 q) := by
  by_cases ha0 : a = 0
  · subst a
    simp [aToQ]
  · rw [aToQ, if_neg ha0, getLsbD_coreBits R L _ (by omega)]
    have hidx : (⟨190 + a - 1 - 190 + 1, by omega⟩ : Fin 8) =
        ⟨a, ha⟩ := by ext; simp; omega
    simp only [coreBitAt, dif_neg (by omega : ¬190 + a - 1 < 64),
      dif_neg (by omega : ¬190 + a - 1 < 94),
      dif_neg (by omega : ¬190 + a - 1 < 118),
      dif_neg (by omega : ¬190 + a - 1 < 142),
      dif_neg (by omega : ¬190 + a - 1 < 172),
      dif_neg (by omega : ¬190 + a - 1 < 190),
      dif_pos (by omega : 190 + a - 1 < 197)]
    rw [hidx]
    simp [ha0]

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Encoding
