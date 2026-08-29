import SeymourEight.Cases.BSevenKTwo.RSix.XThreeNoRoot.Labels
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.UnreachedCoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedEncoding

open Labels UnreachedCore

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]
variable {G : Digraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def coreBitAt {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (n : Nat) : Bool :=
  if hnA : n < 64 then
    decide (R (L.a ⟨n / 8, by omega⟩).1
      (L.a ⟨n % 8, Nat.mod_lt _ (by omega)⟩).1)
  else if hnP : n < 106 then
    let k := n - 64
    let i := k / 6
    let j0 := k % 6
    let j := if j0 < i then j0 else j0 + 1
    if hi : i < 6 then
      if hj : j < 6 then decide (R (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1)
      else false
    else false
  else if hnPH : n < 141 then
    let k := n - 106
    let i := k / 5
    let h := k % 5
    if hi : i < 6 then
      decide (R (L.p ⟨i, hi⟩).1 (L.a ⟨h + 1, by omega⟩).1)
    else decide (R (L.a ⟨h + 1, by omega⟩).1 q)
  else if hnHP : n < 176 then
    let k := n - 141
    let h := k / 7
    let i := k % 7
    if hi : i < 6 then
      decide (R (L.a ⟨h + 1, by omega⟩).1 (L.p ⟨i, hi⟩).1)
    else false
  else if hnPZ : n < 211 then
    let k := n - 176
    let i := k / 5
    let z := k % 5
    if hi : i < 6 then
      if hz : z < 4 then decide (R (L.p ⟨i, hi⟩).1 (L.z ⟨z, hz⟩).1)
      else false
    else if hz : z < 2 then decide (R (L.a ⟨z + 6, by omega⟩).1 q)
    else false
  else if hnRP : n < 225 then
    let k := n - 211
    let r := k / 7
    let i := k % 7
    if hi : i < 6 then
      decide (R (L.a ⟨r + 6, by omega⟩).1 (L.p ⟨i, hi⟩).1)
    else false
  else false

def coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) : UnreachedCore.Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 225 ↦ coreBitAt R L n))

@[simp] theorem getLsbD_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (n : Nat) (hn : n < 225) :
    (coreBits R L).getLsbD n = coreBitAt R L n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

@[simp] theorem aArc_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    Core.aArc (coreBits R L) i j =
      decide (R (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  rw [Core.aArc, RSeven.XThreeNoRoot.Core.aArc,
    getLsbD_coreBits R L _ (by omega)]
  have hd : (8 * i + j) / 8 = i := by omega
  have hm : (8 * i + j) % 8 = j := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
  simp [coreBitAt, show 8 * i + j < 64 by omega, hd, hm]

@[simp] theorem pArc_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (i j : Nat) (hi : i < 6) (hj : j < 6) :
    Core.pArc (coreBits R L) i j =
      decide (i ≠ j ∧ R (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1) := by
  by_cases hij : i = j
  · subst j; simp [Core.pArc, RSeven.XThreeNoRoot.Core.pArc]
  · have hIndex : 64 + RSeven.XThreeNoRoot.Core.directedIndex i j < 106 := by
      unfold RSeven.XThreeNoRoot.Core.directedIndex
      split <;> omega
    rw [Core.pArc, RSeven.XThreeNoRoot.Core.pArc,
      getLsbD_coreBits R L _ (by omega)]
    have hDiv : RSeven.XThreeNoRoot.Core.directedIndex i j / 6 = i := by
      unfold RSeven.XThreeNoRoot.Core.directedIndex
      split <;> omega
    have hMod : RSeven.XThreeNoRoot.Core.directedIndex i j % 6 =
        if j < i then j else j - 1 := by
      by_cases hji : j < i
      · simpa [RSeven.XThreeNoRoot.Core.directedIndex, hji, Nat.mul_comm] using
          Nat.mul_add_mod_of_lt (a := i) (show j < 6 by omega)
      · simpa [RSeven.XThreeNoRoot.Core.directedIndex, hji, Nat.mul_comm] using
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
    simp only [coreBitAt,
      dif_neg (by omega : ¬64 + RSeven.XThreeNoRoot.Core.directedIndex i j < 64),
      dif_pos hIndex,
      show 64 + RSeven.XThreeNoRoot.Core.directedIndex i j - 64 =
        RSeven.XThreeNoRoot.Core.directedIndex i j by omega]
    rw [dif_pos (by simpa [hDiv] using hi)]
    rw [dif_pos (by simpa [hDiv, hMod, hTarget] using hj)]
    simp only [hDiv, hMod, hTarget]
    simp [hij]

@[simp] theorem pToH_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (i h : Nat) (hi : i < 6) (hh : h < 5) :
    Core.pToH (coreBits R L) i h =
      decide (R (L.p ⟨i, hi⟩).1 (L.a ⟨h + 1, by omega⟩).1) := by
  rw [Core.pToH, RSeven.XThreeNoRoot.Core.pToH,
    getLsbD_coreBits R L _ (by omega)]
  have hd : (5 * i + h) / 5 = i := by omega
  have hm : (5 * i + h) % 5 = h := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hh
  simp [coreBitAt, show ¬106 + 5 * i + h < 64 by omega,
    show ¬106 + 5 * i + h < 106 by omega,
    show 106 + 5 * i + h < 141 by omega,
    show 106 + 5 * i + h - 106 = 5 * i + h by omega, hd, hm, hi]

@[simp] theorem hToP_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (h i : Nat) (hh : h < 5) (hi : i < 6) :
    Core.hToP (coreBits R L) h i =
      decide (R (L.a ⟨h + 1, by omega⟩).1 (L.p ⟨i, hi⟩).1) := by
  rw [Core.hToP, RSeven.XThreeNoRoot.Core.hToP,
    getLsbD_coreBits R L _ (by omega)]
  have hd : (7 * h + i) / 7 = h := by omega
  have hm : (7 * h + i) % 7 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := h)
      (show i < 7 by omega)
  simp [coreBitAt, show ¬141 + 7 * h + i < 64 by omega,
    show ¬141 + 7 * h + i < 106 by omega,
    show ¬141 + 7 * h + i < 141 by omega,
    show 141 + 7 * h + i < 176 by omega,
    show 141 + 7 * h + i - 141 = 7 * h + i by omega, hd, hm, hi]

@[simp] theorem pToZ_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (i z : Nat) (hi : i < 6) (hz : z < 4) :
    Core.pToE (coreBits R L) i z =
      decide (R (L.p ⟨i, hi⟩).1 (L.z ⟨z, hz⟩).1) := by
  rw [Core.pToE, RSeven.XThreeNoRoot.Core.pToZ,
    getLsbD_coreBits R L _ (by omega)]
  have hd : (5 * i + z) / 5 = i := by omega
  have hm : (5 * i + z) % 5 = z := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i)
      (show z < 5 by omega)
  simp [coreBitAt, show ¬176 + 5 * i + z < 64 by omega,
    show ¬176 + 5 * i + z < 106 by omega,
    show ¬176 + 5 * i + z < 141 by omega,
    show ¬176 + 5 * i + z < 176 by omega,
    show 176 + 5 * i + z < 211 by omega,
    show 176 + 5 * i + z - 176 = 5 * i + z by omega, hd, hm, hi, hz]

@[simp] theorem rToP_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (r i : Nat) (hr : r < 2) (hi : i < 6) :
    Core.rToP (coreBits R L) r i =
      decide (R (L.a ⟨r + 6, by omega⟩).1 (L.p ⟨i, hi⟩).1) := by
  rw [Core.rToP, RSeven.XThreeNoRoot.Core.rToP,
    getLsbD_coreBits R L _ (by omega)]
  have hd : (7 * r + i) / 7 = r := by omega
  have hm : (7 * r + i) % 7 = i := by
    simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := r)
      (show i < 7 by omega)
  simp [coreBitAt, show ¬211 + 7 * r + i < 64 by omega,
    show ¬211 + 7 * r + i < 106 by omega,
    show ¬211 + 7 * r + i < 141 by omega,
    show ¬211 + 7 * r + i < 176 by omega,
    show ¬211 + 7 * r + i < 211 by omega,
    show 211 + 7 * r + i < 225 by omega,
    show 211 + 7 * r + i - 211 = 7 * r + i by omega, hd, hm, hi]

@[simp] theorem aToQ_coreBits {C : G.LocalConfiguration} {q : V}
    (L : UnreachedLabels G C q) (a : Nat) (ha : a < 8) :
    Core.aToQ (coreBits R L) a = decide (a ≠ 0 ∧ R (L.a ⟨a, ha⟩).1 q) := by
  by_cases ha0 : a = 0
  · subst a; simp [Core.aToQ]
  · by_cases ha6 : a < 6
    · rw [Core.aToQ, if_neg ha0, if_pos ha6, Core.pToH,
        RSeven.XThreeNoRoot.Core.pToH,
        getLsbD_coreBits R L _ (by omega)]
      have hd : (5 * 6 + (a - 1)) / 5 = 6 := by omega
      have hm : (5 * 6 + (a - 1)) % 5 = a - 1 := by omega
      have hidx : (⟨a - 1 + 1, by omega⟩ : Fin 8) = ⟨a, ha⟩ := by
        apply Fin.ext
        simp
        omega
      simp [coreBitAt, show ¬136 + (a - 1) < 64 by omega,
        show ¬136 + (a - 1) < 106 by omega,
        show 136 + (a - 1) < 141 by omega,
        show 136 + (a - 1) - 106 = 30 + (a - 1) by omega,
        hd, hm, ha0, hidx]
    · rw [Core.aToQ, if_neg ha0, if_neg ha6, Core.pToE,
        RSeven.XThreeNoRoot.Core.pToZ,
        getLsbD_coreBits R L _ (by omega)]
      have hd : (5 * 6 + (a - 6)) / 5 = 6 := by omega
      have hm : (5 * 6 + (a - 6)) % 5 = a - 6 := by omega
      have hz : a - 6 < 2 := by omega
      have hidx : (⟨a - 6 + 6, by omega⟩ : Fin 8) = ⟨a, ha⟩ := by
        apply Fin.ext
        simp
        omega
      simp [coreBitAt, show ¬206 + (a - 6) < 64 by omega,
        show ¬206 + (a - 6) < 106 by omega,
        show ¬206 + (a - 6) < 141 by omega,
        show ¬206 + (a - 6) < 176 by omega,
        show 206 + (a - 6) < 211 by omega,
        show 206 + (a - 6) - 176 = 30 + (a - 6) by omega,
        hd, hm, ha0, hz, hidx]

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedEncoding
