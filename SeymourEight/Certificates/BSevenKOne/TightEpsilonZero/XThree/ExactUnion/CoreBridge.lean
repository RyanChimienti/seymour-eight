import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.CoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

/-! Decoder for the 214 exact-seven retained incidences. -/

namespace SeymourEight.FourZExactSevenBridge

open FourZExactSeven

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (R (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 77 then
    let q := n - 49
    decide (R (p ⟨q / 4, by omega⟩) (h ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 105 then
    let q := n - 77
    decide (R (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnA : n < 169 then
    let q := n - 105
    decide (R (a ⟨q / 8, by omega⟩) (a ⟨q % 8, Nat.mod_lt _ (by omega)⟩))
  else if hnZ : n < 185 then
    let q := n - 169
    decide (R (z ⟨q / 4, by omega⟩) (z ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnZW : n < 213 then
    let q := n - 185
    decide (R (z ⟨q / 7, by omega⟩) (w ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if n = 213 then decide (R (z 0) (p 0))
  else false

def coreBits (p : Fin 7 → V) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) : BitVec 214 :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE
      (List.ofFn fun n : Fin 214 ↦ coreBitAt R p h a z w n))

@[simp] theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (n : Nat) (hn : n < 214) :
    (coreBits R p h a z w).getLsbD n = coreBitAt R p h a z w n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

private theorem div_index (i j width : Nat) (hj : j < width) :
    (i * width + j) / width = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j width : Nat) (hj : j < width) :
    (i * width + j) % width = j := Nat.mul_add_mod_of_lt hj

@[simp] theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p h a z w) i j = decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [pArc, getLsbD_coreBits R p h a z w (i * 7 + j) (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp] theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 4) :
    pToH (coreBits R p h a z w) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  rw [pToH, getLsbD_coreBits R p h a z w (49 + i * 4 + j) (by omega)]
  simp [coreBitAt, show ¬49 + i * 4 + j < 49 by omega,
    show 49 + i * 4 + j < 77 by omega,
    show 49 + i * 4 + j - 49 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp] theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i j : Nat) (hi : i < 4) (hj : j < 7) :
    hToP (coreBits R p h a z w) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [hToP, getLsbD_coreBits R p h a z w (77 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬77 + i * 7 + j < 49 by omega,
    show ¬77 + i * 7 + j < 77 by omega,
    show 77 + i * 7 + j < 105 by omega,
    show 77 + i * 7 + j - 77 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp] theorem aArc_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (coreBits R p h a z w) i j = decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [aArc, getLsbD_coreBits R p h a z w (105 + i * 8 + j) (by omega)]
  simp [coreBitAt, show ¬105 + i * 8 + j < 49 by omega,
    show ¬105 + i * 8 + j < 77 by omega,
    show ¬105 + i * 8 + j < 105 by omega,
    show 105 + i * 8 + j < 169 by omega,
    show 105 + i * 8 + j - 105 = i * 8 + j by omega,
    div_index i j 8 hj, mod_index i j 8 hj]

@[simp] theorem zArc_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i j : Nat) (hi : i < 4) (hj : j < 4) :
    zArc (coreBits R p h a z w) i j = decide (R (z ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [zArc, getLsbD_coreBits R p h a z w (169 + i * 4 + j) (by omega)]
  simp [coreBitAt, show ¬169 + i * 4 + j < 49 by omega,
    show ¬169 + i * 4 + j < 77 by omega,
    show ¬169 + i * 4 + j < 105 by omega,
    show ¬169 + i * 4 + j < 169 by omega,
    show 169 + i * 4 + j < 185 by omega,
    show 169 + i * 4 + j - 169 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp] theorem zToW_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i j : Nat) (hi : i < 4) (hj : j < 7) :
    zToW (coreBits R p h a z w) i j = decide (R (z ⟨i, hi⟩) (w ⟨j, hj⟩)) := by
  rw [zToW, getLsbD_coreBits R p h a z w (185 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬185 + i * 7 + j < 49 by omega,
    show ¬185 + i * 7 + j < 77 by omega,
    show ¬185 + i * 7 + j < 105 by omega,
    show ¬185 + i * 7 + j < 169 by omega,
    show ¬185 + i * 7 + j < 185 by omega,
    show 185 + i * 7 + j < 213 by omega,
    show 185 + i * 7 + j - 185 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp] theorem z0ToP0_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V) :
    z0ToP0 (coreBits R p h a z w) = decide (R (z 0) (p 0)) := by
  rw [z0ToP0, getLsbD_coreBits R p h a z w 213 (by omega)]
  simp [coreBitAt]

end SeymourEight.FourZExactSevenBridge
