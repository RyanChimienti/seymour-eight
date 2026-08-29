import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.XThreeReducedCoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.EpsilonOneXThreeReducedGraphBridge

open EpsilonOneXThreeReducedCore

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (R (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 77 then
    let q := n - 49
    decide (R (p ⟨q / 4, by omega⟩) (h ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 105 then
    let q := n - 77
    decide (R (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPE : n < 133 then
    let q := n - 105
    decide (R (p ⟨q / 4, by omega⟩) (e ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnRP : n < 154 then
    let q := n - 133
    decide (R (r ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnAA : n < 218 then
    let q := n - 154
    decide (R (a ⟨q / 8, by omega⟩) (a ⟨q % 8, Nat.mod_lt _ (by omega)⟩))
  else if hnZP : n < 230 then
    let q := n - 218
    let target := if q % 4 = 0 then a 0 else a ⟨q % 4 + 4, by omega⟩
    decide (R (z ⟨q / 4, by omega⟩) target)
  else false

def coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 230 => coreBitAt R p h e r a z n))

@[simp] theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (e : Fin 4 → V) (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (n : Nat) (hn : n < 230) :
    (coreBits R p h e r a z).getLsbD n = coreBitAt R p h e r a z n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

private theorem div_index (i j w : Nat) (hj : j < w) : (i * w + j) / w = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j w : Nat) (hj : j < w) : (i * w + j) % w = j :=
  Nat.mul_add_mod_of_lt hj

@[simp] theorem pp_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pp (coreBits R p h e r a z) i j = decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [pp, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega, div_index i j 7 hj, mod_index i j 7 hj]

@[simp] theorem ph_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 4) :
    ph (coreBits R p h e r a z) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  rw [ph, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show ¬49 + i * 4 + j < 49 by omega,
    show 49 + i * 4 + j < 77 by omega, show 49 + i * 4 + j - 49 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp] theorem hp_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 4) (hj : j < 7) :
    hp (coreBits R p h e r a z) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [hp, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show ¬77 + i * 7 + j < 49 by omega,
    show ¬77 + i * 7 + j < 77 by omega, show 77 + i * 7 + j < 105 by omega,
    show 77 + i * 7 + j - 77 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp] theorem pe_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 4) :
    pe (coreBits R p h e r a z) i j = decide (R (p ⟨i, hi⟩) (e ⟨j, hj⟩)) := by
  rw [pe, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show ¬105 + i * 4 + j < 49 by omega,
    show ¬105 + i * 4 + j < 77 by omega, show ¬105 + i * 4 + j < 105 by omega,
    show 105 + i * 4 + j < 133 by omega,
    show 105 + i * 4 + j - 105 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp] theorem rp_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 3) (hj : j < 7) :
    rp (coreBits R p h e r a z) i j = decide (R (r ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [rp, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show ¬133 + i * 7 + j < 49 by omega,
    show ¬133 + i * 7 + j < 77 by omega, show ¬133 + i * 7 + j < 105 by omega,
    show ¬133 + i * 7 + j < 133 by omega, show 133 + i * 7 + j < 154 by omega,
    show 133 + i * 7 + j - 133 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp] theorem aa_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aa (coreBits R p h e r a z) i j = decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [aa, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show ¬154 + i * 8 + j < 49 by omega,
    show ¬154 + i * 8 + j < 77 by omega, show ¬154 + i * 8 + j < 105 by omega,
    show ¬154 + i * 8 + j < 133 by omega, show ¬154 + i * 8 + j < 154 by omega,
    show 154 + i * 8 + j < 218 by omega,
    show 154 + i * 8 + j - 154 = i * 8 + j by omega,
    div_index i j 8 hj, mod_index i j 8 hj]

@[simp] theorem zp_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 3) (hj : j < 4) :
    zp (coreBits R p h e r a z) i j =
      decide (R (z ⟨i, hi⟩) (if j = 0 then a 0 else a ⟨j + 4, by omega⟩)) := by
  rw [zp, getLsbD_coreBits R p h e r a z _ (by omega)]
  simp [coreBitAt, show ¬218 + i * 4 + j < 49 by omega,
    show ¬218 + i * 4 + j < 77 by omega, show ¬218 + i * 4 + j < 105 by omega,
    show ¬218 + i * 4 + j < 133 by omega, show ¬218 + i * 4 + j < 154 by omega,
    show ¬218 + i * 4 + j < 218 by omega, show 218 + i * 4 + j < 230 by omega,
    show 218 + i * 4 + j - 218 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

end SeymourEight.EpsilonOneXThreeReducedGraphBridge
