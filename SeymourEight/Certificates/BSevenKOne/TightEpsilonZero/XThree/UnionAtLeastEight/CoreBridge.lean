import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.CoreDefs
import Mathlib.Data.List.OfFn

set_option linter.style.header false

/-! Decoder for the 105 retained `P × P`, `P × H`, and `H × P` bits. -/

namespace SeymourEight.FourZUnionEightBridge

open FourZUnionEight

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (h : Fin 4 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (R (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 77 then
    let q := n - 49
    decide (R (p ⟨q / 4, by omega⟩) (h ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 105 then
    let q := n - 77
    decide (R (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 7 → V) (h : Fin 4 → V) : BitVec 105 :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE
      (List.ofFn fun n : Fin 105 ↦ coreBitAt R p h n))

@[simp]
theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (n : Nat) (hn : n < 105) :
    (coreBits R p h).getLsbD n = coreBitAt R p h n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

private theorem div_index (i j width : Nat) (hj : j < width) :
    (i * width + j) / width = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j width : Nat) (hj : j < width) :
    (i * width + j) % width = j := Nat.mul_add_mod_of_lt hj

@[simp]
theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p h) i j = decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [pArc, getLsbD_coreBits R p h (i * 7 + j) (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 4) :
    pToH (coreBits R p h) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  rw [pToH, getLsbD_coreBits R p h (49 + i * 4 + j) (by omega)]
  simp [coreBitAt, show ¬49 + i * 4 + j < 49 by omega,
    show 49 + i * 4 + j < 77 by omega,
    show 49 + i * 4 + j - 49 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp]
theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (i j : Nat) (hi : i < 4) (hj : j < 7) :
    hToP (coreBits R p h) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [hToP, getLsbD_coreBits R p h (77 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬77 + i * 7 + j < 49 by omega,
    show ¬77 + i * 7 + j < 77 by omega,
    show 77 + i * 7 + j < 105 by omega,
    show 77 + i * 7 + j - 77 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

end SeymourEight.FourZUnionEightBridge
