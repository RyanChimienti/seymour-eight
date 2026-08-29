import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.HighDefect.Dispatch
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Incidence decoder for the high-defect core

Packs labelled copies of `P`, `H = A₁ ∪ X`, `R`, `Z`, and `A` into the
218-bit layout consumed by `FourZHighDefect.highDefectCore`.
-/

namespace SeymourEight.FourZHighDefectBridge

open FourZHighDefect

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (R (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 77 then
    let q := n - 49
    decide (R (p ⟨q / 4, by omega⟩) (h ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 105 then
    let q := n - 77
    decide (R (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPZ : n < 133 then
    let q := n - 105
    decide (R (p ⟨q / 4, by omega⟩) (z ⟨q % 4, Nat.mod_lt _ (by omega)⟩))
  else if hnRP : n < 154 then
    let q := n - 133
    decide (R (r ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnA : n < 218 then
    let q := n - 154
    decide (R (a ⟨q / 8, by omega⟩) (a ⟨q % 8, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V) : BitVec 218 :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE
      (List.ofFn fun n : Fin 218 ↦ coreBitAt R p h r z a n))

@[simp]
theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V) (n : Nat) (hn : n < 218) :
    (coreBits R p h r z a).getLsbD n = coreBitAt R p h r z a n := by
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
theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p h r z a) i j =
      decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [pArc, getLsbD_coreBits R p h r z a (i * 7 + j) (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 4) :
    pToH (coreBits R p h r z a) i j =
      decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  rw [pToH, getLsbD_coreBits R p h r z a (49 + i * 4 + j) (by omega)]
  simp [coreBitAt, show ¬49 + i * 4 + j < 49 by omega,
    show 49 + i * 4 + j < 77 by omega,
    show 49 + i * 4 + j - 49 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp]
theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 4) (hj : j < 7) :
    hToP (coreBits R p h r z a) i j =
      decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [hToP, getLsbD_coreBits R p h r z a (77 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬77 + i * 7 + j < 49 by omega,
    show ¬77 + i * 7 + j < 77 by omega,
    show 77 + i * 7 + j < 105 by omega,
    show 77 + i * 7 + j - 77 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem pToZ_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 4) :
    pToZ (coreBits R p h r z a) i j =
      decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [pToZ, getLsbD_coreBits R p h r z a (105 + i * 4 + j) (by omega)]
  simp [coreBitAt, show ¬105 + i * 4 + j < 49 by omega,
    show ¬105 + i * 4 + j < 77 by omega,
    show ¬105 + i * 4 + j < 105 by omega,
    show 105 + i * 4 + j < 133 by omega,
    show 105 + i * 4 + j - 105 = i * 4 + j by omega,
    div_index i j 4 hj, mod_index i j 4 hj]

@[simp]
theorem rToP_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 3) (hj : j < 7) :
    rToP (coreBits R p h r z a) i j =
      decide (R (r ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [rToP, getLsbD_coreBits R p h r z a (133 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬133 + i * 7 + j < 49 by omega,
    show ¬133 + i * 7 + j < 77 by omega,
    show ¬133 + i * 7 + j < 105 by omega,
    show ¬133 + i * 7 + j < 133 by omega,
    show 133 + i * 7 + j < 154 by omega,
    show 133 + i * 7 + j - 133 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem aArc_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (coreBits R p h r z a) i j =
      decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [aArc, getLsbD_coreBits R p h r z a (154 + i * 8 + j) (by omega)]
  simp [coreBitAt, show ¬154 + i * 8 + j < 49 by omega,
    show ¬154 + i * 8 + j < 77 by omega,
    show ¬154 + i * 8 + j < 105 by omega,
    show ¬154 + i * 8 + j < 133 by omega,
    show ¬154 + i * 8 + j < 154 by omega,
    show 154 + i * 8 + j < 218 by omega,
    show 154 + i * 8 + j - 154 = i * 8 + j by omega,
    div_index i j 8 hj, mod_index i j 8 hj]

theorem impossible_of_encodedCore (p : Fin 7 → V) (h : Fin 4 → V)
    (r : Fin 3 → V) (z : Fin 4 → V) (a : Fin 8 → V)
    (missing degreeSum : Nat)
    (hMissingLower : 2 ≤ missing) (hMissingUpper : missing ≤ 7)
    (hDegreeLower : 56 ≤ degreeSum)
    (hDegreeUpper : degreeSum ≤ 63 - missing)
    (hCore : highDefectCoreAtMissingDegree missing degreeSum
      (coreBits R p h r z a) = true) : False := by
  rw [highDefectCoreAtMissingDegree_unsat missing degreeSum hMissingLower
    hMissingUpper hDegreeLower hDegreeUpper] at hCore
  contradiction

end SeymourEight.FourZHighDefectBridge
