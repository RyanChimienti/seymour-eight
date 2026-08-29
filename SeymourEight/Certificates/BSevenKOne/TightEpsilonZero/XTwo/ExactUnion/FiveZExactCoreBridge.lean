import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactFamilyUnordered
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactAllOverlaps
import Mathlib.Data.List.OfFn

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Incidence decoder for the exact five-`Z` core

This is the first half of the graph-to-certificate bridge.  It packs five
labelled finite vertex classes and the ambient arc relation into the exact
280-bit layout consumed by `FiveZExactRisk.familyCore`, then proves that each
of the eight incidence matrices decodes to the original relation.
-/

namespace SeymourEight.FiveZExactCoreBridge

open FiveZExactRisk

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (R (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 70 then
    let q := n - 49
    decide (R (p ⟨q / 3, by omega⟩) (h ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 91 then
    let q := n - 70
    decide (R (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPZ : n < 126 then
    let q := n - 91
    decide (R (p ⟨q / 5, by omega⟩) (z ⟨q % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnZP : n < 161 then
    let q := n - 126
    decide (R (z ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnA : n < 225 then
    let q := n - 161
    decide (R (a ⟨q / 8, by omega⟩) (a ⟨q % 8, Nat.mod_lt _ (by omega)⟩))
  else if hnZ : n < 250 then
    let q := n - 225
    decide (R (z ⟨q / 5, by omega⟩) (z ⟨q % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnZW : n < 280 then
    let q := n - 250
    decide (R (z ⟨q / 6, by omega⟩) (w ⟨q % 6, Nat.mod_lt _ (by omega)⟩))
  else false

def coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V) : BitVec 280 :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 280 ↦ coreBitAt R p h z w a n))

@[simp]
theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V) (n : Nat) (hn : n < 280) :
    (coreBits R p h z w a).getLsbD n = coreBitAt R p h z w a n := by
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
theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p h z w a) i j = decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [pArc, getLsbD_coreBits R p h z w a (i * 7 + j) (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 3) :
    pToH (coreBits R p h z w a) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  rw [pToH, getLsbD_coreBits R p h z w a (49 + i * 3 + j) (by omega)]
  simp [coreBitAt, show ¬49 + i * 3 + j < 49 by omega,
    show 49 + i * 3 + j < 70 by omega,
    show 49 + i * 3 + j - 49 = i * 3 + j by omega,
    div_index i j 3 hj, mod_index i j 3 hj]

@[simp]
theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 3) (hj : j < 7) :
    hToP (coreBits R p h z w a) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [hToP, getLsbD_coreBits R p h z w a (70 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬70 + i * 7 + j < 49 by omega,
    show ¬70 + i * 7 + j < 70 by omega,
    show 70 + i * 7 + j < 91 by omega,
    show 70 + i * 7 + j - 70 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem pToZ_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 5) :
    pToZ (coreBits R p h z w a) i j = decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [pToZ, getLsbD_coreBits R p h z w a (91 + i * 5 + j) (by omega)]
  simp [coreBitAt, show ¬91 + i * 5 + j < 49 by omega,
    show ¬91 + i * 5 + j < 70 by omega,
    show ¬91 + i * 5 + j < 91 by omega,
    show 91 + i * 5 + j < 126 by omega,
    show 91 + i * 5 + j - 91 = i * 5 + j by omega,
    div_index i j 5 hj, mod_index i j 5 hj]

@[simp]
theorem zToP_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 5) (hj : j < 7) :
    zToP (coreBits R p h z w a) i j = decide (R (z ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  rw [zToP, getLsbD_coreBits R p h z w a (126 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬126 + i * 7 + j < 49 by omega,
    show ¬126 + i * 7 + j < 70 by omega,
    show ¬126 + i * 7 + j < 91 by omega,
    show ¬126 + i * 7 + j < 126 by omega,
    show 126 + i * 7 + j < 161 by omega,
    show 126 + i * 7 + j - 126 = i * 7 + j by omega,
    div_index i j 7 hj, mod_index i j 7 hj]

@[simp]
theorem aArc_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (coreBits R p h z w a) i j = decide (R (a ⟨i, hi⟩) (a ⟨j, hj⟩)) := by
  rw [aArc, getLsbD_coreBits R p h z w a (161 + i * 8 + j) (by omega)]
  simp [coreBitAt, show ¬161 + i * 8 + j < 49 by omega,
    show ¬161 + i * 8 + j < 70 by omega,
    show ¬161 + i * 8 + j < 91 by omega,
    show ¬161 + i * 8 + j < 126 by omega,
    show ¬161 + i * 8 + j < 161 by omega,
    show 161 + i * 8 + j < 225 by omega,
    show 161 + i * 8 + j - 161 = i * 8 + j by omega,
    div_index i j 8 hj, mod_index i j 8 hj]

@[simp]
theorem zArc_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 5) (hj : j < 5) :
    zArc (coreBits R p h z w a) i j = decide (R (z ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  rw [zArc, getLsbD_coreBits R p h z w a (225 + i * 5 + j) (by omega)]
  simp [coreBitAt, show ¬225 + i * 5 + j < 49 by omega,
    show ¬225 + i * 5 + j < 70 by omega,
    show ¬225 + i * 5 + j < 91 by omega,
    show ¬225 + i * 5 + j < 126 by omega,
    show ¬225 + i * 5 + j < 161 by omega,
    show ¬225 + i * 5 + j < 225 by omega,
    show 225 + i * 5 + j < 250 by omega,
    show 225 + i * 5 + j - 225 = i * 5 + j by omega,
    div_index i j 5 hj, mod_index i j 5 hj]

@[simp]
theorem zToW_coreBits (p : Fin 7 → V) (h : Fin 3 → V) (z : Fin 5 → V)
    (w : Fin 6 → V) (a : Fin 8 → V)
    (i j : Nat) (hi : i < 5) (hj : j < 6) :
    zToW (coreBits R p h z w a) i j = decide (R (z ⟨i, hi⟩) (w ⟨j, hj⟩)) := by
  rw [zToW, getLsbD_coreBits R p h z w a (250 + i * 6 + j) (by omega)]
  simp [coreBitAt, show ¬250 + i * 6 + j < 49 by omega,
    show ¬250 + i * 6 + j < 70 by omega,
    show ¬250 + i * 6 + j < 91 by omega,
    show ¬250 + i * 6 + j < 126 by omega,
    show ¬250 + i * 6 + j < 161 by omega,
    show ¬250 + i * 6 + j < 225 by omega,
    show ¬250 + i * 6 + j < 250 by omega,
    show 250 + i * 6 + j < 280 by omega,
    show 250 + i * 6 + j - 250 = i * 6 + j by omega,
    div_index i j 6 hj, mod_index i j 6 hj]

/-- Any labelling satisfying the symmetry-free family core is contradictory. -/
theorem impossible_of_encodedCoreUnordered (p : Fin 7 → V) (h : Fin 3 → V)
    (z : Fin 5 → V) (w : Fin 6 → V) (a : Fin 8 → V)
    (hCore : familyCoreUnordered (coreBits R p h z w a) = true) : False := by
  rw [familyCoreUnordered_unsat] at hCore
  contradiction

/-- Any labelling satisfying the all-overlap union-six/seven core is
contradictory. -/
theorem impossible_of_encodedAllOverlaps (p : Fin 7 → V) (h : Fin 3 → V)
    (z : Fin 5 → V) (w : Fin 6 → V) (a : Fin 8 → V)
    (hCore : familyCoreAnyOverlap (coreBits R p h z w a) = true) : False := by
  rw [familyCoreAnyOverlap_unsat] at hCore
  contradiction

end SeymourEight.FiveZExactCoreBridge
