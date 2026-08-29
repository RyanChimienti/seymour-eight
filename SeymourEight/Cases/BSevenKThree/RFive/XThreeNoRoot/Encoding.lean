import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.Labels
import SeymourEight.Certificates.BSevenKThree.RFive.XThree.CoreDefs
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Encoding

open Labels Core

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def coreBitAt {zCount : Nat} (p : Fin 5 → V) (a : Fin 8 → V)
    (q : Fin 2 → V) (z : Fin zCount → V) (n : Nat) : Bool :=
  if hnA0 : n < 4 then
    decide (R (a ⟨n + 4, by omega⟩) (a 0))
  else if hnAA : n < 46 then
    let d := n - 4
    let i := d / 6
    let j0 := d % 6
    let j := if j0 < i then j0 else j0 + 1
    decide (R (a ⟨i + 1, by omega⟩) (a ⟨j + 1, by
      have hj0 : j0 < 6 := Nat.mod_lt _ (by omega)
      dsimp [j]
      split <;> omega⟩))
  else if hnPP : n < 66 then
    let d := n - 46
    let i := d / 4
    let j0 := d % 4
    let j := if j0 < i then j0 else j0 + 1
    decide (R (p ⟨i, by omega⟩) (p ⟨j, by
      have hj0 : j0 < 4 := Nat.mod_lt _ (by omega)
      dsimp [j]
      split <;> omega⟩))
  else if hnAP : n < 101 then
    let d := n - 66
    decide (R (a ⟨d / 5 + 1, by omega⟩)
      (p ⟨d % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 131 then
    let d := n - 101
    decide (R (p ⟨d / 6, by omega⟩)
      (a ⟨d % 6 + 1, by have := Nat.mod_lt d (by omega : 0 < 6); omega⟩))
  else if hnAQ : n < 145 then
    let d := n - 131
    decide (R (a ⟨d / 2 + 1, by omega⟩)
      (q ⟨d % 2, Nat.mod_lt _ (by omega)⟩))
  else if hnPAux : n < 170 then
    let d := n - 145
    let e := d % 5
    if heQ : e < 2 then decide (R (p ⟨d / 5, by omega⟩) (q ⟨e, heQ⟩))
    else if hz : e - 2 < zCount then
      decide (R (p ⟨d / 5, by omega⟩) (z ⟨e - 2, hz⟩))
    else false
  else false

def graphBits {zCount : Nat} (p : Fin 5 → V) (a : Fin 8 → V)
    (q : Fin 2 → V) (z : Fin zCount → V) : Core.Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE
      (List.ofFn fun n : Fin 170 => coreBitAt R p a q z n))

@[simp] theorem getLsbD_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (n : Nat)
    (hn : n < 170) :
    (graphBits R p a q z).getLsbD n = coreBitAt R p a q z n := by
  rw [graphBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn) false,
    List.getElem_ofFn]

@[simp] theorem aToZero_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i : Nat)
    (hi : i < 4) :
    Core.encodedArc (graphBits R p a q z) (4 + i) 0 =
      decide (R (a ⟨4 + i, by omega⟩) (a 0)) := by
  interval_cases i <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt]

@[simp] theorem hArc_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i j : Nat)
    (hi : i < 7) (hj : j < 7) :
    Core.encodedArc (graphBits R p a q z) (i + 1) (j + 1) =
      decide (i ≠ j ∧ R (a ⟨i + 1, by omega⟩) (a ⟨j + 1, by omega⟩)) := by
  interval_cases i <;> interval_cases j <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    try rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt, Core.directedIndex]

@[simp] theorem pArc_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i j : Nat)
    (hi : i < 5) (hj : j < 5) :
    Core.encodedArc (graphBits R p a q z) (8 + i) (8 + j) =
      decide (i ≠ j ∧ R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  interval_cases i <;> interval_cases j <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    try rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt, Core.directedIndex]

@[simp] theorem hToP_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (h i : Nat)
    (hh : h < 7) (hi : i < 5) :
    Core.encodedArc (graphBits R p a q z) (h + 1) (8 + i) =
      decide (R (a ⟨h + 1, by omega⟩) (p ⟨i, hi⟩)) := by
  interval_cases h <;> interval_cases i <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt]

@[simp] theorem pToH_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i h : Nat)
    (hi : i < 5) (hh : h < 6) :
    Core.encodedArc (graphBits R p a q z) (8 + i) (h + 1) =
      decide (R (p ⟨i, hi⟩) (a ⟨h + 1, by omega⟩)) := by
  interval_cases i <;> interval_cases h <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt]

@[simp] theorem aToQ_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i j : Nat)
    (hi : i < 7) (hj : j < 2) :
    Core.encodedArc (graphBits R p a q z) (i + 1) (13 + j) =
      decide (R (a ⟨i + 1, by omega⟩) (q ⟨j, hj⟩)) := by
  interval_cases i <;> interval_cases j <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt]

@[simp] theorem pToQ_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i j : Nat)
    (hi : i < 5) (hj : j < 2) :
    Core.encodedArc (graphBits R p a q z) (8 + i) (13 + j) =
      decide (R (p ⟨i, hi⟩) (q ⟨j, hj⟩)) := by
  interval_cases i <;> interval_cases j <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt]

@[simp] theorem pToZ_graphBits {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i j : Nat)
    (hi : i < 5) (hj3 : j < 3) (hj : j < zCount) :
    Core.encodedArc (graphBits R p a q z) (8 + i) (15 + j) =
      decide (R (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  interval_cases i <;> interval_cases j <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt, hj]

@[simp] theorem pToZ_graphBits_inactive {zCount : Nat} (p : Fin 5 → V)
    (a : Fin 8 → V) (q : Fin 2 → V) (z : Fin zCount → V) (i j : Nat)
    (hi : i < 5) (hj3 : j < 3) (hj : zCount ≤ j) :
    Core.encodedArc (graphBits R p a q z) (8 + i) (15 + j) = false := by
  have hjNot : ¬j < zCount := by omega
  interval_cases i <;> interval_cases j <;>
    rw [Core.encodedArc] <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT,
      Nat.reduceEqDiff, if_true, if_false] <;>
    rw [getLsbD_graphBits R p a q z] <;>
    simp [coreBitAt, hjNot]

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Encoding
