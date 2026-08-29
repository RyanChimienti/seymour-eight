import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Encoding graph incidences for the terminal certificate

This file begins the soundness bridge for `TerminalCore`.  It records the
three incidence matrices in exactly the 119-bit layout consumed by the
certificate and proves the corresponding decoder equations.
-/

namespace SeymourEight.TerminalCoreBridge

open TerminalCore

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

/-- The Boolean stored at position `n` in the terminal-core encoding. -/
def coreBitAt (p : Fin 7 → V) (h : Fin 5 → V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (R (p ⟨n / 7, by omega⟩) (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 84 then
    let q := n - 49
    decide (R (p ⟨q / 5, by omega⟩) (h ⟨q % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 119 then
    let q := n - 84
    decide (R (h ⟨q / 7, by omega⟩) (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else
    false

/-- Encode the `P→P`, `P→H`, and `H→P` matrices as one 119-bit word. -/
def coreBits (p : Fin 7 → V) (h : Fin 5 → V) : BitVec 119 :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 119 ↦ coreBitAt R p h n))

@[simp]
theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (n : Nat) (hn : n < 119) :
    (coreBits R p h).getLsbD n = coreBitAt R p h n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa using hn) false,
    List.getElem_ofFn]

@[simp]
theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (coreBits R p h) i j = decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  have hDiv : (i * 7 + j) / 7 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * 7 + j) % 7 = j := Nat.mul_add_mod_of_lt hj
  have hIndex : i * 7 + j < 49 := by omega
  rw [pArc, getLsbD_coreBits R p h (i * 7 + j) (by omega)]
  simp [coreBitAt, hIndex, hDiv, hMod]

@[simp]
theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 5) :
    pToH (coreBits R p h) i j = decide (R (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  have hDiv : (i * 5 + j) / 5 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * 5 + j) % 5 = j := Nat.mul_add_mod_of_lt hj
  have hNotP : ¬49 + i * 5 + j < 49 := by omega
  have hIndex : 49 + i * 5 + j < 84 := by omega
  have hSub : 49 + i * 5 + j - 49 = i * 5 + j := by omega
  rw [pToH, getLsbD_coreBits R p h (49 + i * 5 + j) (by omega)]
  simp [coreBitAt, hNotP, hIndex, hSub, hDiv, hMod]

@[simp]
theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i j : Nat) (hi : i < 5) (hj : j < 7) :
    hToP (coreBits R p h) i j = decide (R (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  have hDiv : (i * 7 + j) / 7 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * 7 + j) % 7 = j := Nat.mul_add_mod_of_lt hj
  have hNotP : ¬84 + i * 7 + j < 49 := by omega
  have hNotPH : ¬84 + i * 7 + j < 84 := by omega
  have hIndex : 84 + i * 7 + j < 119 := by omega
  have hSub : 84 + i * 7 + j - 84 = i * 7 + j := by omega
  rw [hToP, getLsbD_coreBits R p h (84 + i * 7 + j) (by omega)]
  simp [coreBitAt, hNotP, hNotPH, hIndex, hSub, hDiv, hMod]

/-- Oriented incidences between labelled `P` and `H` vertices remain oriented. -/
theorem orientedBetweenPAndH_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (hAnti : ∀ u v, R u v → ¬R v u) :
    orientedBetweenPAndH (coreBits R p h) = true := by
  have hNoBoth : ∀ u v, ¬(R u v ∧ R v u) := by
    intro u v huv
    exact hAnti u v huv.1 huv.2
  have hOneMissing : ∀ u v, ¬R u v ∨ ¬R v u := by
    intro u v
    exact not_and_or.mp (hNoBoth u v)
  simp [orientedBetweenPAndH, allSeven, allFive, pToH_coreBits,
    hToP_coreBits, hOneMissing]

/--
On a labelled tournament, the certificate's upper-triangular convention
recovers the original arc relation in either index order.
-/
theorem tournamentArc_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    tournamentArc (coreBits R p h) i j =
      decide (R (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  by_cases hij : i = j
  · subst j
    rw [tournamentArc, if_pos rfl]
    simp [hLoopless]
  by_cases hlt : i < j
  · rw [tournamentArc, if_neg hij, if_pos hlt,
      pArc_coreBits R p h i j hi hj]
  · have hji : j < i := by omega
    have hFinNe : (⟨i, hi⟩ : Fin 7) ≠ ⟨j, hj⟩ := by
      intro hEq
      exact hij (Fin.ext_iff.mp hEq)
    rcases hComplete ⟨i, hi⟩ ⟨j, hj⟩ hFinNe with hForward | hReverse
    · have hNotReverse := hAnti _ _ hForward
      rw [tournamentArc, if_neg hij, if_neg hlt,
        pArc_coreBits R p h j i hj hi]
      simp [hForward, hNotReverse]
    · have hNotForward := hAnti _ _ hReverse
      rw [tournamentArc, if_neg hij, if_neg hlt,
        pArc_coreBits R p h j i hj hi]
      simp [hReverse, hNotForward]

/-! ## Labelled graph-side counts -/

/-- Read a labelled `P` vertex using a natural-number index modulo seven. -/
def pAt (p : Fin 7 → V) (i : Nat) : V :=
  p ⟨i % 7, Nat.mod_lt _ (by omega)⟩

/-- Read a labelled `H` vertex using a natural-number index modulo five. -/
def hAt (h : Fin 5 → V) (i : Nat) : V :=
  h ⟨i % 5, Nat.mod_lt _ (by omega)⟩

@[simp]
theorem pAt_of_lt (p : Fin 7 → V) (i : Nat) (hi : i < 7) :
    pAt p i = p ⟨i, hi⟩ := by
  simp [pAt, Nat.mod_eq_of_lt hi]

@[simp]
theorem hAt_of_lt (h : Fin 5 → V) (i : Nat) (hi : i < 5) :
    hAt h i = h ⟨i, hi⟩ := by
  simp [hAt, Nat.mod_eq_of_lt hi]

def labelledPArc (p : Fin 7 → V) (i j : Nat) : Bool :=
  decide (R (pAt p i) (pAt p j))

def labelledPToH (p : Fin 7 → V) (h : Fin 5 → V) (i j : Nat) : Bool :=
  decide (R (pAt p i) (hAt h j))

def labelledHToP (p : Fin 7 → V) (h : Fin 5 → V) (i j : Nat) : Bool :=
  decide (R (hAt h i) (pAt p j))

def labelledPOutCount (p : Fin 7 → V) (i : Nat) : BitVec 8 :=
  sumSeven (labelledPArc R p i)

def labelledPToHCount (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) : BitVec 8 :=
  sumFive (labelledPToH R p h i)

def labelledHToPCount (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) : BitVec 8 :=
  sumSeven (labelledHToP R p h i)

def labelledTotalPToH (p : Fin 7 → V) (h : Fin 5 → V) : BitVec 8 :=
  sumCountSeven (labelledPToHCount R p h)

def labelledTotalHToP (p : Fin 7 → V) (h : Fin 5 → V) : BitVec 8 :=
  sumCountFive (labelledHToPCount R p h)

theorem pToHCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) (hi : i < 7) :
    pToHCount (coreBits R p h) i = labelledPToHCount R p h i := by
  simp [pToHCount, labelledPToHCount, labelledPToH, sumFive,
    pToH_coreBits, pAt_of_lt, hAt_of_lt, hi]

theorem hToPCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) (hi : i < 5) :
    sumSeven (hToP (coreBits R p h) i) = labelledHToPCount R p h i := by
  simp [labelledHToPCount, labelledHToP, sumSeven, hToP_coreBits,
    pAt_of_lt, hAt_of_lt, hi]

theorem totalPToH_coreBits (p : Fin 7 → V) (h : Fin 5 → V) :
    totalPToH (coreBits R p h) = labelledTotalPToH R p h := by
  simp [totalPToH, labelledTotalPToH, sumCountSeven,
    pToHCount_coreBits]

theorem totalHToP_coreBits (p : Fin 7 → V) (h : Fin 5 → V) :
    totalHToP (coreBits R p h) = labelledTotalHToP R p h := by
  simp [totalHToP, labelledTotalHToP, sumCountFive,
    hToPCount_coreBits]

theorem tournamentPOutCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (i : Nat) (hi : i < 7) :
    tournamentPOutCount (coreBits R p h) i = labelledPOutCount R p i := by
  simp [tournamentPOutCount, labelledPOutCount, labelledPArc, sumSeven,
    tournamentArc_coreBits R p h hLoopless hAnti hComplete,
    pAt_of_lt, hi]

/-- Two-step reachability inside the labelled `P ∪ H` core. -/
def labelledReachedViaPOrH (p : Fin 7 → V) (h : Fin 5 → V)
    (i j : Nat) : Bool :=
  anySeven (fun middle ↦
    decide (middle ≠ i) && decide (middle ≠ j) &&
      labelledPArc R p i middle && labelledPArc R p middle j) ||
  anyFive (fun middle ↦
    labelledPToH R p h i middle && labelledHToP R p h middle j)

/-- Strict second-neighbor count in labelled `P`, through labelled `P ∪ H`. -/
def labelledSecondPCount (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) : BitVec 8 :=
  sumSeven (fun j ↦
    decide (j ≠ i) && !labelledPArc R p i j &&
      labelledReachedViaPOrH R p h i j)

/-- The degree retained by the terminal core after its common-`Z` reduction. -/
def labelledRetainedDegree (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) : BitVec 8 :=
  (if i = 0 then 2 else 3) + labelledPToHCount R p h i +
    labelledPOutCount R p i

/-- Graph-side form of the Boolean local counting test. -/
def labelledEquation18At (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) : Bool :=
  (labelledSecondPCount R p h i + 7).ule
    (labelledPOutCount R p i + 2 * labelledPToHCount R p h i +
      (if i = 0 then 0 else 2))

/-- Graph-side version of the certificate's lexicographic tail ordering. -/
def labelledInterchangeableOrdered (p : Fin 7 → V) (h : Fin 5 → V) : Bool :=
  let orderedPair := fun i j ↦
    (labelledRetainedDegree R p h j).ule
        (labelledRetainedDegree R p h i) &&
      (!(labelledRetainedDegree R p h i == labelledRetainedDegree R p h j) ||
        (labelledPToHCount R p h j).ule (labelledPToHCount R p h i))
  orderedPair 1 2 && orderedPair 2 3 && orderedPair 3 4 &&
    orderedPair 4 5 && orderedPair 5 6

theorem tournamentReachedViaPOrH_coreBits
    (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    tournamentReachedViaPOrH (coreBits R p h) i j =
      labelledReachedViaPOrH R p h i j := by
  simp [tournamentReachedViaPOrH, labelledReachedViaPOrH, labelledPArc,
    labelledPToH, labelledHToP, anySeven, anyFive,
    tournamentArc_coreBits R p h hLoopless hAnti hComplete,
    pToH_coreBits, hToP_coreBits, pAt_of_lt, hAt_of_lt, hi, hj]

theorem tournamentSecondPCount_coreBits
    (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (i : Nat) (hi : i < 7) :
    tournamentSecondPCount (coreBits R p h) i =
      labelledSecondPCount R p h i := by
  simp [tournamentSecondPCount, labelledSecondPCount, labelledPArc, sumSeven,
    tournamentArc_coreBits R p h hLoopless hAnti hComplete,
    tournamentReachedViaPOrH_coreBits R p h hLoopless hAnti hComplete,
    pAt_of_lt, hi]

theorem tournamentRetainedDegree_coreBits
    (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (i : Nat) (hi : i < 7) :
    tournamentRetainedDegree (coreBits R p h) i =
      labelledRetainedDegree R p h i := by
  rw [tournamentRetainedDegree, labelledRetainedDegree,
    pToHCount_coreBits R p h i hi,
    tournamentPOutCount_coreBits R p h hLoopless hAnti hComplete i hi]

theorem tournamentEquation18At_coreBits
    (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i))
    (i : Nat) (hi : i < 7) :
    tournamentEquation18At (coreBits R p h) i =
      labelledEquation18At R p h i := by
  rw [tournamentEquation18At, labelledEquation18At,
    tournamentSecondPCount_coreBits R p h hLoopless hAnti hComplete i hi,
    tournamentPOutCount_coreBits R p h hLoopless hAnti hComplete i hi,
    pToHCount_coreBits R p h i hi]

theorem tournamentInterchangeableOrdered_coreBits
    (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i)) :
    tournamentInterchangeableOrdered (coreBits R p h) =
      labelledInterchangeableOrdered R p h := by
  simp [tournamentInterchangeableOrdered, labelledInterchangeableOrdered,
    tournamentRetainedDegree_coreBits R p h hLoopless hAnti hComplete,
    pToHCount_coreBits]

theorem orientedOnP_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u) :
    orientedOnP (coreBits R p h) = true := by
  have hNoBoth : ∀ u v, ¬(R u v ∧ R v u) := by
    intro u v huv
    exact hAnti u v huv.1 huv.2
  have hOneMissing : ∀ u v, ¬R u v ∨ ¬R v u := by
    intro u v
    exact not_and_or.mp (hNoBoth u v)
  simp [orientedOnP, allSeven, pArc_coreBits, hLoopless, hOneMissing]

theorem pOutCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) (hi : i < 7) :
    pOutCount (coreBits R p h) i = labelledPOutCount R p i := by
  simp [pOutCount, labelledPOutCount, labelledPArc, sumSeven,
    pArc_coreBits, pAt_of_lt, hi]

theorem totalPOut_coreBits (p : Fin 7 → V) (h : Fin 5 → V) :
    totalPOut (coreBits R p h) = sumCountSeven (labelledPOutCount R p) := by
  simp [totalPOut, sumCountSeven, pOutCount_coreBits]

theorem reachedViaPOrH_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    reachedViaPOrH (coreBits R p h) i j =
      labelledReachedViaPOrH R p h i j := by
  simp [reachedViaPOrH, labelledReachedViaPOrH, labelledPArc,
    labelledPToH, labelledHToP, anySeven, anyFive, pArc_coreBits,
    pToH_coreBits, hToP_coreBits, pAt_of_lt, hAt_of_lt, hi, hj]

theorem secondPCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) (hi : i < 7) :
    secondPCount (coreBits R p h) i = labelledSecondPCount R p h i := by
  simp [secondPCount, labelledSecondPCount, labelledPArc, sumSeven,
    pArc_coreBits, reachedViaPOrH_coreBits, pAt_of_lt, hi]

theorem retainedDegree_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) (hi : i < 7) :
    retainedDegree (coreBits R p h) i = labelledRetainedDegree R p h i := by
  rw [retainedDegree, labelledRetainedDegree,
    pToHCount_coreBits R p h i hi, pOutCount_coreBits R p h i hi]

theorem equation18At_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (i : Nat) (hi : i < 7) :
    equation18At (coreBits R p h) i = labelledEquation18At R p h i := by
  rw [equation18At, labelledEquation18At,
    secondPCount_coreBits R p h i hi,
    pOutCount_coreBits R p h i hi,
    pToHCount_coreBits R p h i hi]

theorem interchangeableOrdered_coreBits (p : Fin 7 → V) (h : Fin 5 → V) :
    interchangeableOrdered (coreBits R p h) =
      labelledInterchangeableOrdered R p h := by
  simp [interchangeableOrdered, labelledInterchangeableOrdered,
    retainedDegree_coreBits, pToHCount_coreBits]

/-! ## Canonical ordering of the six interchangeable labels -/

/-- Extend a permutation of indices `0,...,5` by fixing the new index zero. -/
def extendTailPerm (τ : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 7) where
  toFun := Fin.cases 0 (fun i ↦ Fin.succ (τ i))
  invFun := Fin.cases 0 (fun i ↦ Fin.succ (τ.symm i))
  left_inv i := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp

@[simp]
theorem extendTailPerm_zero (τ : Equiv.Perm (Fin 6)) :
    extendTailPerm τ 0 = 0 := rfl

@[simp]
theorem extendTailPerm_succ (τ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    extendTailPerm τ (Fin.succ i) = Fin.succ (τ i) := rfl

/-- A radix-256 key encoding descending lexicographic order by `(degree,H-count)`. -/
def descendingKey (degree hCount : V → Nat) (v : V) : OrderDual Nat :=
  OrderDual.toDual (256 * degree v + hCount v)

/-- Sort the six tail labels, leaving the exceptional label zero fixed. -/
def tailSortPermutation (degree hCount : V → Nat) (p : Fin 7 → V) :
    Equiv.Perm (Fin 6) :=
  Tuple.sort (fun i ↦ descendingKey degree hCount (p (Fin.succ i)))

/-- Relabel `P` by the descending lexicographic tail order. -/
def sortedP (degree hCount : V → Nat) (p : Fin 7 → V) : Fin 7 → V :=
  p ∘ extendTailPerm (tailSortPermutation degree hCount p)

@[simp]
theorem sortedP_zero (degree hCount : V → Nat) (p : Fin 7 → V) :
    sortedP degree hCount p 0 = p 0 := rfl

theorem sortedP_bijective (degree hCount : V → Nat) (p : Fin 7 → V)
    (hp : Function.Bijective p) :
    Function.Bijective (sortedP degree hCount p) :=
  hp.comp (extendTailPerm (tailSortPermutation degree hCount p)).bijective

/-- The radix keys of the sorted tail are nonincreasing. -/
theorem sortedP_key_anti (degree hCount : V → Nat) (p : Fin 7 → V)
    {i j : Fin 6} (hij : i ≤ j) :
    256 * degree (sortedP degree hCount p (Fin.succ i)) +
        hCount (sortedP degree hCount p (Fin.succ i)) ≥
      256 * degree (sortedP degree hCount p (Fin.succ j)) +
        hCount (sortedP degree hCount p (Fin.succ j)) := by
  have hSorted := Tuple.monotone_sort
    (fun k ↦ descendingKey degree hCount (p (Fin.succ k))) hij
  exact hSorted

/-- With a one-byte secondary key, sorted tail degrees are nonincreasing. -/
theorem sortedP_degree_anti (degree hCount : V → Nat) (p : Fin 7 → V)
    (hCountLt : ∀ v, hCount v < 256) {i j : Fin 6} (hij : i ≤ j) :
    degree (sortedP degree hCount p (Fin.succ j)) ≤
      degree (sortedP degree hCount p (Fin.succ i)) := by
  have hKey := sortedP_key_anti degree hCount p hij
  have hiBound := hCountLt (sortedP degree hCount p (Fin.succ i))
  have hjBound := hCountLt (sortedP degree hCount p (Fin.succ j))
  omega

/-- Within a tied-degree block, the sorted `H`-counts are nonincreasing. -/
theorem sortedP_hCount_anti_of_degree_eq
    (degree hCount : V → Nat) (p : Fin 7 → V)
    {i j : Fin 6} (hij : i ≤ j)
    (hDegree : degree (sortedP degree hCount p (Fin.succ i)) =
      degree (sortedP degree hCount p (Fin.succ j))) :
    hCount (sortedP degree hCount p (Fin.succ j)) ≤
      hCount (sortedP degree hCount p (Fin.succ i)) := by
  have hKey := sortedP_key_anti degree hCount p hij
  omega

/-- One ordered-pair clause of the certificate follows from the tail sort. -/
theorem labelledOrderedPair_sortedP
    (degree hCount : V → Nat) (p : Fin 7 → V) (h : Fin 5 → V)
    (hCountLt : ∀ v, hCount v < 256)
    (hDegree : ∀ i : Fin 7,
      (labelledRetainedDegree R (sortedP degree hCount p) h i).toNat =
        degree (sortedP degree hCount p i))
    (hHCount : ∀ i : Fin 7,
      (labelledPToHCount R (sortedP degree hCount p) h i).toNat =
        hCount (sortedP degree hCount p i))
    {i j : Fin 6} (hij : i ≤ j) :
    (labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ j)).ule
        (labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ i)) &&
      (!(labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ i) ==
          labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ j)) ||
        (labelledPToHCount R (sortedP degree hCount p) h (Fin.succ j)).ule
          (labelledPToHCount R (sortedP degree hCount p) h (Fin.succ i))) = true := by
  have hDegreeLe := sortedP_degree_anti degree hCount p hCountLt hij
  have hDegreeLe' :
      (labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ j)).toNat ≤
        (labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ i)).toNat := by
    simpa only [hDegree] using hDegreeLe
  have hFirst :
      (labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ j)).ule
        (labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ i)) = true := by
    simpa only [BitVec.ule_eq_decide, decide_eq_true_eq] using hDegreeLe'
  by_cases hEq :
      labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ i) =
        labelledRetainedDegree R (sortedP degree hCount p) h (Fin.succ j)
  · have hDegreeEq :
        degree (sortedP degree hCount p (Fin.succ i)) =
          degree (sortedP degree hCount p (Fin.succ j)) := by
      rw [← hDegree, ← hDegree, hEq]
    have hHLe := sortedP_hCount_anti_of_degree_eq
      degree hCount p hij hDegreeEq
    have hHLe' :
        (labelledPToHCount R (sortedP degree hCount p) h (Fin.succ j)).toNat ≤
          (labelledPToHCount R (sortedP degree hCount p) h (Fin.succ i)).toNat := by
      simpa only [hHCount] using hHLe
    rw [Bool.and_eq_true]
    constructor
    · simpa only [Fin.val_succ] using hFirst
    · simp only [decide_eq_true_eq, Bool.or_eq_true]
      right
      simpa only [BitVec.ule_eq_decide, decide_eq_true_eq, Fin.val_succ]
        using hHLe'
  · rw [Bool.and_eq_true]
    constructor
    · simpa only [Fin.val_succ] using hFirst
    · simp only [decide_eq_true_eq, Bool.or_eq_true]
      left
      have hEq' :
          ¬labelledRetainedDegree R (sortedP degree hCount p) h (i + 1) =
            labelledRetainedDegree R (sortedP degree hCount p) h (j + 1) := by
        simpa only [Fin.val_succ] using hEq
      simp [hEq']

/-- The sorted labels satisfy all five adjacent ordering clauses. -/
theorem labelledInterchangeableOrdered_sortedP
    (degree hCount : V → Nat) (p : Fin 7 → V) (h : Fin 5 → V)
    (hCountLt : ∀ v, hCount v < 256)
    (hDegree : ∀ i : Fin 7,
      (labelledRetainedDegree R (sortedP degree hCount p) h i).toNat =
        degree (sortedP degree hCount p i))
    (hHCount : ∀ i : Fin 7,
      (labelledPToHCount R (sortedP degree hCount p) h i).toNat =
        hCount (sortedP degree hCount p i)) :
    labelledInterchangeableOrdered R (sortedP degree hCount p) h = true := by
  have h01 := labelledOrderedPair_sortedP R degree hCount p h hCountLt
    hDegree hHCount (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by omega)
  have h12 := labelledOrderedPair_sortedP R degree hCount p h hCountLt
    hDegree hHCount (i := (1 : Fin 6)) (j := (2 : Fin 6)) (by omega)
  have h23 := labelledOrderedPair_sortedP R degree hCount p h hCountLt
    hDegree hHCount (i := (2 : Fin 6)) (j := (3 : Fin 6)) (by omega)
  have h34 := labelledOrderedPair_sortedP R degree hCount p h hCountLt
    hDegree hHCount (i := (3 : Fin 6)) (j := (4 : Fin 6)) (by omega)
  have h45 := labelledOrderedPair_sortedP R degree hCount p h hCountLt
    hDegree hHCount (i := (4 : Fin 6)) (j := (5 : Fin 6)) (by omega)
  simp only [labelledInterchangeableOrdered, Bool.and_eq_true]
  norm_num at h01 h12 h23 h34 h45 ⊢
  exact ⟨⟨⟨⟨h01, h12⟩, h23⟩, h34⟩, h45⟩

/-! ## Soundness composition with the finite certificate -/

/--
The labelled, graph-side hypotheses retained by the
`(alpha,beta,degreeSum)=(1,0,57)` finite core.
-/
structure LabelledAlphaOneCore (p : Fin 7 → V) (h : Fin 5 → V) : Prop where
  loopless : ∀ u, ¬R u u
  anti : ∀ u v, R u v → ¬R v u
  completeP : ∀ i j : Fin 7, i ≠ j → R (p i) (p j) ∨ R (p j) (p i)
  totalPToH : labelledTotalPToH R p h + 1 = 17
  totalHToP : (18 : BitVec 8).ule (labelledTotalHToP R p h) = true
  perVertex : ∀ i : Nat, i < 7 →
    ((8 : BitVec 8).ule (labelledRetainedDegree R p h i) &&
      (labelledRetainedDegree R p h i).ule 9 &&
      labelledEquation18At R p h i) = true
  ordered : labelledInterchangeableOrdered R p h = true
  degreeSum : sumCountSeven (labelledRetainedDegree R p h) = 57

namespace LabelledAlphaOneCore

variable {R} {p : Fin 7 → V} {h : Fin 5 → V}
    (D : LabelledAlphaOneCore R p h)

include D in
/-- The incidence encoding of labelled graph data satisfies the checked core. -/
theorem encodedCore_true :
    tournamentOneMissingRootCore (coreBits R p h) 1 57 = true := by
  have hOriented := orientedBetweenPAndH_coreBits R p h D.anti
  have hPToH : TerminalCore.totalPToH (coreBits R p h) + 1 = 17 := by
    rw [totalPToH_coreBits]
    exact D.totalPToH
  have hPToHBool :
      (TerminalCore.totalPToH (coreBits R p h) + 1 == 17) = true := by
    simpa using hPToH
  have hHToP : (18 : BitVec 8).ule
      (TerminalCore.totalHToP (coreBits R p h)) = true := by
    rw [totalHToP_coreBits]
    exact D.totalHToP
  have hAt : ∀ i : Nat, (hi : i < 7) →
      ((8 : BitVec 8).ule
          (tournamentRetainedDegree (coreBits R p h) i) &&
        (tournamentRetainedDegree (coreBits R p h) i).ule 9 &&
        tournamentEquation18At (coreBits R p h) i) = true := by
    intro i hi
    rw [tournamentRetainedDegree_coreBits R p h D.loopless D.anti
      D.completeP i hi,
      tournamentEquation18At_coreBits R p h D.loopless D.anti
        D.completeP i hi]
    exact D.perVertex i hi
  have hAll : allSeven (fun i ↦
      (8 : BitVec 8).ule (tournamentRetainedDegree (coreBits R p h) i) &&
      (tournamentRetainedDegree (coreBits R p h) i).ule 9 &&
      tournamentEquation18At (coreBits R p h) i) = true := by
    have h0 := hAt 0 (by omega)
    have h1 := hAt 1 (by omega)
    have h2 := hAt 2 (by omega)
    have h3 := hAt 3 (by omega)
    have h4 := hAt 4 (by omega)
    have h5 := hAt 5 (by omega)
    have h6 := hAt 6 (by omega)
    simp only [allSeven, Bool.and_eq_true] at h0 h1 h2 h3 h4 h5 h6 ⊢
    exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  have hOrdered :
      tournamentInterchangeableOrdered (coreBits R p h) = true := by
    rw [tournamentInterchangeableOrdered_coreBits R p h D.loopless D.anti
      D.completeP]
    exact D.ordered
  have hDegreeSum :
      sumCountSeven (tournamentRetainedDegree (coreBits R p h)) = 57 := by
    simp only [sumCountSeven]
    rw [tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 0
        (by omega),
      tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 1
        (by omega),
      tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 2
        (by omega),
      tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 3
        (by omega),
      tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 4
        (by omega),
      tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 5
        (by omega),
      tournamentRetainedDegree_coreBits R p h D.loopless D.anti D.completeP 6
        (by omega)]
    exact D.degreeSum
  have hDegreeSumBool :
      (sumCountSeven (tournamentRetainedDegree (coreBits R p h)) == 57) =
        true := by
    simpa using hDegreeSum
  simp only [tournamentOneMissingRootCore, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hOriented, hPToHBool⟩, hHToP⟩, hAll⟩, hOrdered⟩,
    hDegreeSumBool⟩

include D in
/-- No labelled graph relation can satisfy the certified terminal core. -/
theorem impossible : False := by
  have hTrue := encodedCore_true D
  have hFalse := alphaOneBetaZero_unsat (coreBits R p h)
  rw [hFalse] at hTrue
  contradiction

end LabelledAlphaOneCore

/-- Labelled graph-side hypotheses for the general ordered internal-edge core. -/
structure LabelledOrderedEdgeCore (p : Fin 7 → V) (h : Fin 5 → V)
    (alpha internalEdges degreeSum : BitVec 8) : Prop where
  loopless : ∀ u, ¬R u u
  anti : ∀ u v, R u v → ¬R v u
  internalTotal : sumCountSeven (labelledPOutCount R p) = internalEdges
  totalPToH : labelledTotalPToH R p h + alpha = 17
  totalHToP : (18 : BitVec 8).ule (labelledTotalHToP R p h) = true
  perVertex : ∀ i : Nat, i < 7 →
    ((8 : BitVec 8).ule (labelledRetainedDegree R p h i) &&
      (labelledRetainedDegree R p h i).ule 9 &&
      labelledEquation18At R p h i) = true
  ordered : labelledInterchangeableOrdered R p h = true
  degreeSumEq : sumCountSeven (labelledRetainedDegree R p h) = degreeSum

namespace LabelledOrderedEdgeCore

variable {R} {p : Fin 7 → V} {h : Fin 5 → V}
    {alpha internalEdges degreeSum : BitVec 8}
    (D : LabelledOrderedEdgeCore R p h alpha internalEdges degreeSum)

include D in
theorem encodedCore_true :
    orderedOneMissingRootEdgeCore (coreBits R p h)
      alpha internalEdges degreeSum = true := by
  have hOrientedP := orientedOnP_coreBits R p h D.loopless D.anti
  have hOrientedPH := orientedBetweenPAndH_coreBits R p h D.anti
  have hInternal : TerminalCore.totalPOut (coreBits R p h) = internalEdges := by
    rw [totalPOut_coreBits]
    exact D.internalTotal
  have hInternalBool :
      (TerminalCore.totalPOut (coreBits R p h) == internalEdges) = true := by
    simpa using hInternal
  have hPToH : TerminalCore.totalPToH (coreBits R p h) + alpha = 17 := by
    rw [totalPToH_coreBits]
    exact D.totalPToH
  have hPToHBool :
      (TerminalCore.totalPToH (coreBits R p h) + alpha == 17) = true := by
    simpa using hPToH
  have hHToP :
      (18 : BitVec 8).ule (TerminalCore.totalHToP (coreBits R p h)) = true := by
    rw [totalHToP_coreBits]
    exact D.totalHToP
  have hAt : ∀ i : Nat, (hi : i < 7) →
      ((8 : BitVec 8).ule (retainedDegree (coreBits R p h) i) &&
        (retainedDegree (coreBits R p h) i).ule 9 &&
        equation18At (coreBits R p h) i) = true := by
    intro i hi
    rw [retainedDegree_coreBits R p h i hi,
      equation18At_coreBits R p h i hi]
    exact D.perVertex i hi
  have hAll : allSeven (fun i ↦
      (8 : BitVec 8).ule (retainedDegree (coreBits R p h) i) &&
      (retainedDegree (coreBits R p h) i).ule 9 &&
      equation18At (coreBits R p h) i) = true := by
    have h0 := hAt 0 (by omega)
    have h1 := hAt 1 (by omega)
    have h2 := hAt 2 (by omega)
    have h3 := hAt 3 (by omega)
    have h4 := hAt 4 (by omega)
    have h5 := hAt 5 (by omega)
    have h6 := hAt 6 (by omega)
    simp only [allSeven, Bool.and_eq_true] at h0 h1 h2 h3 h4 h5 h6 ⊢
    exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  have hOrdered : interchangeableOrdered (coreBits R p h) = true := by
    rw [interchangeableOrdered_coreBits]
    exact D.ordered
  have hDegreeSum :
      sumCountSeven (retainedDegree (coreBits R p h)) = degreeSum := by
    simp only [sumCountSeven]
    rw [retainedDegree_coreBits R p h 0 (by omega),
      retainedDegree_coreBits R p h 1 (by omega),
      retainedDegree_coreBits R p h 2 (by omega),
      retainedDegree_coreBits R p h 3 (by omega),
      retainedDegree_coreBits R p h 4 (by omega),
      retainedDegree_coreBits R p h 5 (by omega),
      retainedDegree_coreBits R p h 6 (by omega)]
    exact D.degreeSumEq
  have hDegreeSumBool :
      (sumCountSeven (retainedDegree (coreBits R p h)) == degreeSum) = true := by
    simpa using hDegreeSum
  simp only [orderedOneMissingRootEdgeCore, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨hOrientedP, hOrientedPH⟩, hInternalBool⟩,
    hPToHBool⟩, hHToP⟩, hAll⟩, hOrdered⟩, hDegreeSumBool⟩

include D in
theorem impossible
    (hUnsat : ∀ bits : BitVec 119,
      orderedOneMissingRootEdgeCore bits alpha internalEdges degreeSum = false) : False := by
  have hTrue := encodedCore_true D
  have hFalse := hUnsat (coreBits R p h)
  rw [hFalse] at hTrue
  contradiction

end LabelledOrderedEdgeCore

/-- Labelled graph-side hypotheses for the complete degree-sum-58 core. -/
structure LabelledDegreeTenCore (p : Fin 7 → V) (h : Fin 5 → V) : Prop where
  loopless : ∀ u, ¬R u u
  anti : ∀ u v, R u v → ¬R v u
  internalTotal : sumCountSeven (labelledPOutCount R p) = 21
  totalPToH : labelledTotalPToH R p h = 17
  totalHToP : (18 : BitVec 8).ule (labelledTotalHToP R p h) = true
  perVertex : ∀ i : Nat, i < 7 →
    ((8 : BitVec 8).ule (labelledRetainedDegree R p h i) &&
      (labelledRetainedDegree R p h i).ule 10 &&
      labelledEquation18At R p h i) = true
  ordered : labelledInterchangeableOrdered R p h = true
  degreeSumEq : sumCountSeven (labelledRetainedDegree R p h) = 58

namespace LabelledDegreeTenCore

variable {R} {p : Fin 7 → V} {h : Fin 5 → V}
    (D : LabelledDegreeTenCore R p h)

include D in
theorem encodedCore_true : degreeTenCore (coreBits R p h) = true := by
  have hOrientedP := orientedOnP_coreBits R p h D.loopless D.anti
  have hOrientedPH := orientedBetweenPAndH_coreBits R p h D.anti
  have hInternal : TerminalCore.totalPOut (coreBits R p h) = 21 := by
    rw [totalPOut_coreBits]
    exact D.internalTotal
  have hInternalBool :
      (TerminalCore.totalPOut (coreBits R p h) == 21) = true := by
    simpa using hInternal
  have hPToH : TerminalCore.totalPToH (coreBits R p h) = 17 := by
    rw [totalPToH_coreBits]
    exact D.totalPToH
  have hPToHBool : (TerminalCore.totalPToH (coreBits R p h) == 17) = true := by
    simpa using hPToH
  have hHToP :
      (18 : BitVec 8).ule (TerminalCore.totalHToP (coreBits R p h)) = true := by
    rw [totalHToP_coreBits]
    exact D.totalHToP
  have hAt : ∀ i : Nat, (hi : i < 7) →
      ((8 : BitVec 8).ule (retainedDegree (coreBits R p h) i) &&
        (retainedDegree (coreBits R p h) i).ule 10 &&
        equation18At (coreBits R p h) i) = true := by
    intro i hi
    rw [retainedDegree_coreBits R p h i hi,
      equation18At_coreBits R p h i hi]
    exact D.perVertex i hi
  have hAll : allSeven (fun i ↦
      (8 : BitVec 8).ule (retainedDegree (coreBits R p h) i) &&
      (retainedDegree (coreBits R p h) i).ule 10 &&
      equation18At (coreBits R p h) i) = true := by
    have h0 := hAt 0 (by omega)
    have h1 := hAt 1 (by omega)
    have h2 := hAt 2 (by omega)
    have h3 := hAt 3 (by omega)
    have h4 := hAt 4 (by omega)
    have h5 := hAt 5 (by omega)
    have h6 := hAt 6 (by omega)
    simp only [allSeven, Bool.and_eq_true] at h0 h1 h2 h3 h4 h5 h6 ⊢
    exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  have hOrdered : interchangeableOrdered (coreBits R p h) = true := by
    rw [interchangeableOrdered_coreBits]
    exact D.ordered
  have hDegreeSum :
      sumCountSeven (retainedDegree (coreBits R p h)) = 58 := by
    simp only [sumCountSeven]
    rw [retainedDegree_coreBits R p h 0 (by omega),
      retainedDegree_coreBits R p h 1 (by omega),
      retainedDegree_coreBits R p h 2 (by omega),
      retainedDegree_coreBits R p h 3 (by omega),
      retainedDegree_coreBits R p h 4 (by omega),
      retainedDegree_coreBits R p h 5 (by omega),
      retainedDegree_coreBits R p h 6 (by omega)]
    exact D.degreeSumEq
  have hDegreeSumBool :
      (sumCountSeven (retainedDegree (coreBits R p h)) == 58) = true := by
    simpa using hDegreeSum
  simp only [degreeTenCore, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨hOrientedP, hOrientedPH⟩, hInternalBool⟩,
    hPToHBool⟩, hHToP⟩, hAll⟩, hOrdered⟩, hDegreeSumBool⟩

include D in
theorem impossible : False := by
  have hTrue := encodedCore_true D
  have hFalse := degreeTen_unsat (coreBits R p h)
  rw [hFalse] at hTrue
  contradiction

end LabelledDegreeTenCore

end SeymourEight.TerminalCoreBridge
