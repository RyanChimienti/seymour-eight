import SeymourEight.Certificates.BSixKTwo
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.OfFn

/-!
# Incidence encoding for the `(6,2)` cores

This is the small trusted adapter between labelled graph vertices and the bit
layout checked by `bv_decide`.
-/

namespace SeymourEight.BSixKTwoCoreBridge

open BSixKTwoCore

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

def hAt {x : Nat} (h : Fin (hSize x) → V) (i : Nat) : V :=
  h ⟨i % hSize x, Nat.mod_lt _ (by simp [hSize])⟩

def pAt (p : Fin 6 → V) (i : Nat) : V :=
  p ⟨i % 6, Nat.mod_lt _ (by omega)⟩

def tAt {x : Nat} (hx : x ≤ 5) (t : Fin (tSize x) → V) (i : Nat) : V :=
  t ⟨i % tSize x, Nat.mod_lt _ (by simp [tSize]; omega)⟩

def wAt {x : Nat} (hx : x ≤ 5) (w : Fin (wSize x) → V) (i : Nat) : V :=
  w ⟨i % wSize x, Nat.mod_lt _ (by simp [wSize]; omega)⟩

def coreAt {x : Nat} (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (i : Nat) : V :=
  if i < hSize x then hAt h i else pAt p (i - hSize x)

def coreBitAt {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V) (n : Nat) : Bool :=
  if _hnCore : n < coreSize x * coreSize x then
    decide (R (coreAt h p (n / coreSize x))
      (coreAt h p (n % coreSize x)))
  else if _hnT : n < coreSize x * coreSize x + x * tSize x then
    let q := n - coreSize x * coreSize x
    decide (R (hAt h (2 + q / tSize x)) (tAt hx t (q % tSize x)))
  else if _hnW : n < coreWidth x then
    let q := n - (coreSize x * coreSize x + x * tSize x)
    decide (R (pAt p (q / wSize x)) (wAt hx w (q % wSize x)))
  else
    false

def coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V) :
    BitVec (coreWidth x) :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE
      (List.ofFn fun n : Fin (coreWidth x) ↦ coreBitAt R hx h p t w n))

@[simp]
theorem getLsbD_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (n : Nat) (hn : n < coreWidth x) :
    (coreBits R hx h p t w).getLsbD n = coreBitAt R hx h p t w n := by
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa using hn) false,
    List.getElem_ofFn]

@[simp]
theorem hAt_of_lt {x : Nat} (h : Fin (hSize x) → V)
    (i : Nat) (hi : i < hSize x) :
    hAt h i = h ⟨i, hi⟩ := by
  simp [hAt, Nat.mod_eq_of_lt hi]

@[simp]
theorem pAt_of_lt (p : Fin 6 → V) (i : Nat) (hi : i < 6) :
    pAt p i = p ⟨i, hi⟩ := by
  simp [pAt, Nat.mod_eq_of_lt hi]

@[simp]
theorem tAt_of_lt {x : Nat} (hx : x ≤ 5) (t : Fin (tSize x) → V)
    (i : Nat) (hi : i < tSize x) :
    tAt hx t i = t ⟨i, hi⟩ := by
  simp [tAt, Nat.mod_eq_of_lt hi]

@[simp]
theorem wAt_of_lt {x : Nat} (hx : x ≤ 5) (w : Fin (wSize x) → V)
    (i : Nat) (hi : i < wSize x) :
    wAt hx w i = w ⟨i, hi⟩ := by
  simp [wAt, Nat.mod_eq_of_lt hi]

@[simp]
theorem coreAt_h {x : Nat} (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (i : Nat) (hi : i < hSize x) :
    coreAt h p i = h ⟨i, hi⟩ := by
  simp [coreAt, hi, hAt_of_lt]

@[simp]
theorem coreAt_p {x : Nat} (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (i : Nat) (hi : i < 6) :
    coreAt h p (hSize x + i) = p ⟨i, hi⟩ := by
  simp [coreAt, hSize, pAt_of_lt, hi]

@[simp]
theorem arc_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (i j : Nat) (hi : i < coreSize x) (hj : j < coreSize x) :
    arc (coreBits R hx h p t w) i j =
      decide (R (coreAt h p i) (coreAt h p j)) := by
  have hDiv : (i * coreSize x + j) / coreSize x = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by simp [coreSize])]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * coreSize x + j) % coreSize x = j :=
    Nat.mul_add_mod_of_lt hj
  have hIndex : i * coreSize x + j < coreSize x * coreSize x := by
    calc
      i * coreSize x + j < i * coreSize x + coreSize x :=
        Nat.add_lt_add_left hj _
      _ = (i + 1) * coreSize x := by simp [Nat.add_mul]
      _ ≤ coreSize x * coreSize x :=
        Nat.mul_le_mul_right (coreSize x) (Nat.add_one_le_iff.mpr hi)
  rw [arc, getLsbD_coreBits R hx h p t w _ (by
    simp [coreWidth]; omega)]
  simp [coreBitAt, hIndex, hDiv, hMod]

set_option linter.flexible false in
@[simp]
theorem xToT_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (i j : Nat) (hi : i < x) (hj : j < tSize x) :
    xToT (coreBits R hx h p t w) i j =
      decide (R (h ⟨2 + i, by simp [hSize]; omega⟩) (t ⟨j, hj⟩)) := by
  have hDiv : (i * tSize x + j) / tSize x = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by simp [tSize]; omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * tSize x + j) % tSize x = j := Nat.mul_add_mod_of_lt hj
  have hNotCore : ¬coreSize x * coreSize x + i * tSize x + j <
      coreSize x * coreSize x := by omega
  have hIndex : coreSize x * coreSize x + i * tSize x + j <
      coreSize x * coreSize x + x * tSize x := by
    rw [Nat.add_assoc]
    apply Nat.add_lt_add_left
    calc
      i * tSize x + j < i * tSize x + tSize x := Nat.add_lt_add_left hj _
      _ = (i + 1) * tSize x := by simp [Nat.add_mul]
      _ ≤ x * tSize x := Nat.mul_le_mul_right _ (Nat.add_one_le_iff.mpr hi)
  have hSub : coreSize x * coreSize x + i * tSize x + j -
      coreSize x * coreSize x = i * tSize x + j := by omega
  rw [xToT, getLsbD_coreBits R hx h p t w _ (by
    simp [coreWidth]; omega)]
  simp [coreBitAt, hNotCore, hIndex, hSub, hDiv, hMod]
  rw [hAt_of_lt h (2 + i) (by simp [hSize]; omega), tAt_of_lt hx t j hj]

set_option linter.flexible false in
@[simp]
theorem pToW_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (i j : Nat) (hi : i < 6) (hj : j < wSize x) :
    pToW (coreBits R hx h p t w) i j =
      decide (R (p ⟨i, hi⟩) (w ⟨j, hj⟩)) := by
  let start := coreSize x * coreSize x + x * tSize x
  have hDiv : (i * wSize x + j) / wSize x = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by simp [wSize]; omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * wSize x + j) % wSize x = j := Nat.mul_add_mod_of_lt hj
  have hNotCore : ¬start + i * wSize x + j < coreSize x * coreSize x := by
    dsimp [start]
    omega
  have hNotT : ¬start + i * wSize x + j < start := by omega
  have hIndex : start + i * wSize x + j < coreWidth x := by
    dsimp [start]
    simp [coreWidth]
    rw [Nat.add_assoc]
    apply Nat.add_lt_add_left
    calc
      i * wSize x + j < i * wSize x + wSize x := Nat.add_lt_add_left hj _
      _ = (i + 1) * wSize x := by simp [Nat.add_mul]
      _ ≤ 6 * wSize x := Nat.mul_le_mul_right _ (Nat.add_one_le_iff.mpr hi)
  have hSub : start + i * wSize x + j - start = i * wSize x + j := by omega
  rw [pToW, getLsbD_coreBits R hx h p t w _ hIndex]
  simp [coreBitAt, start, hNotCore, hNotT, hIndex, hSub, hDiv, hMod]
  rw [pAt_of_lt p i hi, wAt_of_lt hx w j hj]

theorem allN_eq_true_iff (n : Nat) (f : Nat → Bool) :
    allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
      simp only [allN, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hBefore, hLast⟩ i hi
        by_cases hin : i < n
        · exact hBefore i hin
        · have : i = n := by omega
          simpa [this] using hLast
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

theorem anyN_eq_true_iff (n : Nat) (f : Nat → Bool) :
    anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [anyN]
  | succ n ih =>
      simp only [anyN, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hLast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hLast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · have : i = n := by omega
          exact Or.inr (this ▸ hfi)

/-- A byte-sized Boolean sum agrees with its ordinary natural-number sum. -/
theorem toNat_sumN (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (sumN n f).toNat = ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hSumLe : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤
              ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [sumN, BitVec.toNat_add, ih hn']
      rw [Finset.sum_range_succ]
      have hLt0 : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) < 256 := by
        omega
      have hLt1 : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) + 1 < 256 := by
        omega
      have hLt0' :
          (∑ i ∈ Finset.range n,
            (if f i then (1 : BitVec 8) else 0).toNat) < 256 := by
        simpa [bitCount] using hLt0
      have hLt1' :
          (∑ i ∈ Finset.range n,
            (if f i then (1 : BitVec 8) else 0).toNat) + 1 < 256 := by
        simpa [bitCount] using hLt1
      cases hfn : f n
      · simp only [bitCount]
        exact Nat.mod_eq_of_lt hLt0'
      · simp only [bitCount, ↓reduceIte]
        exact Nat.mod_eq_of_lt hLt1'

def trueCount (n : Nat) (f : Nat → Bool) : Nat :=
  ((Finset.range n).filter fun i ↦ f i = true).card

theorem trueCount_le (n : Nat) (f : Nat → Bool) : trueCount n f ≤ n := by
  unfold trueCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range n)

theorem trueCount_congr {n : Nat} {f g : Nat → Bool}
    (h : ∀ i < n, f i = g i) : trueCount n f = trueCount n g := by
  unfold trueCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hfi⟩
    exact ⟨hi, (h i hi) ▸ hfi⟩
  · rintro ⟨hi, hgi⟩
    exact ⟨hi, (h i hi).symm ▸ hgi⟩

theorem toNat_sumN_eq_trueCount (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (sumN n f).toNat = trueCount n f := by
  rw [toNat_sumN n f hn]
  unfold trueCount
  simp only [bitCount]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : f i <;> simp

theorem trueCount_eq_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    trueCount n f = ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  rw [← toNat_sumN n f hn, toNat_sumN_eq_trueCount n f hn]

theorem trueCount_eq_filter_fin (n : Nat) (f : Nat → Bool) :
    trueCount n f = ((Finset.univ : Finset (Fin n)).filter
      fun i ↦ f i.val = true).card := by
  unfold trueCount
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if f i = true then 1 else 0) n]

/-- The represented second-neighbor byte is the sum of its three block counts. -/
theorem toNat_representedSecondCount {x : Nat} (hx : x ≤ 5)
    (bits : BitVec (coreWidth x)) (u : Nat) :
    (representedSecondCount bits u).toNat =
      trueCount (coreSize x) (fun target ↦
        decide (target ≠ u) && !arc bits u target &&
          reachedInCore bits u target) +
      trueCount (tSize x) (reachedT bits u) +
      trueCount (wSize x) (reachedW bits u) := by
  have hCore := trueCount_le (coreSize x) (fun target ↦
    decide (target ≠ u) && !arc bits u target && reachedInCore bits u target)
  have hT := trueCount_le (tSize x) (reachedT bits u)
  have hW := trueCount_le (wSize x) (reachedW bits u)
  have hFirst :
      trueCount (coreSize x) (fun target ↦
        decide (target ≠ u) && !arc bits u target && reachedInCore bits u target) +
        trueCount (tSize x) (reachedT bits u) < 256 := by
    unfold coreSize at hCore
    unfold tSize at hT
    unfold coreSize tSize
    omega
  have hAll :
      trueCount (coreSize x) (fun target ↦
        decide (target ≠ u) && !arc bits u target && reachedInCore bits u target) +
        trueCount (tSize x) (reachedT bits u) +
          trueCount (wSize x) (reachedW bits u) < 256 := by
    unfold coreSize at hCore
    unfold tSize at hT
    unfold wSize at hW
    unfold coreSize tSize wSize
    omega
  rw [representedSecondCount, BitVec.toNat_add, BitVec.toNat_add,
    secondCoreCount,
    toNat_sumN_eq_trueCount _ _ (by unfold coreSize; omega),
    toNat_sumN_eq_trueCount _ _ (by unfold tSize; omega),
    toNat_sumN_eq_trueCount _ _ (by unfold wSize; omega)]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt hFirst, Nat.mod_eq_of_lt hAll]

theorem toNat_internalOut {x : Nat} (hx : x ≤ 5)
    (bits : BitVec (coreWidth x)) (u : Nat) :
    (internalOut bits u).toNat = trueCount (coreSize x) (arc bits u) := by
  exact toNat_sumN_eq_trueCount _ _ (by unfold coreSize; omega)

/-- Decode an `H`-row degree byte into its three labelled blocks. -/
theorem toNat_hDegree_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (i : Nat) (hi : i < hSize x) :
    (hDegree (coreBits R hx h p t w) i).toNat =
      trueCount (coreSize x) (fun j ↦
        decide (R (h ⟨i, hi⟩) (coreAt h p j))) +
      (if 2 ≤ i then trueCount (tSize x) (fun j ↦
        decide (R (h ⟨i, hi⟩) (tAt hx t j))) else 0) := by
  let bits := coreBits R hx h p t w
  have hCore := trueCount_le (coreSize x) (arc bits i)
  have hArc : trueCount (coreSize x) (arc bits i) =
      trueCount (coreSize x) (fun j ↦
        decide (R (h ⟨i, hi⟩) (coreAt h p j))) := by
    apply trueCount_congr
    intro j hj
    rw [arc_coreBits R hx h p t w i j (by
      unfold coreSize
      unfold hSize at hi
      omega) hj,
      coreAt_h h p i hi]
  by_cases hi2 : 2 ≤ i
  · have hix : i - 2 < x := by unfold hSize at hi; omega
    have hT := trueCount_le (tSize x) (xToT bits (i - 2))
    have hX : h ⟨i, hi⟩ = h ⟨2 + (i - 2), by unfold hSize; omega⟩ := by
      apply congrArg h
      apply Fin.ext
      have hiEq : 2 + (i - 2) = i := by omega
      exact hiEq.symm
    have hTDecode : trueCount (tSize x) (xToT bits (i - 2)) =
        trueCount (tSize x) (fun j ↦
          decide (R (h ⟨i, hi⟩) (tAt hx t j))) := by
      apply trueCount_congr
      intro j hj
      rw [xToT_coreBits R hx h p t w (i - 2) j hix hj,
        tAt_of_lt hx t j hj, hX]
    have hBound : trueCount (coreSize x) (arc bits i) +
        trueCount (tSize x) (xToT bits (i - 2)) < 256 := by
      unfold coreSize at hCore
      unfold tSize at hT
      unfold coreSize tSize
      omega
    have hBound' : trueCount (coreSize x) (fun j ↦
          decide (R (h ⟨i, hi⟩) (coreAt h p j))) +
        trueCount (tSize x) (fun j ↦
          decide (R (h ⟨i, hi⟩) (tAt hx t j))) < 256 := by
      rw [← hArc, ← hTDecode]
      exact hBound
    rw [hDegree, if_pos hi2, BitVec.toNat_add,
      toNat_internalOut hx bits i,
      toNat_sumN_eq_trueCount _ _ (by unfold tSize; omega), hArc, hTDecode]
    simp only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt hBound']
    simp [hi2]
  · rw [hDegree, if_neg hi2, BitVec.toNat_add,
      toNat_internalOut hx bits i, hArc]
    have hBound' : trueCount (coreSize x) (fun j ↦
        decide (R (h ⟨i, hi⟩) (coreAt h p j))) < 256 := by
      rw [← hArc]
      unfold coreSize at hCore
      unfold coreSize
      omega
    simp only [Nat.reducePow]
    rw [show (0 : BitVec 8).toNat = 0 by decide, Nat.add_zero,
      Nat.mod_eq_of_lt hBound']
    · simp [hi2]

/-- Decode a `P`-row degree byte into the core and external blocks. -/
theorem toNat_pDegree_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (i : Nat) (hi : i < 6) :
    (pDegree (coreBits R hx h p t w) i).toNat =
      trueCount (coreSize x) (fun j ↦
        decide (R (p ⟨i, hi⟩) (coreAt h p j))) +
      trueCount (wSize x) (fun j ↦
        decide (R (p ⟨i, hi⟩) (wAt hx w j))) := by
  let bits := coreBits R hx h p t w
  have hCore := trueCount_le (coreSize x) (arc bits (hSize x + i))
  have hW := trueCount_le (wSize x) (pToW bits i)
  have hArc : trueCount (coreSize x) (arc bits (hSize x + i)) =
      trueCount (coreSize x) (fun j ↦
        decide (R (p ⟨i, hi⟩) (coreAt h p j))) := by
    apply trueCount_congr
    intro j hj
    rw [arc_coreBits R hx h p t w (hSize x + i) j
      (by unfold coreSize; unfold hSize; omega) hj, coreAt_p h p i hi]
  have hWDecode : trueCount (wSize x) (pToW bits i) =
      trueCount (wSize x) (fun j ↦
        decide (R (p ⟨i, hi⟩) (wAt hx w j))) := by
    apply trueCount_congr
    intro j hj
    rw [pToW_coreBits R hx h p t w i j hi hj, wAt_of_lt hx w j hj]
  have hBound : trueCount (coreSize x) (arc bits (hSize x + i)) +
      trueCount (wSize x) (pToW bits i) < 256 := by
    unfold coreSize at hCore
    unfold wSize at hW
    unfold coreSize wSize
    omega
  have hBound' : trueCount (coreSize x) (fun j ↦
        decide (R (p ⟨i, hi⟩) (coreAt h p j))) +
      trueCount (wSize x) (fun j ↦
        decide (R (p ⟨i, hi⟩) (wAt hx w j))) < 256 := by
    rw [← hArc, ← hWDecode]
    exact hBound
  rw [pDegree, BitVec.toNat_add,
    toNat_internalOut hx bits (hSize x + i),
    toNat_sumN_eq_trueCount _ _ (by unfold wSize; omega), hArc, hWDecode]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt hBound']

/-- A non-overflowing sum of byte counts agrees with the natural sum. -/
theorem toNat_sumCountsN (n : Nat) (f : Nat → BitVec 8)
    (hTotal : (∑ i ∈ Finset.range n, (f i).toNat) < 256) :
    (sumCountsN n f).toNat = ∑ i ∈ Finset.range n, (f i).toNat := by
  induction n with
  | zero => simp [sumCountsN]
  | succ n ih =>
      rw [Finset.sum_range_succ] at hTotal ⊢
      have hBefore : (∑ i ∈ Finset.range n, (f i).toNat) < 256 := by omega
      rw [sumCountsN, BitVec.toNat_add, ih hBefore]
      simp only [Nat.reducePow]
      rw [Nat.mod_eq_of_lt hTotal]

/-- The Boolean orientation test is sound for any labelled oriented relation. -/
theorem oriented_coreBits {x : Nat} (hx : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (hLoopless : ∀ u, ¬R u u)
    (hAnti : ∀ u v, R u v → ¬R v u) :
    oriented (coreBits R hx h p t w) = true := by
  rw [oriented, allN_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true]
  constructor
  · simp [arc_coreBits R hx h p t w i i hi hi, hLoopless]
  · rw [allN_eq_true_iff]
    intro j hj
    simp only [arc_coreBits R hx h p t w i j hi hj,
      arc_coreBits R hx h p t w j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    · have hOneMissing : ¬R (coreAt h p i) (coreAt h p j) ∨
          ¬R (coreAt h p j) (coreAt h p i) := by
        exact not_and_or.mp (fun hb ↦ hAnti _ _ hb.1 hb.2)
      rcases hOneMissing with hForward | hReverse
      · simp [hij, hForward]
      · simp [hij, hReverse]

/-- Assemble `baseCore` from its four families of byte-level inequalities. -/
theorem baseCore_true_of {x : Nat} (bits : BitVec (coreWidth x))
    (hOriented : oriented bits = true)
    (hH : ∀ i < hSize x, 8 ≤ (hDegree bits i).toNat)
    (hP : ∀ i < 6, 8 ≤ (pDegree bits i).toNat)
    (hInternal : ∀ u < 2, 2 ≤ (sumN (hSize x) (arc bits u)).toNat)
    (hSecond : ∀ u < 2,
      (representedSecondCount bits u).toNat < (internalOut bits u).toNat) :
    baseCore bits = true := by
  have hh : allN (hSize x)
      (fun i ↦ (8 : BitVec 8).ule (hDegree bits i)) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    simpa using hH i hi
  have hp : allN 6 (fun i ↦ (8 : BitVec 8).ule (pDegree bits i)) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    simpa using hP i hi
  have ha : allN 2 (fun u ↦
      (2 : BitVec 8).ule (sumN (hSize x) (arc bits u)) &&
        (representedSecondCount bits u).ult (internalOut bits u)) = true := by
    rw [allN_eq_true_iff]
    intro u hu
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, BitVec.ult_eq_decide,
      decide_eq_true_eq]
    exact ⟨by simpa using hInternal u hu, hSecond u hu⟩
  rw [baseCore]
  simpa only [Bool.and_eq_true] using ⟨⟨⟨hOriented, hh⟩, hp⟩, ha⟩

end SeymourEight.BSixKTwoCoreBridge
