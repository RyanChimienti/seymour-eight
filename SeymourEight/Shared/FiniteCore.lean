import Std.Tactic.BVDecide
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Shared combinators for finite obstruction certificates

These definitions are independent of any particular local-configuration
layout.  Case-specific certificate modules should define only their bit
encoding and graph predicates on top of this small interface.
-/

namespace SeymourEight.Shared.FiniteCore

open scoped BigOperators

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def sumCount : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumCount n p + p n

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat =
      ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hSumLe : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [count, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      have hLt0 : (∑ i ∈ Finset.range n,
          (bitCount (f i)).toNat) < 256 := by omega
      have hLt1 : (∑ i ∈ Finset.range n,
          (bitCount (f i)).toNat) + 1 < 256 := by omega
      cases hfn : f n
      · simpa [bitCount, hfn] using Nat.mod_eq_of_lt hLt0
      · simpa [bitCount, hfn] using Nat.mod_eq_of_lt hLt1

theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ (bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [bitCount]

theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · simpa [show i = n by omega] using hn
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [any]
  | succ n ih =>
      simp only [any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hLast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hLast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · exact Or.inr (show i = n by omega ▸ hfi)

end SeymourEight.Shared.FiniteCore
