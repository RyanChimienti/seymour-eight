import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.PCompatibility
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGraphBridge
import Mathlib.Tactic.IntervalCases

/-!
# Capacity compatibility for the three-`Z` core

These small Boolean facts justify the lossless saturated encodings.  They
involve only the `P-P` or `P-H` incidence block, not the full obstruction.
-/

namespace SeymourEight.ThreeZHighDefect

open FiveZExactRisk

set_option maxRecDepth 100000

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
        · have : i = n := by omega
          simpa [this] using hn
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private def boolNat (b : Bool) : Nat := if b then 1 else 0

private theorem sum_eq_card_forces_one (S : Finset Nat) (t : Nat → Nat)
    (hle : ∀ i ∈ S, t i ≤ 1) (hsum : ∑ i ∈ S, t i = S.card) :
    ∀ i ∈ S, t i = 1 := by
  intro i hi
  have hrest : ∑ j ∈ S.erase i, t j ≤ (S.erase i).card := by
    calc
      _ ≤ ∑ _j ∈ S.erase i, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hle j (Finset.mem_of_mem_erase hj)
      _ = (S.erase i).card := by simp
  have herase : (S.erase i).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hi]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hsplit := Finset.sum_erase_add _ (fun j ↦ t j) hi
  have hii := hle i hi
  omega

private theorem ph_pair_sums (bits : BitVec 218)
    (hor : orientedPH bits = true) :
    ∀ q < 35,
      boolNat (pToH bits (q / 5) (q % 5)) +
        boolNat (hToP bits (q % 5) (q / 5)) ≤ 1 := by
  intro q hq
  have hi : q / 5 < 7 := by omega
  have hh : q % 5 < 5 := Nat.mod_lt _ (by omega)
  have hrow := (all_eq_true_iff 7 _).mp hor (q / 5) hi
  have hpair := (all_eq_true_iff 5 _).mp hrow (q % 5) hh
  simp only [Bool.not_eq_true'] at hpair
  cases hp : pToH bits (q / 5) (q % 5) <;>
    cases hh' : hToP bits (q % 5) (q / 5) <;>
    simp_all [boolNat]

set_option maxHeartbeats 4000000 in
private theorem ph_total_sum (bits : BitVec 218)
    (forward reverse : Nat)
    (hforward : totalPToH bits = BitVec.ofNat 8 forward)
    (hreverse : totalHToP bits = BitVec.ofNat 8 reverse)
    (hf : forward < 256) (hr : reverse < 256) :
    ∑ q ∈ Finset.range 35,
      (boolNat (pToH bits (q / 5) (q % 5)) +
        boolNat (hToP bits (q % 5) (q / 5))) = forward + reverse := by
  have hf' := congrArg BitVec.toNat hforward
  have hr' := congrArg BitVec.toNat hreverse
  rw [totalPToH, FiveZExactGraphBridge.toNat_count 35 _ (by omega)] at hf'
  rw [totalHToP, FiveZExactGraphBridge.toNat_count 35 _ (by omega)] at hr'
  have hfValue : (BitVec.ofNat 8 forward).toNat = forward := by
    simp [Nat.mod_eq_of_lt hf]
  have hrValue : (BitVec.ofNat 8 reverse).toNat = reverse := by
    simp [Nat.mod_eq_of_lt hr]
  rw [hfValue] at hf'
  rw [hrValue] at hr'
  have hfNat : ∑ q ∈ Finset.range 35,
      boolNat (pToH bits (q / 5) (q % 5)) = forward := by
    rw [← hf']
    apply Finset.sum_congr rfl
    intro q hq
    cases pToH bits (q / 5) (q % 5) <;> rfl
  have hrNat : ∑ q ∈ Finset.range 35,
      boolNat (hToP bits (q % 5) (q / 5)) = reverse := by
    rw [← hr']
    apply Finset.sum_congr rfl
    intro q hq
    cases hToP bits (q % 5) (q / 5) <;> rfl
  rw [Finset.sum_add_distrib, hfNat, hrNat]

private theorem firstTrueBV_congr (w n : Nat) (f g : Nat → Bool)
    (h : ∀ i < n, f i = g i) : firstTrueBV w n f = firstTrueBV w n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      rw [firstTrueBV, firstTrueBV, h 0 (by omega)]
      split
      · rfl
      · congr 1
        apply ih
        intro i hi
        exact h (i + 1) (by omega)

theorem phComplete_of_capacity (bits : BitVec 218)
    (hor : orientedPH bits = true)
    (hforward : totalPToH bits = 17)
    (hreverse : totalHToP bits = 18) :
    phComplete bits = true := by
  have hsum := ph_total_sum bits 17 18 hforward hreverse (by omega) (by omega)
  have hone := sum_eq_card_forces_one (Finset.range 35)
    (fun q ↦ boolNat (pToH bits (q / 5) (q % 5)) +
      boolNat (hToP bits (q % 5) (q / 5)))
    (fun q hq ↦ ph_pair_sums bits hor q (Finset.mem_range.mp hq)) (by simpa using hsum)
  rw [phComplete, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro h hh
  have hp := hone (i * 5 + h) (Finset.mem_range.mpr (by omega))
  have hdiv : (i * 5 + h) / 5 = i := by omega
  have hmod : (i * 5 + h) % 5 = h := by omega
  simp only [hdiv, hmod] at hp
  cases hpv : pToH bits i h <;> cases hhv : hToP bits h i <;>
    simp_all [boolNat]

set_option maxHeartbeats 8000000 in
theorem phOneComplete_of_capacity (bits : BitVec 218)
    (hor : orientedPH bits = true)
    (hforward : totalPToH bits = 16)
    (hreverse : totalHToP bits = 18) : phOneComplete bits = true := by
  let t := fun q ↦ boolNat (pToH bits (q / 5) (q % 5)) +
    boolNat (hToP bits (q % 5) (q / 5))
  have hle : ∀ q ∈ Finset.range 35, t q ≤ 1 := fun q hq ↦
    ph_pair_sums bits hor q (Finset.mem_range.mp hq)
  have hsum : ∑ q ∈ Finset.range 35, t q = 34 := by
    simpa [t] using ph_total_sum bits 16 18 hforward hreverse (by omega) (by omega)
  have hex : ∃ q < 35, t q = 0 := by
    by_contra hn
    push Not at hn
    have hall : ∀ q ∈ Finset.range 35, t q = 1 := by
      intro q hq
      have := hle q hq
      have := hn q (Finset.mem_range.mp hq)
      omega
    have : ∑ q ∈ Finset.range 35, t q = 35 := by
      calc
        _ = ∑ _q ∈ Finset.range 35, 1 := by
          apply Finset.sum_congr rfl
          intro q hq
          exact hall q hq
        _ = 35 := by simp
    omega
  obtain ⟨q, hq, hq0⟩ := hex
  have hother : ∀ j < 35, j ≠ q → t j = 1 := by
    have hrestSum : ∑ j ∈ (Finset.range 35).erase q, t j =
        ((Finset.range 35).erase q).card := by
      have hsplit := Finset.sum_erase_add (Finset.range 35) t
        (Finset.mem_range.mpr hq)
      rw [hq0] at hsplit
      have hcard : ((Finset.range 35).erase q).card = 34 := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hq)]
        simp
      omega
    have hall := sum_eq_card_forces_one ((Finset.range 35).erase q) t
      (fun j hj ↦ hle j (Finset.mem_of_mem_erase hj)) hrestSum
    intro j hj hjq
    exact hall j (Finset.mem_erase.mpr ⟨hjq, Finset.mem_range.mpr hj⟩)
  have hqMissing : pToH bits (q / 5) (q % 5) = false ∧
      hToP bits (q % 5) (q / 5) = false := by
    cases hp : pToH bits (q / 5) (q % 5) <;>
      cases hh : hToP bits (q % 5) (q / 5) <;> simp_all [t, boolNat]
  have hpred : ∀ j < 35,
      (!pToH bits (j / 5) (j % 5) && !hToP bits (j % 5) (j / 5)) =
        decide (j = q) := by
    intro j hj
    by_cases hjq : j = q
    · subst j
      simp [hqMissing]
    · have hjOne := hother j hj hjq
      cases hp : pToH bits (j / 5) (j % 5) <;>
        cases hh : hToP bits (j % 5) (j / 5)
      all_goals simp [t, boolNat, hp, hh] at hjOne
      all_goals simp [hjq]
  have hidx : phMissingIndex bits = BitVec.ofNat 6 q := by
    rw [phMissingIndex, firstTrueBV_congr 6 35 _ _ hpred]
    interval_cases q <;> decide
  rw [phOneComplete, hidx, Bool.and_eq_true]
  constructor
  · simp only [BitVec.ult_eq_decide, decide_eq_true_eq,
      BitVec.toNat_ofNat, Nat.reducePow,
      Nat.mod_eq_of_lt (by omega : q < 64)]
    have h35 : (35 : BitVec 6).toNat = 35 := by decide
    rw [h35]
    exact hq
  · rw [all_eq_true_iff]
    intro j hj
    by_cases hjq : j = q
    · subst j
      simp [hqMissing]
    · have hjOne := hother j hj hjq
      have hcodeNe : BitVec.ofNat 6 q ≠ BitVec.ofNat 6 j := by
        intro heq
        have heqNat := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.reducePow,
          Nat.mod_eq_of_lt (by omega : q < 64),
          Nat.mod_eq_of_lt (by omega : j < 64)] at heqNat
        exact hjq heqNat.symm
      simp only [beq_eq_false_iff_ne.mpr hcodeNe]
      cases hp : pToH bits (j / 5) (j % 5) <;>
        cases hh : hToP bits (j % 5) (j / 5)
      all_goals simp [t, boolNat, hp, hh] at hjOne
      all_goals simp

set_option maxHeartbeats 8000000 in
theorem phComplete_of_capacity_sixteen_nineteen (bits : BitVec 218)
    (hor : orientedPH bits = true)
    (hforward : totalPToH bits = 16)
    (hreverse : totalHToP bits = 19) : phComplete bits = true := by
  have hsum := ph_total_sum bits 16 19 hforward hreverse (by omega) (by omega)
  have hone := sum_eq_card_forces_one (Finset.range 35)
    (fun q ↦ boolNat (pToH bits (q / 5) (q % 5)) +
      boolNat (hToP bits (q % 5) (q / 5)))
    (fun q hq ↦ ph_pair_sums bits hor q (Finset.mem_range.mp hq)) (by simpa using hsum)
  rw [phComplete, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro h hh
  have hp := hone (i * 5 + h) (Finset.mem_range.mpr (by omega))
  have hdiv : (i * 5 + h) / 5 = i := by omega
  have hmod : (i * 5 + h) % 5 = h := by omega
  simp only [hdiv, hmod] at hp
  cases hpv : pToH bits i h <;> cases hhv : hToP bits h i <;>
    simp_all [boolNat]

end SeymourEight.ThreeZHighDefect
