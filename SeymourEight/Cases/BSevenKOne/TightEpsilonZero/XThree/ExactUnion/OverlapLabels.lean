import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.GraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactLabels
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

/-! Canonical `H`/external-union labels and overlap types. -/

namespace SeymourEight.FourZExactSevenOverlapLabels

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge
  FiveZExactGlobalBridge FiveZExactLabels Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 3000000 in
/-- The 14-bit directed incidence code of an actual vertex against `P`. -/
def vertexHCode (p : Fin 7 → V) (v : V) : BitVec 16 :=
  count16 7 fun i =>
    (bitCount16 (decide (G.Adj (p ⟨i % 7, Nat.mod_lt _ (by omega)⟩) v)) <<< i) +
      (bitCount16 (decide (G.Adj v
        (p ⟨i % 7, Nat.mod_lt _ (by omega)⟩))) <<< (7 + i))

set_option maxHeartbeats 3000000 in
/-- Sort the three `X` labels with members of `W` first and, inside either
membership block, with decreasing directed incidence code. -/
def xSortPermutation (p : Fin 7 → V) (W : Finset V) (x : Fin 3 → V) :
    Equiv.Perm (Fin 3) :=
  Tuple.sort fun i => OrderDual.toDual
    (65536 * (if x i ∈ W then 1 else 0) + (vertexHCode G p (x i)).toNat)

set_option maxHeartbeats 3000000 in
def sortedX (p : Fin 7 → V) (W : Finset V) (x : Fin 3 → V) : Fin 3 → V :=
  x ∘ xSortPermutation G p W x

set_option maxHeartbeats 3000000 in
omit [Fintype V] in
theorem sortedX_bijective (p : Fin 7 → V) (W : Finset V) (x : Fin 3 → V)
    (hx : Function.Bijective x) :
    Function.Bijective (sortedX G p W x) :=
  hx.comp (xSortPermutation G p W x).bijective

set_option maxHeartbeats 3000000 in
set_option maxHeartbeats 1000000 in
omit [Fintype V] in
theorem sortedX_key_anti (p : Fin 7 → V) (W : Finset V) (x : Fin 3 → V)
    {i j : Fin 3} (hij : i ≤ j) :
    65536 * (if sortedX G p W x i ∈ W then 1 else 0) +
        (vertexHCode G p (sortedX G p W x i)).toNat ≥
      65536 * (if sortedX G p W x j ∈ W then 1 else 0) +
        (vertexHCode G p (sortedX G p W x j)).toNat := by
  classical
  have hSorted := Tuple.monotone_sort (fun k => OrderDual.toDual
    (65536 * (if x k ∈ W then 1 else 0) +
      (vertexHCode G p (x k)).toNat)) hij
  exact hSorted

set_option maxHeartbeats 3000000 in
/-- Label `H=A1∪X` with the unique `A1` vertex first and the sorted `X`
vertices in positions one through three. -/
noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (hHCard : C.H.card = 4)
    (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X})
    (p : Fin 7 → V) (W : Finset V) :
    Fin 4 ≃ {v : V // v ∈ C.H} := by
  let xs := sortedX G p W (fun i => (eX i).1)
  let f : Fin 4 → {v : V // v ∈ C.H} := fun i =>
    if hi : i.val = 0 then
      ⟨(eA1 0).1, Finset.mem_union_left C.X (eA1 0).2⟩
    else
      ⟨xs ⟨i.val - 1, by omega⟩,
        Finset.mem_union_right C.A1
          ((eX (xSortPermutation G p W (fun j => (eX j).1)
            ⟨i.val - 1, by omega⟩)).2)⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    rcases Finset.mem_union.mp v.2 with hvA1 | hvX
    · obtain ⟨i, hi⟩ := eA1.surjective ⟨v.1, hvA1⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := eX.surjective ⟨v.1, hvX⟩
      let j := (xSortPermutation G p W (fun q => (eX q).1)).symm i
      refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, xs, sortedX, j, show j.val + 1 ≠ 0 by omega] using
        congrArg Subtype.val hi
  · simp [hHCard]

@[simp] theorem hLabelEquiv_zero (C : G.LocalConfiguration)
    (hHCard : C.H.card = 4) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X}) (p : Fin 7 → V) (W : Finset V) :
    (hLabelEquiv G C hHCard eA1 eX p W 0).1 = (eA1 0).1 := by rfl

@[simp] theorem hLabelEquiv_succ (C : G.LocalConfiguration)
    (hHCard : C.H.card = 4) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X}) (p : Fin 7 → V) (W : Finset V)
    (i : Fin 3) :
    (hLabelEquiv G C hHCard eA1 eX p W (Fin.succ i)).1 =
      sortedX G p W (fun j => (eX j).1) i := by
  simp [hLabelEquiv, sortedX]

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem hCode_coreBits (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (i : Nat) (hi : i < 4) :
    FourZExactSeven.hCode (coreBits G.Adj p h a z w) i =
      vertexHCode G p (h ⟨i, hi⟩) := by
  classical
  have hp : ∀ j : Nat, (hj : j < 7) →
      FourZExactSeven.pToH (coreBits G.Adj p h a z w) j i =
        decide (G.Adj (p ⟨j, hj⟩) (h ⟨i, hi⟩)) := by
    intro j hj
    exact FourZExactSevenBridge.pToH_coreBits G.Adj p h a z w
      j i hj hi
  have hh : ∀ j : Nat, (hj : j < 7) →
      FourZExactSeven.hToP (coreBits G.Adj p h a z w) i j =
        decide (G.Adj (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
    intro j hj
    exact FourZExactSevenBridge.hToP_coreBits G.Adj p h a z w
      i j hi hj
  unfold FourZExactSeven.hCode vertexHCode
  simp only [count16]
  rw [hp 0 (by omega), hh 0 (by omega), hp 1 (by omega), hh 1 (by omega),
    hp 2 (by omega), hh 2 (by omega), hp 3 (by omega), hh 3 (by omega),
    hp 4 (by omega), hh 4 (by omega), hp 5 (by omega), hh 5 (by omega),
    hp 6 (by omega), hh 6 (by omega)]

set_option maxHeartbeats 3000000 in
omit [Fintype V] in
theorem sortedX_mem_iff_lt_inter_card (p : Fin 7 → V) (W X : Finset V)
    (eX : Fin 3 ≃ {v : V // v ∈ X}) (i : Fin 3) :
    sortedX G p W (fun j => (eX j).1) i ∈ W ↔ i.val < (W ∩ X).card := by
  classical
  let xs := sortedX G p W (fun j => (eX j).1)
  have hxMem : ∀ j : Fin 3, xs j ∈ X := by
    intro j
    exact (eX (xSortPermutation G p W (fun q => (eX q).1) j)).2
  have hCodeLt : ∀ j : Fin 3, (vertexHCode G p (xs j)).toNat < 65536 := by
    intro j
    simpa using (vertexHCode G p (xs j)).isLt
  have hMono01 : xs 1 ∈ W → xs 0 ∈ W := by
    intro h1
    by_contra h0
    have hk := sortedX_key_anti G p W (fun j => (eX j).1)
      (i := 0) (j := 1) (by decide)
    simp only [xs] at h0 h1 hk ⊢
    simp [h0, h1] at hk
    have h0c := hCodeLt 0
    omega
  have hMono12 : xs 2 ∈ W → xs 1 ∈ W := by
    intro h2
    by_contra h1
    have hk := sortedX_key_anti G p W (fun j => (eX j).1)
      (i := 1) (j := 2) (by decide)
    simp only [xs] at h1 h2 hk ⊢
    simp [h1, h2] at hk
    have h1c := hCodeLt 1
    omega
  have hCount : (W ∩ X).card =
      (if xs 0 ∈ W then 1 else 0) + (if xs 1 ∈ W then 1 else 0) +
        (if xs 2 ∈ W then 1 else 0) := by
    have heq : W ∩ X = X.filter (fun v => v ∈ W) := by
      ext v
      simp [and_comm]
    rw [heq, filterCard_eq_sum_fin X
      ((xSortPermutation G p W (fun j => (eX j).1)).trans eX)
      (fun v => v ∈ W)]
    simp [Fin.sum_univ_succ, xs, sortedX, Nat.add_assoc]
    rfl
  have hCardLe : (W ∩ X).card ≤ 3 := by
    exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (by
      simpa using (Fintype.card_congr eX).symm)
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hiCases with rfl | rfl | rfl <;>
    by_cases h0 : xs 0 ∈ W <;>
    by_cases h1 : xs 1 ∈ W <;>
    by_cases h2 : xs 2 ∈ W <;>
    simp_all [xs]

set_option maxHeartbeats 3000000 in
theorem hLabel_mem_iff (C : G.LocalConfiguration)
    (hHCard : C.H.card = 4) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X}) (p : Fin 7 → V) (W : Finset V)
    (i : Fin 3) :
    (hLabelEquiv G C hHCard eA1 eX p W (Fin.succ i)).1 ∈ W ↔
      i.val < (W ∩ C.X).card := by
  rw [hLabelEquiv_succ]
  exact sortedX_mem_iff_lt_inter_card G p W C.X eX i

set_option maxHeartbeats 3000000 in
omit [Fintype V] in
theorem sortedX_code_anti_of_same_mem (p : Fin 7 → V) (W : Finset V)
    (x : Fin 3 → V) {i j : Fin 3} (hij : i ≤ j)
    (hSame : (sortedX G p W x i ∈ W) = (sortedX G p W x j ∈ W)) :
    (vertexHCode G p (sortedX G p W x j)).toNat ≤
      (vertexHCode G p (sortedX G p W x i)).toNat := by
  classical
  have hk := sortedX_key_anti G p W x hij
  split at hk <;> split at hk <;> simp_all

set_option maxHeartbeats 3000000 in
private theorem hWH_of_mem_and_prefix {C : G.LocalConfiguration}
    (W : Finset V) (overlap : OverlapType)
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (w : Fin 7 ≃ {v : V // v ∈ W})
    (hMem : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ W ↔ hInW overlap hi = true))
    (hPrefix : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      wMatchesH overlap wi hi = true →
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1) :
    ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1) := by
  intro wi hi hwi hhi
  constructor
  · exact hPrefix wi hi hwi hhi
  · intro heq
    have hhW : (h ⟨hi, hhi⟩).1 ∈ W := by
      rw [← heq]
      exact (w ⟨wi, hwi⟩).2
    have hb := (hMem hi hhi).mp hhW
    rw [hInW, any_eq_true_iff] at hb
    obtain ⟨q, hq, hMatch⟩ := hb
    have hqEq := hPrefix q hi hq hhi hMatch
    have hIndex : (⟨wi, hwi⟩ : Fin 7) = ⟨q, hq⟩ := by
      apply w.injective
      apply Subtype.ext
      exact heq.trans hqEq.symm
    have : wi = q := congrArg Fin.val hIndex
    subst q
    exact hMatch

set_option maxHeartbeats 3000000 in
private noncomputable def finsetEquivFinAtZeroOneTwoThree (S : Finset V)
    (hCard : S.card = 7) (v0 : V) (hv0 : v0 ∈ S)
    (v1 : V) (hv1 : v1 ∈ S) (v2 : V) (hv2 : v2 ∈ S)
    (v3 : V) (hv3 : v3 ∈ S)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (_h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (_h13 : v1 ≠ v3) (_h23 : v2 ≠ v3) :
    Fin 7 ≃ {v : V // v ∈ S} :=
  let e := FiveZExactLabels.finsetEquivFinAtZeroOneTwo S (by omega) hCard
    v0 hv0 v1 hv1 v2 hv2 h01 h02 h12
  (Equiv.swap (3 : Fin 7) (e.symm ⟨v3, hv3⟩)).trans e

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
private theorem finsetEquivFinAtZeroOneTwo_zero (S : Finset V)
    (hCard : S.card = 7) (v0 : V) (hv0 : v0 ∈ S)
    (v1 : V) (hv1 : v1 ∈ S) (v2 : V) (hv2 : v2 ∈ S)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2) :
    (FiveZExactLabels.finsetEquivFinAtZeroOneTwo S (by omega) hCard
      v0 hv0 v1 hv1 v2 hv2 h01 h02 h12 0).1 = v0 := by
  classical
  let e0 := FiveZExactLabels.finsetEquivFinAtZero S (by omega) hCard v0 hv0
  let e1 := FiveZExactLabels.finsetEquivFinAtZeroOne S (by omega) hCard
    v0 hv0 v1 hv1 h01
  have he10 : (e1 0).1 = v0 := by
    have hi1 : e0.symm ⟨v1, hv1⟩ ≠ (0 : Fin 7) := by
      intro hi
      have heq := congrArg (fun q => (e0 q).1) hi
      simp only [Equiv.apply_symm_apply] at heq
      exact h01 ((FiveZExactLabels.finsetEquivFinAtZero_zero S (by omega)
        hCard v0 hv0).symm.trans heq.symm)
    change (e0 ((Equiv.swap 1 (e0.symm ⟨v1, hv1⟩)) 0)).1 = v0
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi1 h.symm)]
    exact FiveZExactLabels.finsetEquivFinAtZero_zero S (by omega) hCard v0 hv0
  have hi2 : e1.symm ⟨v2, hv2⟩ ≠ (0 : Fin 7) := by
    intro hi
    have heq := congrArg (fun q => (e1 q).1) hi
    simp only [Equiv.apply_symm_apply] at heq
    exact h02 (he10.symm.trans heq.symm)
  change (e1 ((Equiv.swap 2 (e1.symm ⟨v2, hv2⟩)) 0)).1 = v0
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi2 h.symm)]
  exact he10

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
private theorem finsetEquivFinAtZeroOne_zero (S : Finset V)
    (hCard : S.card = 7) (v0 : V) (hv0 : v0 ∈ S)
    (v1 : V) (hv1 : v1 ∈ S) (h01 : v0 ≠ v1) :
    (FiveZExactLabels.finsetEquivFinAtZeroOne S (by omega) hCard
      v0 hv0 v1 hv1 h01 0).1 = v0 := by
  classical
  let e0 := FiveZExactLabels.finsetEquivFinAtZero S (by omega) hCard v0 hv0
  have hi1 : e0.symm ⟨v1, hv1⟩ ≠ (0 : Fin 7) := by
    intro hi
    have heq := congrArg (fun q => (e0 q).1) hi
    simp only [Equiv.apply_symm_apply] at heq
    exact h01 ((FiveZExactLabels.finsetEquivFinAtZero_zero S (by omega)
      hCard v0 hv0).symm.trans heq.symm)
  change (e0 ((Equiv.swap 1 (e0.symm ⟨v1, hv1⟩)) 0)).1 = v0
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi1 h.symm)]
  exact FiveZExactLabels.finsetEquivFinAtZero_zero S (by omega) hCard v0 hv0

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
private theorem finsetEquivFinAtZeroOneTwo_one (S : Finset V)
    (hCard : S.card = 7) (v0 : V) (hv0 : v0 ∈ S)
    (v1 : V) (hv1 : v1 ∈ S) (v2 : V) (hv2 : v2 ∈ S)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2) :
    (FiveZExactLabels.finsetEquivFinAtZeroOneTwo S (by omega) hCard
      v0 hv0 v1 hv1 v2 hv2 h01 h02 h12 1).1 = v1 := by
  classical
  let e1 := FiveZExactLabels.finsetEquivFinAtZeroOne S (by omega) hCard
    v0 hv0 v1 hv1 h01
  have he11 : (e1 1).1 = v1 :=
    FiveZExactLabels.finsetEquivFinAtZeroOne_one S (by omega) hCard
      v0 hv0 v1 hv1 h01
  have hi2 : e1.symm ⟨v2, hv2⟩ ≠ (1 : Fin 7) := by
    intro hi
    have heq := congrArg (fun q => (e1 q).1) hi
    simp only [Equiv.apply_symm_apply] at heq
    exact h12 (he11.symm.trans heq.symm)
  change (e1 ((Equiv.swap 2 (e1.symm ⟨v2, hv2⟩)) 1)).1 = v1
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi2 h.symm)]
  exact he11

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
private theorem finsetEquivFinAtZeroOneTwoThree_apply (S : Finset V)
    (hCard : S.card = 7) (v0 : V) (hv0 : v0 ∈ S)
    (v1 : V) (hv1 : v1 ∈ S) (v2 : V) (hv2 : v2 ∈ S)
    (v3 : V) (hv3 : v3 ∈ S)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (i : Fin 4) :
    (finsetEquivFinAtZeroOneTwoThree S hCard v0 hv0 v1 hv1 v2 hv2 v3 hv3
      h01 h02 h03 h12 h13 h23 ⟨i.val, by omega⟩).1 =
      if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2 else v3 := by
  classical
  let e := FiveZExactLabels.finsetEquivFinAtZeroOneTwo S (by omega) hCard
    v0 hv0 v1 hv1 v2 hv2 h01 h02 h12
  have he0 : (e 0).1 = v0 := finsetEquivFinAtZeroOneTwo_zero S hCard
    v0 hv0 v1 hv1 v2 hv2 h01 h02 h12
  have he1 : (e 1).1 = v1 := finsetEquivFinAtZeroOneTwo_one S hCard
    v0 hv0 v1 hv1 v2 hv2 h01 h02 h12
  have he2 : (e 2).1 = v2 :=
    FiveZExactLabels.finsetEquivFinAtZeroOneTwo_two S (by omega) hCard
      v0 hv0 v1 hv1 v2 hv2 h01 h02 h12
  have hi0 : e.symm ⟨v3, hv3⟩ ≠ (0 : Fin 7) := by
    intro hi
    have heq := congrArg (fun q => (e q).1) hi
    simp only [Equiv.apply_symm_apply] at heq
    exact h03 (he0.symm.trans heq.symm)
  have hi1 : e.symm ⟨v3, hv3⟩ ≠ (1 : Fin 7) := by
    intro hi
    have heq := congrArg (fun q => (e q).1) hi
    simp only [Equiv.apply_symm_apply] at heq
    exact h13 (he1.symm.trans heq.symm)
  have hi2 : e.symm ⟨v3, hv3⟩ ≠ (2 : Fin 7) := by
    intro hi
    have heq := congrArg (fun q => (e q).1) hi
    simp only [Equiv.apply_symm_apply] at heq
    exact h23 (he2.symm.trans heq.symm)
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hiCases with rfl | rfl | rfl | rfl
  · change (e ((Equiv.swap 3 (e.symm ⟨v3, hv3⟩)) 0)).1 = v0
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi0 h.symm)]
    exact he0
  · change (e ((Equiv.swap 3 (e.symm ⟨v3, hv3⟩)) 1)).1 = v1
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi1 h.symm)]
    exact he1
  · change (e ((Equiv.swap 3 (e.symm ⟨v3, hv3⟩)) 2)).1 = v2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hi2 h.symm)]
    exact he2
  · simp [finsetEquivFinAtZeroOneTwoThree]

set_option maxHeartbeats 3000000 in
theorem hCode_ule_hLabel (C : G.LocalConfiguration)
    (hHCard : C.H.card = 4) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X})
    (p : Fin 7 → V) (W : Finset V) (a : Fin 8 → V) (z : Fin 4 → V)
    (w : Fin 7 → V) {i j : Fin 3} (hij : i ≤ j)
    (hSame : (sortedX G p W (fun q => (eX q).1) i ∈ W) =
      (sortedX G p W (fun q => (eX q).1) j ∈ W)) :
    (FourZExactSeven.hCode (coreBits G.Adj p
      (fun q => (hLabelEquiv G C hHCard eA1 eX p W q).1) a z w)
      (j.val + 1)).ule
      (FourZExactSeven.hCode (coreBits G.Adj p
        (fun q => (hLabelEquiv G C hHCard eA1 eX p W q).1) a z w)
        (i.val + 1)) = true := by
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hCode_coreBits G p
    (fun q => (hLabelEquiv G C hHCard eA1 eX p W q).1) a z w
      (j.val + 1) (by omega),
    hCode_coreBits G p
    (fun q => (hLabelEquiv G C hHCard eA1 eX p W q).1) a z w
      (i.val + 1) (by omega)]
  simp only [show (⟨j.val + 1, by omega⟩ : Fin 4) = Fin.succ j by rfl,
    show (⟨i.val + 1, by omega⟩ : Fin 4) = Fin.succ i by rfl,
    hLabelEquiv_succ]
  exact sortedX_code_anti_of_same_mem G p W (fun q => (eX q).1) hij hSame

set_option maxHeartbeats 3000000 in
structure Data (C : G.LocalConfiguration) (p : Fin 7 ≃ {v : V // v ∈ C.P}) where
  overlap : OverlapType
  h : Fin 4 ≃ {v : V // v ∈ C.H}
  w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C}
  h0A1 : (h 0).1 ∈ C.A1
  h1X : (h 1).1 ∈ C.X
  h2X : (h 2).1 ∈ C.X
  h3X : (h 3).1 ∈ C.X
  hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
    (wMatchesH overlap wi hi = true ↔
      (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1)
  hHInW : ∀ hi : Nat, (hhi : hi < 4) →
    ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
      hInW overlap hi = true)
  orderH : ∀ (a : Fin 8 → V) (z : Fin 4 → V),
    orderedH overlap (coreBits G.Adj (fun i => (p i).1)
      (fun i => (h i).1) a z (fun i => (w i).1)) = true

set_option linter.flexible false in
set_option maxHeartbeats 3000000 in
/-- Every exact-seven external union admits one of the eight canonical
overlap labels, with the `X` blocks simultaneously sorted by `hCode`. -/
theorem exists_data (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (hA1Card : C.A1.card = 1) (hXCard : C.X.card = 3)
    (hHCard : C.H.card = 4)
    (hWCard : (FourZExactSevenGraphBridge.zExternalUnion G C).card = 7) :
    Nonempty (Data G C p) := by
  let W := FourZExactSevenGraphBridge.zExternalUnion G C
  let eA1 : Fin 1 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eX : Fin 3 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let h := hLabelEquiv G C hHCard eA1 eX (fun i => (p i).1) W
  let n := (W ∩ C.X).card
  have hnLe : n ≤ 3 := by
    exact (Finset.card_le_card Finset.inter_subset_right).trans_eq hXCard
  have hh0 : (h 0).1 = (eA1 0).1 := by simp [h]
  have hh1 : (h 1).1 = sortedX G (fun i => (p i).1) W
      (fun i => (eX i).1) 0 := by
    change (hLabelEquiv G C hHCard eA1 eX (fun i => (p i).1) W
      (Fin.succ 0)).1 = _
    exact hLabelEquiv_succ G C hHCard eA1 eX (fun i => (p i).1) W 0
  have hh2 : (h 2).1 = sortedX G (fun i => (p i).1) W
      (fun i => (eX i).1) 1 := by
    change (hLabelEquiv G C hHCard eA1 eX (fun i => (p i).1) W
      (Fin.succ 1)).1 = _
    exact hLabelEquiv_succ G C hHCard eA1 eX (fun i => (p i).1) W 1
  have hh3 : (h 3).1 = sortedX G (fun i => (p i).1) W
      (fun i => (eX i).1) 2 := by
    change (hLabelEquiv G C hHCard eA1 eX (fun i => (p i).1) W
      (Fin.succ 2)).1 = _
    exact hLabelEquiv_succ G C hHCard eA1 eX (fun i => (p i).1) W 2
  have h0A1 : (h 0).1 ∈ C.A1 := by simp [hh0]
  have h1X : (h 1).1 ∈ C.X := by
    rw [hh1]
    exact (eX (xSortPermutation G (fun i => (p i).1) W
      (fun i => (eX i).1) 0)).2
  have h2X : (h 2).1 ∈ C.X := by
    rw [hh2]
    exact (eX (xSortPermutation G (fun i => (p i).1) W
      (fun i => (eX i).1) 1)).2
  have h3X : (h 3).1 ∈ C.X := by
    rw [hh3]
    exact (eX (xSortPermutation G (fun i => (p i).1) W
      (fun i => (eX i).1) 2)).2
  have hXMem : ∀ i : Fin 3, (h (Fin.succ i)).1 ∈ W ↔ i.val < n := by
    intro i
    simpa [h, n] using hLabel_mem_iff G C hHCard eA1 eX
      (fun q => (p q).1) W i
  have hMem1 : (h 1).1 ∈ W ↔ 0 < n := by simpa using hXMem 0
  have hMem2 : (h 2).1 ∈ W ↔ 1 < n := by simpa using hXMem 1
  have hMem3 : (h 3).1 ∈ W ↔ 2 < n := by simpa using hXMem 2
  have hDistinct01 : (h 0).1 ≠ (h 1).1 := fun heq =>
    Fin.zero_ne_one (h.injective (Subtype.ext heq))
  have hDistinct02 : (h 0).1 ≠ (h 2).1 := fun heq =>
    (by decide : (0 : Fin 4) ≠ 2) (h.injective (Subtype.ext heq))
  have hDistinct03 : (h 0).1 ≠ (h 3).1 := fun heq =>
    (by decide : (0 : Fin 4) ≠ 3) (h.injective (Subtype.ext heq))
  have hDistinct12 : (h 1).1 ≠ (h 2).1 := fun heq =>
    (by decide : (1 : Fin 4) ≠ 2) (h.injective (Subtype.ext heq))
  have hDistinct13 : (h 1).1 ≠ (h 3).1 := fun heq =>
    (by decide : (1 : Fin 4) ≠ 3) (h.injective (Subtype.ext heq))
  have hDistinct23 : (h 2).1 ≠ (h 3).1 := fun heq =>
    (by decide : (2 : Fin 4) ≠ 3) (h.injective (Subtype.ext heq))
  have make (overlap : OverlapType)
      (w : Fin 7 ≃ {v : V // v ∈ W})
      (hMem : ∀ hi : Nat, (hhi : hi < 4) →
        ((h ⟨hi, hhi⟩).1 ∈ W ↔ hInW overlap hi = true))
      (hPrefix : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
        wMatchesH overlap wi hi = true →
          (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1)
      (hOrder : ∀ (a : Fin 8 → V) (z : Fin 4 → V),
        orderedH overlap (coreBits G.Adj (fun i => (p i).1)
          (fun i => (h i).1) a z (fun i => (w i).1)) = true) :
      Nonempty (Data G C p) := by
    refine ⟨⟨overlap, h, w, h0A1, h1X, h2X, h3X, ?_, ?_, hOrder⟩⟩
    · exact hWH_of_mem_and_prefix G W overlap h w hMem hPrefix
    · simpa [W] using hMem
  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hnCases with hn | hn | hn | hn
  · by_cases ha : (h 0).1 ∈ W
    · let w := FiveZExactLabels.finsetEquivFinAtZero W (by omega) hWCard
        (h 0).1 ha
      apply make .aOne w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with ⟨rfl, rfl⟩
        exact FiveZExactLabels.finsetEquivFinAtZero_zero W (by omega)
          hWCard (h 0).1 ha
      · intro a z
        simp only [FourZExactSeven.orderedH]
        rw [Bool.and_eq_true]
        constructor
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 0) (j := 1) (by decide)
            (by rw [← hh1, ← hh2]; simp [hMem1, hMem2, hn])
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 1) (j := 2) (by decide)
            (by rw [← hh2, ← hh3]; simp [hMem2, hMem3, hn])
    · let w : Fin 7 ≃ {v : V // v ∈ W} := finsetEquivFin W hWCard
      apply make .none w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
      · intro a z
        simp only [FourZExactSeven.orderedH]
        rw [Bool.and_eq_true]
        constructor
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 0) (j := 1) (by decide)
            (by rw [← hh1, ← hh2]; simp [hMem1, hMem2, hn])
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 1) (j := 2) (by decide)
            (by rw [← hh2, ← hh3]; simp [hMem2, hMem3, hn])
  · by_cases ha : (h 0).1 ∈ W
    · let w := FiveZExactLabels.finsetEquivFinAtZeroOne W (by omega) hWCard
        (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega)) hDistinct01
      apply make .aXOne w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact finsetEquivFinAtZeroOne_zero W hWCard _ ha _
            ((hXMem 0).2 (by omega)) hDistinct01
        · exact FiveZExactLabels.finsetEquivFinAtZeroOne_one W (by omega)
            hWCard _ ha _ ((hXMem 0).2 (by omega)) hDistinct01
      · intro a z
        simp only [FourZExactSeven.orderedH]
        exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
          W a z (fun i => (w i).1) (i := 1) (j := 2) (by decide)
          (by rw [← hh2, ← hh3]; simp [hMem2, hMem3, hn])
    · let w := FiveZExactLabels.finsetEquivFinAtZero W (by omega) hWCard
        (h 1).1 ((hXMem 0).2 (by omega))
      apply make .xOne w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with ⟨rfl, rfl⟩
        exact FiveZExactLabels.finsetEquivFinAtZero_zero W (by omega)
          hWCard _ ((hXMem 0).2 (by omega))
      · intro a z
        simp only [FourZExactSeven.orderedH]
        exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
          W a z (fun i => (w i).1) (i := 1) (j := 2) (by decide)
          (by rw [← hh2, ← hh3]; simp [hMem2, hMem3, hn])
  · by_cases ha : (h 0).1 ∈ W
    · let w := FiveZExactLabels.finsetEquivFinAtZeroOneTwo W (by omega) hWCard
        (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega))
        (h 2).1 ((hXMem 1).2 (by omega)) hDistinct01 hDistinct02 hDistinct12
      apply make .aXTwo w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with (hcase | hcase) | hcase
        · rcases hcase with ⟨rfl, rfl⟩
          exact finsetEquivFinAtZeroOneTwo_zero W hWCard _ ha _
            ((hXMem 0).2 (by omega)) _ ((hXMem 1).2 (by omega))
            hDistinct01 hDistinct02 hDistinct12
        · rcases hcase with ⟨rfl, rfl⟩
          exact finsetEquivFinAtZeroOneTwo_one W hWCard _ ha _
            ((hXMem 0).2 (by omega)) _ ((hXMem 1).2 (by omega))
            hDistinct01 hDistinct02 hDistinct12
        · rcases hcase with ⟨rfl, rfl⟩
          exact FiveZExactLabels.finsetEquivFinAtZeroOneTwo_two W (by omega)
            hWCard _ ha _ ((hXMem 0).2 (by omega)) _
            ((hXMem 1).2 (by omega)) hDistinct01 hDistinct02 hDistinct12
      · intro a z
        simp only [FourZExactSeven.orderedH]
        exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
          W a z (fun i => (w i).1) (i := 0) (j := 1) (by decide)
          (by rw [← hh1, ← hh2]; simp [hMem1, hMem2, hn])
    · let w := FiveZExactLabels.finsetEquivFinAtZeroOne W (by omega) hWCard
        (h 1).1 ((hXMem 0).2 (by omega)) (h 2).1
        ((hXMem 1).2 (by omega)) hDistinct12
      apply make .xTwo w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact finsetEquivFinAtZeroOne_zero W hWCard _
            ((hXMem 0).2 (by omega)) _ ((hXMem 1).2 (by omega)) hDistinct12
        · exact FiveZExactLabels.finsetEquivFinAtZeroOne_one W (by omega)
            hWCard _ ((hXMem 0).2 (by omega)) _
            ((hXMem 1).2 (by omega)) hDistinct12
      · intro a z
        simp only [FourZExactSeven.orderedH]
        exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
          W a z (fun i => (w i).1) (i := 0) (j := 1) (by decide)
          (by rw [← hh1, ← hh2]; simp [hMem1, hMem2, hn])
  · by_cases ha : (h 0).1 ∈ W
    · let w := finsetEquivFinAtZeroOneTwoThree W hWCard
        (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega))
        (h 2).1 ((hXMem 1).2 (by omega)) (h 3).1
        ((hXMem 2).2 (by omega)) hDistinct01 hDistinct02 hDistinct03
        hDistinct12 hDistinct13 hDistinct23
      apply make .aXThree w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with ((hcase | hcase) | hcase) | hcase
        · rcases hcase with ⟨rfl, rfl⟩
          simpa using finsetEquivFinAtZeroOneTwoThree_apply W hWCard
            (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega))
            (h 2).1 ((hXMem 1).2 (by omega)) (h 3).1
            ((hXMem 2).2 (by omega)) hDistinct01 hDistinct02 hDistinct03
            hDistinct12 hDistinct13 hDistinct23 (0 : Fin 4)
        · rcases hcase with ⟨rfl, rfl⟩
          simpa using finsetEquivFinAtZeroOneTwoThree_apply W hWCard
            (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega))
            (h 2).1 ((hXMem 1).2 (by omega)) (h 3).1
            ((hXMem 2).2 (by omega)) hDistinct01 hDistinct02 hDistinct03
            hDistinct12 hDistinct13 hDistinct23 (1 : Fin 4)
        · rcases hcase with ⟨rfl, rfl⟩
          simpa using finsetEquivFinAtZeroOneTwoThree_apply W hWCard
            (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega))
            (h 2).1 ((hXMem 1).2 (by omega)) (h 3).1
            ((hXMem 2).2 (by omega)) hDistinct01 hDistinct02 hDistinct03
            hDistinct12 hDistinct13 hDistinct23 (2 : Fin 4)
        · rcases hcase with ⟨rfl, rfl⟩
          simpa using finsetEquivFinAtZeroOneTwoThree_apply W hWCard
            (h 0).1 ha (h 1).1 ((hXMem 0).2 (by omega))
            (h 2).1 ((hXMem 1).2 (by omega)) (h 3).1
            ((hXMem 2).2 (by omega)) hDistinct01 hDistinct02 hDistinct03
            hDistinct12 hDistinct13 hDistinct23 (3 : Fin 4)
      · intro a z
        simp only [FourZExactSeven.orderedH]
        rw [Bool.and_eq_true]
        constructor
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 0) (j := 1) (by decide)
            (by rw [← hh1, ← hh2]; simp [hMem1, hMem2, hn])
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 1) (j := 2) (by decide)
            (by rw [← hh2, ← hh3]; simp [hMem2, hMem3, hn])
    · let w := FiveZExactLabels.finsetEquivFinAtZeroOneTwo W (by omega) hWCard
        (h 1).1 ((hXMem 0).2 (by omega)) (h 2).1
        ((hXMem 1).2 (by omega)) (h 3).1 ((hXMem 2).2 (by omega))
        hDistinct12 hDistinct13 hDistinct23
      apply make .xThree w
      · intro hi hhi
        have hiCases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 := by omega
        rcases hiCases with rfl | rfl | rfl | rfl <;>
          simp [hInW, wMatchesH, any, ha, hMem1, hMem2, hMem3, hn]
      · intro wi hi hwi hhi hm
        simp [wMatchesH] at hm
        rcases hm with (hcase | hcase) | hcase
        · rcases hcase with ⟨rfl, rfl⟩
          exact finsetEquivFinAtZeroOneTwo_zero W hWCard _
            ((hXMem 0).2 (by omega)) _ ((hXMem 1).2 (by omega)) _
            ((hXMem 2).2 (by omega)) hDistinct12 hDistinct13 hDistinct23
        · rcases hcase with ⟨rfl, rfl⟩
          exact finsetEquivFinAtZeroOneTwo_one W hWCard _
            ((hXMem 0).2 (by omega)) _ ((hXMem 1).2 (by omega)) _
            ((hXMem 2).2 (by omega)) hDistinct12 hDistinct13 hDistinct23
        · rcases hcase with ⟨rfl, rfl⟩
          exact FiveZExactLabels.finsetEquivFinAtZeroOneTwo_two W (by omega)
            hWCard _ ((hXMem 0).2 (by omega)) _
            ((hXMem 1).2 (by omega)) _ ((hXMem 2).2 (by omega))
            hDistinct12 hDistinct13 hDistinct23
      · intro a z
        simp only [FourZExactSeven.orderedH]
        rw [Bool.and_eq_true]
        constructor
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 0) (j := 1) (by decide)
            (by rw [← hh1, ← hh2]; simp [hMem1, hMem2, hn])
        · exact hCode_ule_hLabel G C hHCard eA1 eX (fun i => (p i).1)
            W a z (fun i => (w i).1) (i := 1) (j := 2) (by decide)
            (by rw [← hh2, ← hh3]; simp [hMem2, hMem3, hn])

end SeymourEight.FourZExactSevenOverlapLabels
