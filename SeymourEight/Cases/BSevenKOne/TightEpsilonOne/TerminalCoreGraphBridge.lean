import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.Terminal
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreBridge
import SeymourEight.Shared.FinsetBridge
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false

/-!
# Graph/finset adapter for the terminal certificate

This file connects ordinary finite graph sets to the labelled relation used
by `TerminalCoreBridge`.
-/

namespace SeymourEight.TerminalCoreGraphBridge

open RawFinalBranch Shared TerminalAlphaBeta TerminalCore TerminalCoreBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Relabel a seven-element finset so that a prescribed member has label zero. -/
noncomputable def finsetEquivFinAtZero (S : Finset V) (hCard : S.card = 7)
    (v : V) (hv : v ∈ S) : Fin 7 ≃ {w : V // w ∈ S} :=
  let e := finsetEquivFin S hCard
  (Equiv.swap 0 (e.symm ⟨v, hv⟩)).trans e

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZero_zero (S : Finset V) (hCard : S.card = 7)
    (v : V) (hv : v ∈ S) :
    (finsetEquivFinAtZero S hCard v hv 0).1 = v := by
  simp [finsetEquivFinAtZero]

omit [Fintype V] [DecidableEq V] in
/--
If exactly six of seven vertices point to the root, label the unique exception
by zero and all six root-neighbors by the remaining labels.
-/
theorem exists_rootLabelEquiv (P : Finset V) (s : V) (hPCard : P.card = 7)
    (hRootCount : ∑ p ∈ P, epsilonAt G p s = 6) :
    ∃ eP : Fin 7 ≃ {v : V // v ∈ P},
      ∀ i : Nat, (hi : i < 7) →
        epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1 := by
  classical
  let rootNeighbors := P.filter fun p ↦ G.Adj p s
  have hRootCard : rootNeighbors.card = 6 := by
    change (P.filter fun p ↦ G.Adj p s).card = 6
    simpa [epsilonAt] using hRootCount
  have hMissingCard : (P \ rootNeighbors).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hPCard, hRootCard]
  obtain ⟨p0, hMissingEq⟩ := Finset.card_eq_one.mp hMissingCard
  have hp0Missing : p0 ∈ P \ rootNeighbors := by simp [hMissingEq]
  have hp0P : p0 ∈ P := (Finset.mem_sdiff.mp hp0Missing).1
  have hp0NotRoot : ¬G.Adj p0 s := by
    have hp0NotMem := (Finset.mem_sdiff.mp hp0Missing).2
    simpa [rootNeighbors, hp0P] using hp0NotMem
  let eP := finsetEquivFinAtZero P hPCard p0 hp0P
  refine ⟨eP, ?_⟩
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp [eP, epsilonAt, hp0NotRoot]
  · have hLabelP : (eP ⟨i, hi⟩).1 ∈ P := (eP ⟨i, hi⟩).2
    have hLabelNe : (eP ⟨i, hi⟩).1 ≠ p0 := by
      intro hEq
      have hIndex : (⟨i, hi⟩ : Fin 7) = 0 := by
        apply eP.injective
        apply Subtype.ext
        simpa [eP] using hEq
      exact hi0 (Fin.ext_iff.mp hIndex)
    have hAdj : G.Adj (eP ⟨i, hi⟩).1 s := by
      by_contra hNotAdj
      have hMissing : (eP ⟨i, hi⟩).1 ∈ P \ rootNeighbors := by
        apply Finset.mem_sdiff.mpr
        refine ⟨hLabelP, ?_⟩
        simp [rootNeighbors, hLabelP, hNotAdj]
      have hEq : (eP ⟨i, hi⟩).1 = p0 := by
        simpa [hMissingEq] using hMissing
      exact hLabelNe hEq
    simp [epsilonAt, hi0, hAdj]

/-- Regard the sorted relabelling of a seven-element finset as an equivalence. -/
noncomputable def sortedFinsetEquiv (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P}) :
    Fin 7 ≃ {v : V // v ∈ P} :=
  (extendTailPerm (tailSortPermutation degree hCount
    (fun i ↦ (eP i).1))).trans eP

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem sortedFinsetEquiv_coe (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P}) (i : Fin 7) :
    (sortedFinsetEquiv degree hCount P eP i).1 =
      sortedP degree hCount (fun j ↦ (eP j).1) i := rfl

omit [Fintype V] [DecidableEq V] in
/-- Sorting the six tail labels preserves the exceptional root label at zero. -/
theorem sortedFinsetEquiv_root (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P}) (s : V)
    (hRoot : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1) :
    ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (sortedFinsetEquiv degree hCount P eP ⟨i, hi⟩).1 s =
        if i = 0 then 0 else 1 := by
  intro i hi
  let ePS := sortedFinsetEquiv degree hCount P eP
  by_cases hi0 : i = 0
  · subst i
    change epsilonAt G (ePS 0).1 s = 0
    have hBase := hRoot 0 (by omega)
    simpa [ePS, sortedFinsetEquiv, sortedP] using hBase
  · let j : Fin 7 := eP.symm (ePS ⟨i, hi⟩)
    have hj0 : j ≠ 0 := by
      intro hj
      have hValues : ePS ⟨i, hi⟩ = ePS 0 := by
        calc
          ePS ⟨i, hi⟩ = eP j := by simp [j]
          _ = eP 0 := by rw [hj]
          _ = ePS 0 := by
            apply Subtype.ext
            simp [ePS, sortedFinsetEquiv]
      have hIndices := ePS.injective hValues
      exact hi0 (Fin.ext_iff.mp hIndices)
    have hj0Nat : (j : Nat) ≠ 0 := by
      intro hj
      exact hj0 (Fin.ext hj)
    have hJRoot := hRoot j.val j.isLt
    rw [if_neg hj0Nat] at hJRoot
    have hValue : (eP j).1 = (ePS ⟨i, hi⟩).1 := by
      simp [j]
    rw [← hValue]
    simpa [hi0] using hJRoot

/-- The five-bit certificate count has the expected natural-number value. -/
theorem toNat_sumFive (f : Nat → Bool) :
    (sumFive f).toNat =
      (if f 0 then 1 else 0) + (if f 1 then 1 else 0) +
      (if f 2 then 1 else 0) + (if f 3 then 1 else 0) +
      (if f 4 then 1 else 0) := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;>
    cases h3 : f 3 <;> cases h4 : f 4 <;>
    simp [sumFive, bitCount, h0, h1, h2, h3, h4]

/-- The seven-bit certificate count has the expected natural-number value. -/
theorem toNat_sumSeven (f : Nat → Bool) :
    (sumSeven f).toNat =
      (if f 0 then 1 else 0) + (if f 1 then 1 else 0) +
      (if f 2 then 1 else 0) + (if f 3 then 1 else 0) +
      (if f 4 then 1 else 0) + (if f 5 then 1 else 0) +
      (if f 6 then 1 else 0) := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;>
    cases h3 : f 3 <;> cases h4 : f 4 <;> cases h5 : f 5 <;>
    cases h6 : f 6 <;>
    simp [sumSeven, bitCount, h0, h1, h2, h3, h4, h5, h6]

/-- `sumFive` is the ordinary sum of its five Boolean indicators. -/
theorem toNat_sumFive_eq_fin_sum (f : Nat → Bool) :
    (sumFive f).toNat = ∑ i : Fin 5, if f i then 1 else 0 := by
  rw [toNat_sumFive]
  simp only [Fin.sum_univ_succ]
  simp [Nat.add_assoc]

/-- `sumSeven` is the ordinary sum of its seven Boolean indicators. -/
theorem toNat_sumSeven_eq_fin_sum (f : Nat → Bool) :
    (sumSeven f).toNat = ∑ i : Fin 7, if f i then 1 else 0 := by
  rw [toNat_sumSeven]
  simp only [Fin.sum_univ_succ]
  simp [Nat.add_assoc]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_fin_of_anySeven (f : Nat → Bool) (h : anySeven f = true) :
    ∃ i : Fin 7, f i = true := by
  simp only [anySeven, Bool.or_eq_true] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨5, h⟩
  · exact ⟨6, h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_fin_of_anyFive (f : Nat → Bool) (h : anyFive f = true) :
    ∃ i : Fin 5, f i = true := by
  simp only [anyFive, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h)
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩

/-- A seven-term byte sum agrees with the natural sum when no overflow occurs. -/
theorem toNat_sumCountSeven (f : Nat → BitVec 8)
    (hNoOverflow :
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat +
        (f 4).toNat + (f 5).toNat + (f 6).toNat < 256) :
    (sumCountSeven f).toNat =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat +
        (f 4).toNat + (f 5).toNat + (f 6).toNat := by
  simp only [sumCountSeven, BitVec.toNat_add, Nat.reducePow]
  omega

/-- A five-term byte sum agrees with the natural sum when no overflow occurs. -/
theorem toNat_sumCountFive (f : Nat → BitVec 8)
    (hNoOverflow :
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat +
        (f 4).toNat < 256) :
    (sumCountFive f).toNat =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat +
        (f 4).toNat := by
  simp only [sumCountFive, BitVec.toNat_add, Nat.reducePow]
  omega

omit [Fintype V] [DecidableEq V] in
/-- A labelled five-column incidence row is the corresponding finset count. -/
theorem labelledPToHCount_toNat (PLabel : Fin 7 → V)
    (H : Finset V) (eH : Fin 5 ≃ {v : V // v ∈ H}) (i : Nat) :
    (labelledPToHCount G.Adj PLabel (fun j ↦ (eH j).1) i).toNat =
      directCount G H (pAt PLabel i) := by
  rw [labelledPToHCount, toNat_sumFive_eq_fin_sum]
  symm
  apply directCount_eq_sum_bool G H eH
  intro j
  simp [labelledPToH, hAt_of_lt]

omit [Fintype V] [DecidableEq V] in
/-- A labelled seven-column `P→P` row is the corresponding finset count. -/
theorem labelledPOutCount_toNat (P : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P}) (i : Nat) :
    (labelledPOutCount G.Adj (fun j ↦ (eP j).1) i).toNat =
      directCount G P (pAt (fun j ↦ (eP j).1) i) := by
  rw [labelledPOutCount, toNat_sumSeven_eq_fin_sum]
  symm
  apply directCount_eq_sum_bool G P eP
  intro j
  simp [labelledPArc, pAt_of_lt]

omit [Fintype V] [DecidableEq V] in
/-- A labelled seven-column `H→P` row is the corresponding finset count. -/
theorem labelledHToPCount_toNat (P : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P}) (HLabel : Fin 5 → V) (i : Nat) :
    (labelledHToPCount G.Adj (fun j ↦ (eP j).1) HLabel i).toNat =
      directCount G P (hAt HLabel i) := by
  rw [labelledHToPCount, toNat_sumSeven_eq_fin_sum]
  symm
  apply directCount_eq_sum_bool G P eP
  intro j
  simp [labelledHToP, pAt_of_lt]

omit [Fintype V] in
/-- Every labelled strict second neighbor is counted by the graph-side `qCount`. -/
theorem labelledSecond_true_mem (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (i j : Nat) (hi : i < 7) (hj : j < 7)
    (hSecond :
      (decide (j ≠ i) &&
        !labelledPArc G.Adj (fun k ↦ (eP k).1) i j &&
        labelledReachedViaPOrH G.Adj (fun k ↦ (eP k).1)
          (fun k ↦ (eH k).1) i j) = true) :
    (eP ⟨j, hj⟩).1 ∈ secondNeighborsThrough G P (P ∪ H) (eP ⟨i, hi⟩).1 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hji, hNotArcBool⟩, hReach⟩
  have hNotArc : ¬G.Adj (eP ⟨i, hi⟩).1 (eP ⟨j, hj⟩).1 := by
    simp only [labelledPArc] at hNotArcBool
    rw [pAt_of_lt (fun k ↦ (eP k).1) i hi,
      pAt_of_lt (fun k ↦ (eP k).1) j hj] at hNotArcBool
    have hFalse := Bool.eq_false_of_not_eq_true' hNotArcBool
    simpa only [decide_eq_false_iff_not] using hFalse
  have hTargetNe : (eP ⟨j, hj⟩).1 ≠ (eP ⟨i, hi⟩).1 := by
    intro hEq
    have hFinEq : (⟨j, hj⟩ : Fin 7) = ⟨i, hi⟩ := by
      apply eP.injective
      exact Subtype.ext hEq
    exact hji (Fin.ext_iff.mp hFinEq)
  have hWitness : ∃ w ∈ P ∪ H,
      G.Adj (eP ⟨i, hi⟩).1 w ∧ G.Adj w (eP ⟨j, hj⟩).1 := by
    simp only [labelledReachedViaPOrH, Bool.or_eq_true] at hReach
    rcases hReach with hViaP | hViaH
    · obtain ⟨middle, hMiddle⟩ := exists_fin_of_anySeven _ hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hMiddle
      rcases hMiddle with ⟨⟨⟨_mi, _mj⟩, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (eP ⟨i, hi⟩).1 (eP middle).1 := by
        simp only [labelledPArc, decide_eq_true_eq] at hFirstBool
        rw [pAt_of_lt (fun k ↦ (eP k).1) i hi,
          pAt_of_lt (fun k ↦ (eP k).1) middle middle.isLt] at hFirstBool
        exact hFirstBool
      have hSecond' : G.Adj (eP middle).1 (eP ⟨j, hj⟩).1 := by
        simp only [labelledPArc, decide_eq_true_eq] at hSecondBool
        rw [pAt_of_lt (fun k ↦ (eP k).1) middle middle.isLt,
          pAt_of_lt (fun k ↦ (eP k).1) j hj] at hSecondBool
        exact hSecondBool
      exact ⟨(eP middle).1, Finset.mem_union_left H (eP middle).2,
        hFirst, hSecond'⟩
    · obtain ⟨middle, hMiddle⟩ := exists_fin_of_anyFive _ hViaH
      simp only [Bool.and_eq_true] at hMiddle
      rcases hMiddle with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (eP ⟨i, hi⟩).1 (eH middle).1 := by
        simp only [labelledPToH, decide_eq_true_eq] at hFirstBool
        rw [pAt_of_lt (fun k ↦ (eP k).1) i hi,
          hAt_of_lt (fun k ↦ (eH k).1) middle middle.isLt] at hFirstBool
        exact hFirstBool
      have hSecond' : G.Adj (eH middle).1 (eP ⟨j, hj⟩).1 := by
        simp only [labelledHToP, decide_eq_true_eq] at hSecondBool
        rw [hAt_of_lt (fun k ↦ (eH k).1) middle middle.isLt,
          pAt_of_lt (fun k ↦ (eP k).1) j hj] at hSecondBool
        exact hSecondBool
      exact ⟨(eH middle).1, Finset.mem_union_right P (eH middle).2,
        hFirst, hSecond'⟩
  apply Finset.mem_filter.mpr
  exact ⟨(eP ⟨j, hj⟩).2, hNotArc, hTargetNe, hWitness⟩

omit [Fintype V] in
/-- The certificate's labelled second-neighbor count is bounded by `qCount`. -/
theorem labelledSecondPCount_toNat_le_qCount (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H}) (i : Nat) (hi : i < 7) :
    (labelledSecondPCount G.Adj (fun k ↦ (eP k).1)
      (fun k ↦ (eH k).1) i).toNat ≤ qCount G P H (eP ⟨i, hi⟩).1 := by
  rw [labelledSecondPCount, toNat_sumSeven_eq_fin_sum]
  unfold qCount secondNeighborsThrough
  rw [filterCard_eq_sum_fin P eP]
  apply Finset.sum_le_sum
  intro j _hj
  let secondBit := decide (j.val ≠ i) &&
    !labelledPArc G.Adj (fun k ↦ (eP k).1) i j.val &&
    labelledReachedViaPOrH G.Adj (fun k ↦ (eP k).1)
      (fun k ↦ (eH k).1) i j.val
  let Q : V → Prop := fun v ↦
    ¬G.Adj (eP ⟨i, hi⟩).1 v ∧ v ≠ (eP ⟨i, hi⟩).1 ∧
      ∃ w ∈ P ∪ H, G.Adj (eP ⟨i, hi⟩).1 w ∧ G.Adj w v
  change (if secondBit then 1 else 0) ≤ if Q (eP j).1 then 1 else 0
  by_cases hBit : secondBit = true
  · have hMem := labelledSecond_true_mem G P H eP eH i j.val hi j.isLt hBit
    have hQ : Q (eP j).1 := by
      exact (Finset.mem_filter.mp hMem).2
    simp [hBit, hQ]
  · have hFalse : secondBit = false := Bool.eq_false_of_not_eq_true hBit
    simp [hFalse]

omit [Fintype V] in
/-- The graph-level counting identity implies the certificate's labelled
Boolean test. -/
theorem labelledEquation18At_true_of_graph (P H : Finset V) (s : V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H}) (i : Nat) (hi : i < 7)
    (hRoot : epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1)
    (hEquation18 : qCount G P H (eP ⟨i, hi⟩).1 + 7 ≤
      directCount G P (eP ⟨i, hi⟩).1 +
        2 * directCount G H (eP ⟨i, hi⟩).1 +
          2 * epsilonAt G (eP ⟨i, hi⟩).1 s) :
    labelledEquation18At G.Adj (fun k ↦ (eP k).1)
      (fun k ↦ (eH k).1) i = true := by
  have hPCard : P.card = 7 := by
    simpa using (Fintype.card_congr eP).symm
  have hHCard : H.card = 5 := by
    simpa using (Fintype.card_congr eH).symm
  have hPCountLe : directCount G P (eP ⟨i, hi⟩).1 ≤ 7 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHCountLe : directCount G H (eP ⟨i, hi⟩).1 ≤ 5 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hQLe : qCount G P H (eP ⟨i, hi⟩).1 ≤ 7 := by
    unfold qCount secondNeighborsThrough
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hSecondLe := labelledSecondPCount_toNat_le_qCount G P H eP eH i hi
  have hPCount :
      (labelledPOutCount G.Adj (fun k ↦ (eP k).1) i).toNat =
        directCount G P (eP ⟨i, hi⟩).1 := by
    have h := labelledPOutCount_toNat G P eP i
    rw [pAt_of_lt (fun k ↦ (eP k).1) i hi] at h
    exact h
  have hHCount :
      (labelledPToHCount G.Adj (fun k ↦ (eP k).1)
        (fun k ↦ (eH k).1) i).toNat = directCount G H (eP ⟨i, hi⟩).1 := by
    have h := labelledPToHCount_toNat G (fun k ↦ (eP k).1) H eH i
    rw [pAt_of_lt (fun k ↦ (eP k).1) i hi] at h
    exact h
  have hZero : (0 : BitVec 8).toNat = 0 := by decide
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hSeven : (7 : BitVec 8).toNat = 7 := by decide
  simp only [labelledEquation18At, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_mul, Nat.reducePow, hPCount, hHCount,
    hTwo, hSeven]
  by_cases hi0 : i = 0
  · subst i
    have hRootZero : epsilonAt G (eP ⟨0, hi⟩).1 s = 0 := by
      simpa using hRoot
    simp only [if_pos]
    omega
  · have hRootOne : epsilonAt G (eP ⟨i, hi⟩).1 s = 1 := by
      simpa [hi0] using hRoot
    simp only [hi0, if_false]
    omega

omit [Fintype V] [DecidableEq V] in
/-- A maximal `7·2` edge count forces every arc from `P` to `Z`. -/
theorem all_P_to_Z_of_edgeCount_fourteen (P Z : Finset V)
    (hPCard : P.card = 7) (hZCard : Z.card = 2)
    (hEdges : edgeCount G P Z = 14) :
    ∀ p ∈ P, ∀ z ∈ Z, G.Adj p z := by
  classical
  have hDirectLe : ∀ p ∈ P, directCount G Z p ≤ 2 := by
    intro p _hp
    exact (Finset.card_le_card
      (Finset.filter_subset (p := G.Adj p) Z)).trans_eq hZCard
  have hDirectEq : ∀ p ∈ P, directCount G Z p = 2 := by
    intro p hp
    apply Nat.le_antisymm (hDirectLe p hp)
    by_contra hNot
    have hStrict : directCount G Z p < 2 := by omega
    have hSumStrict : (∑ q ∈ P, directCount G Z q) < ∑ _q ∈ P, 2 := by
      apply Finset.sum_lt_sum hDirectLe
      exact ⟨p, hp, hStrict⟩
    unfold edgeCount at hEdges
    simp [hEdges, hPCard] at hSumStrict
  intro p hp z hz
  have hFilterEq : CertificateBridge.internalFirstNeighbors G Z p = Z := by
    apply Finset.eq_of_subset_of_card_le
      (Finset.filter_subset (p := G.Adj p) Z)
    have hEq := hDirectEq p hp
    unfold directCount CertificateBridge.internalFirstNeighbors at hEq
    omega
  have hzFilter : z ∈ CertificateBridge.internalFirstNeighbors G Z p := by
    rw [hFilterEq]
    exact hz
  exact (Finset.mem_filter.mp hzFilter).2

/-- Pointwise local degree accounting from full `P→Z` and captured outgoing arcs. -/
theorem outdegree_eq_local_counts (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hZCard : C.Z.card = 2)
    (hPToZ : ∀ p ∈ C.P, ∀ z ∈ C.Z, G.Adj p z)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P)
    (p : V) (hp : p ∈ C.P) :
    G.outdegree p = 2 + epsilonAt G p C.s +
      directCount G C.H p + directCount G C.P p := by
  have hOutEq : G.outNeighborFinset p =
      C.Z ∪ FinalBranch.rootArcFinset G C p ∪
        CertificateBridge.internalFirstNeighbors G C.H p ∪
          CertificateBridge.internalFirstNeighbors G C.P p := by
    ext v
    constructor
    · intro hvOut
      have hvCaptured := hCaptured p hp hvOut
      have hpv := (Digraph.mem_outNeighborFinset (G := G)).mp hvOut
      simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured ⊢
      rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
      · exact Or.inl (Or.inl (Or.inl hvZ))
      · subst v
        exact Or.inl (Or.inl (Or.inr (by
          simp [FinalBranch.rootArcFinset, hpv])))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hvH, hpv⟩))
      · exact Or.inr (Finset.mem_filter.mpr ⟨hvP, hpv⟩)
    · intro hv
      apply (Digraph.mem_outNeighborFinset (G := G)).mpr
      simp only [Finset.mem_union] at hv
      rcases hv with ((hvZ | hvRoot) | hvH) | hvP
      · exact hPToZ p hp v hvZ
      · by_cases hps : G.Adj p C.s
        · have hvEq : v = C.s := by
            simpa [FinalBranch.rootArcFinset, hps] using hvRoot
          simpa [hvEq] using hps
        · simp [FinalBranch.rootArcFinset, hps] at hvRoot
      · exact (Finset.mem_filter.mp hvH).2
      · exact (Finset.mem_filter.mp hvP).2
  have hZRoot : Disjoint C.Z (FinalBranch.rootArcFinset G C p) := by
    rw [Finset.disjoint_left]
    intro v hvZ hvRoot
    by_cases hps : G.Adj p C.s
    · have hvEq : v = C.s := by
        simpa [FinalBranch.rootArcFinset, hps] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hvZ
    · simp [FinalBranch.rootArcFinset, hps] at hvRoot
  have hZRootH : Disjoint
      (C.Z ∪ FinalBranch.rootArcFinset G C p)
      (CertificateBridge.internalFirstNeighbors G C.H p) := by
    rw [Finset.disjoint_left]
    intro v hvZR hvH
    rcases Finset.mem_union.mp hvZR with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
        (Finset.mem_filter.mp hvH).1
    · by_cases hps : G.Adj p C.s
      · have hvEq : v = C.s := by
          simpa [FinalBranch.rootArcFinset, hps] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1
          (Finset.mem_filter.mp hvH).1
      · simp [FinalBranch.rootArcFinset, hps] at hvRoot
  have hAllP : Disjoint
      (C.Z ∪ FinalBranch.rootArcFinset G C p ∪
        CertificateBridge.internalFirstNeighbors G C.H p)
      (CertificateBridge.internalFirstNeighbors G C.P p) := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvP
    have hvP' := (Finset.mem_filter.mp hvP).1
    rcases Finset.mem_union.mp hvLeft with hvZR | hvH
    · rcases Finset.mem_union.mp hvZR with hvZ | hvRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP'
      · by_cases hps : G.Adj p C.s
        · have hvEq : v = C.s := by
            simpa [FinalBranch.rootArcFinset, hps] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP'
        · simp [FinalBranch.rootArcFinset, hps] at hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 hvP'
  unfold Digraph.outdegree directCount
  rw [hOutEq, Finset.card_union_of_disjoint hAllP,
    Finset.card_union_of_disjoint hZRootH,
    Finset.card_union_of_disjoint hZRoot, hZCard,
    FinalBranch.card_rootArcFinset]

/-- The `W`-neighbor bound needs only captured outgoing arcs and disjointness. -/
theorem direct_W_bound_of_captured (C : G.LocalConfiguration)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P)
    (W : Finset V) (hWZ : Disjoint W C.Z) (hWP : Disjoint W C.P)
    (p : V) (hp : p ∈ C.P) :
    (W.filter (G.Adj p)).card ≤ directCount G C.H p + epsilonAt G p C.s := by
  have hSubset : W.filter (G.Adj p) ⊆
      CertificateBridge.internalFirstNeighbors G C.H p ∪
        FinalBranch.rootArcFinset G C p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvW, hpv⟩
    have hvOut : v ∈ G.outNeighborFinset p :=
      (Digraph.mem_outNeighborFinset (G := G)).mpr hpv
    have hvCaptured := hCaptured p hp hvOut
    simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
    rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
    · exact ((Finset.disjoint_left.mp hWZ) hvW hvZ).elim
    · subst v
      exact Finset.mem_union_right _ (by
        simp [FinalBranch.rootArcFinset, hpv])
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvH, hpv⟩)
    · exact ((Finset.disjoint_left.mp hWP) hvW hvP).elim
  calc
    (W.filter (G.Adj p)).card ≤
        (CertificateBridge.internalFirstNeighbors G C.H p ∪
          FinalBranch.rootArcFinset G C p).card := Finset.card_le_card hSubset
    _ ≤ (CertificateBridge.internalFirstNeighbors G C.H p).card +
        (FinalBranch.rootArcFinset G C p).card := Finset.card_union_le _ _
    _ = directCount G C.H p + epsilonAt G p C.s := by
      rw [FinalBranch.card_rootArcFinset]
      rfl

omit [DecidableEq V] in
/-- The retained byte is the actual degree under the local degree decomposition. -/
theorem labelledRetainedDegree_toNat (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H}) (s : V) (i : Nat) (hi : i < 7)
    (hRoot : epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1)
    (hDegree : G.outdegree (eP ⟨i, hi⟩).1 =
      2 + epsilonAt G (eP ⟨i, hi⟩).1 s + directCount G H (eP ⟨i, hi⟩).1 +
        directCount G P (eP ⟨i, hi⟩).1)
    (hDegreeLt : G.outdegree (eP ⟨i, hi⟩).1 < 256) :
    (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) i).toNat = G.outdegree (eP ⟨i, hi⟩).1 := by
  have hPH :
      (labelledPToHCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i).toNat = directCount G H (eP ⟨i, hi⟩).1 := by
    have h := labelledPToHCount_toNat G (fun j ↦ (eP j).1) H eH i
    rw [pAt_of_lt (fun j ↦ (eP j).1) i hi] at h
    exact h
  have hPP :
      (labelledPOutCount G.Adj (fun j ↦ (eP j).1) i).toNat =
        directCount G P (eP ⟨i, hi⟩).1 := by
    have h := labelledPOutCount_toNat G P eP i
    rw [pAt_of_lt (fun j ↦ (eP j).1) i hi] at h
    exact h
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hThree : (3 : BitVec 8).toNat = 3 := by decide
  by_cases hi0 : i = 0
  · subst i
    have hRootZero : epsilonAt G (eP ⟨0, hi⟩).1 s = 0 := by
      simpa using hRoot
    simp only [labelledRetainedDegree, if_pos, BitVec.toNat_add,
      Nat.reducePow, hPH, hPP, hTwo]
    omega
  · simp [hi0] at hRoot
    simp only [labelledRetainedDegree, hi0, if_false, BitVec.toNat_add,
      Nat.reducePow, hPH, hPP, hThree]
    omega

omit [Fintype V] [DecidableEq V] in
/-- The labelled `P→H` total is the ordinary bipartite edge count. -/
theorem labelledTotalPToH_toNat (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (hNoOverflow : edgeCount G P H < 256) :
    (labelledTotalPToH G.Adj (fun i ↦ (eP i).1)
      (fun j ↦ (eH j).1)).toNat = edgeCount G P H := by
  let pLabel : Fin 7 → V := fun i ↦ (eP i).1
  let hLabel : Fin 5 → V := fun j ↦ (eH j).1
  have hSumLt :
      (labelledPToHCount G.Adj pLabel hLabel 0).toNat +
        (labelledPToHCount G.Adj pLabel hLabel 1).toNat +
        (labelledPToHCount G.Adj pLabel hLabel 2).toNat +
        (labelledPToHCount G.Adj pLabel hLabel 3).toNat +
        (labelledPToHCount G.Adj pLabel hLabel 4).toNat +
        (labelledPToHCount G.Adj pLabel hLabel 5).toNat +
        (labelledPToHCount G.Adj pLabel hLabel 6).toNat < 256 := by
    simp only [pLabel, hLabel, labelledPToHCount_toNat G]
    rw [edgeCount_eq_sum_fin G P H eP] at hNoOverflow
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hNoOverflow
  change (labelledTotalPToH G.Adj pLabel hLabel).toNat = edgeCount G P H
  rw [labelledTotalPToH, toNat_sumCountSeven _ hSumLt]
  simp only [pLabel, hLabel, labelledPToHCount_toNat G]
  rw [edgeCount_eq_sum_fin G P H eP]
  simp [Fin.sum_univ_succ, Nat.add_assoc]

omit [Fintype V] [DecidableEq V] in
/-- The labelled `P→P` total is the ordinary internal edge count. -/
theorem labelledTotalPOut_toNat (P : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (hNoOverflow : edgeCount G P P < 256) :
    (sumCountSeven
      (labelledPOutCount G.Adj (fun i ↦ (eP i).1))).toNat =
      edgeCount G P P := by
  let pLabel : Fin 7 → V := fun i ↦ (eP i).1
  have hSumLt :
      (labelledPOutCount G.Adj pLabel 0).toNat +
        (labelledPOutCount G.Adj pLabel 1).toNat +
        (labelledPOutCount G.Adj pLabel 2).toNat +
        (labelledPOutCount G.Adj pLabel 3).toNat +
        (labelledPOutCount G.Adj pLabel 4).toNat +
        (labelledPOutCount G.Adj pLabel 5).toNat +
        (labelledPOutCount G.Adj pLabel 6).toNat < 256 := by
    simp only [pLabel, labelledPOutCount_toNat G]
    rw [edgeCount_eq_sum_fin G P P eP] at hNoOverflow
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hNoOverflow
  change (sumCountSeven
    (labelledPOutCount G.Adj pLabel)).toNat = edgeCount G P P
  rw [toNat_sumCountSeven _ hSumLt]
  simp only [pLabel, labelledPOutCount_toNat G]
  rw [edgeCount_eq_sum_fin G P P eP]
  simp [Fin.sum_univ_succ, Nat.add_assoc]

omit [Fintype V] [DecidableEq V] in
/-- The labelled `H→P` total is the ordinary reverse bipartite edge count. -/
theorem labelledTotalHToP_toNat (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (hNoOverflow : edgeCount G H P < 256) :
    (labelledTotalHToP G.Adj (fun i ↦ (eP i).1)
      (fun j ↦ (eH j).1)).toNat = edgeCount G H P := by
  let pLabel : Fin 7 → V := fun i ↦ (eP i).1
  let hLabel : Fin 5 → V := fun j ↦ (eH j).1
  have hSumLt :
      (labelledHToPCount G.Adj pLabel hLabel 0).toNat +
        (labelledHToPCount G.Adj pLabel hLabel 1).toNat +
        (labelledHToPCount G.Adj pLabel hLabel 2).toNat +
        (labelledHToPCount G.Adj pLabel hLabel 3).toNat +
        (labelledHToPCount G.Adj pLabel hLabel 4).toNat < 256 := by
    simp only [pLabel, hLabel, labelledHToPCount_toNat G]
    rw [edgeCount_eq_sum_fin G H P eH] at hNoOverflow
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hNoOverflow
  change (labelledTotalHToP G.Adj pLabel hLabel).toNat = edgeCount G H P
  rw [labelledTotalHToP, toNat_sumCountFive _ hSumLt]
  simp only [pLabel, hLabel, labelledHToPCount_toNat G]
  rw [edgeCount_eq_sum_fin G H P eH]
  simp [Fin.sum_univ_succ, Nat.add_assoc]

omit [DecidableEq V] in
/-- Package ordinary finset data as the general ordered internal-edge core. -/
theorem labelledOrderedEdgeCore_of_finsetData (P H : Finset V) (s : V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (alpha internalEdges degreeSum : BitVec 8)
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hInternal : edgeCount G P P = internalEdges.toNat)
    (hPToH : edgeCount G P H + alpha.toNat = 17)
    (hHToP : 18 ≤ edgeCount G H P)
    (hRoot : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1)
    (hDegree : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (eP ⟨i, hi⟩).1 =
        2 + epsilonAt G (eP ⟨i, hi⟩).1 s +
          directCount G H (eP ⟨i, hi⟩).1 + directCount G P (eP ⟨i, hi⟩).1)
    (hDegreeBounds : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (eP ⟨i, hi⟩).1 ∧ G.outdegree (eP ⟨i, hi⟩).1 ≤ 9)
    (hEquation18 : ∀ i : Nat, i < 7 →
      labelledEquation18At G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i = true)
    (hOrdered : labelledInterchangeableOrdered G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) = true)
    (hDegreeSum : ∑ i : Fin 7, G.outdegree (eP i).1 = degreeSum.toNat) :
    LabelledOrderedEdgeCore G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) alpha internalEdges degreeSum := by
  have hInternalLt : edgeCount G P P < 256 := by
    rw [hInternal]
    exact internalEdges.isLt
  have hPToHLt : edgeCount G P H < 256 := by omega
  have hHToPLt : edgeCount G H P < 256 := by
    exact (Shared.edgeCount_le_card_mul_card G H P).trans_lt (by
      have hPCard : P.card = 7 := by
        simpa using (Fintype.card_congr eP).symm
      have hHCard : H.card = 5 := by
        simpa using (Fintype.card_congr eH).symm
      rw [hPCard, hHCard]
      omega)
  have hInternalNat := labelledTotalPOut_toNat G P eP hInternalLt
  have hPToHNat := labelledTotalPToH_toNat G P H eP eH hPToHLt
  have hHToPNat := labelledTotalHToP_toNat G P H eP eH hHToPLt
  refine {
    loopless := hLoopless
    anti := hAnti
    internalTotal := ?_
    totalPToH := ?_
    totalHToP := ?_
    perVertex := ?_
    ordered := hOrdered
    degreeSumEq := ?_
  }
  · apply BitVec.eq_of_toNat_eq
    rw [hInternalNat, hInternal]
  · apply BitVec.eq_of_toNat_eq
    have hSeventeen : (17 : BitVec 8).toNat = 17 := by decide
    simp only [BitVec.toNat_add, Nat.reducePow, hPToHNat, hSeventeen]
    omega
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hHToPNat]
    exact hHToP
  · intro i hi
    have hRetained := labelledRetainedDegree_toNat G P H eP eH s i hi
      (hRoot i hi) (hDegree i hi) (by have := (hDegreeBounds i hi).2; omega)
    have hBounds := hDegreeBounds i hi
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
    exact ⟨⟨by simpa [hRetained] using hBounds.1,
      by simpa [hRetained] using hBounds.2⟩, hEquation18 i hi⟩
  · have hRetained : ∀ i : Nat, (hi : i < 7) →
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) i).toNat = G.outdegree (eP ⟨i, hi⟩).1 := by
      intro i hi
      exact labelledRetainedDegree_toNat G P H eP eH s i hi
        (hRoot i hi) (hDegree i hi) (by have := (hDegreeBounds i hi).2; omega)
    have hNatSum :
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 0).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 1).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 2).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 3).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 4).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 5).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 6).toNat = degreeSum.toNat := by
      rw [hRetained 0 (by omega), hRetained 1 (by omega),
        hRetained 2 (by omega), hRetained 3 (by omega),
        hRetained 4 (by omega), hRetained 5 (by omega),
        hRetained 6 (by omega)]
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using hDegreeSum
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sumCountSeven _ (by
      have hDegreeSumLt := degreeSum.isLt
      omega)]
    exact hNatSum

omit [DecidableEq V] in
/-- Package ordinary graph data as the complete degree-sum-58 core. -/
theorem labelledDegreeTenCore_of_finsetData (P H : Finset V) (s : V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hInternal : edgeCount G P P = 21)
    (hPToH : edgeCount G P H = 17)
    (hHToP : 18 ≤ edgeCount G H P)
    (hRoot : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1)
    (hDegree : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (eP ⟨i, hi⟩).1 =
        2 + epsilonAt G (eP ⟨i, hi⟩).1 s +
          directCount G H (eP ⟨i, hi⟩).1 + directCount G P (eP ⟨i, hi⟩).1)
    (hDegreeBounds : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (eP ⟨i, hi⟩).1 ∧ G.outdegree (eP ⟨i, hi⟩).1 ≤ 10)
    (hEquation18 : ∀ i : Nat, i < 7 →
      labelledEquation18At G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i = true)
    (hOrdered : labelledInterchangeableOrdered G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) = true)
    (hDegreeSum : ∑ i : Fin 7, G.outdegree (eP i).1 = 58) :
    LabelledDegreeTenCore G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) := by
  have hInternalNat := labelledTotalPOut_toNat G P eP (by omega)
  have hPToHNat := labelledTotalPToH_toNat G P H eP eH (by omega)
  have hHToPLt : edgeCount G H P < 256 := by
    exact (Shared.edgeCount_le_card_mul_card G H P).trans_lt (by
      have hPCard : P.card = 7 := by
        simpa using (Fintype.card_congr eP).symm
      have hHCard : H.card = 5 := by
        simpa using (Fintype.card_congr eH).symm
      rw [hPCard, hHCard]
      omega)
  have hHToPNat := labelledTotalHToP_toNat G P H eP eH hHToPLt
  refine {
    loopless := hLoopless
    anti := hAnti
    internalTotal := ?_
    totalPToH := ?_
    totalHToP := ?_
    perVertex := ?_
    ordered := hOrdered
    degreeSumEq := ?_
  }
  · apply BitVec.eq_of_toNat_eq
    rw [hInternalNat, hInternal]
    decide
  · apply BitVec.eq_of_toNat_eq
    rw [hPToHNat, hPToH]
    decide
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hHToPNat]
    exact hHToP
  · intro i hi
    have hRetained := labelledRetainedDegree_toNat G P H eP eH s i hi
      (hRoot i hi) (hDegree i hi) (by have := (hDegreeBounds i hi).2; omega)
    have hBounds := hDegreeBounds i hi
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
    exact ⟨⟨by simpa [hRetained] using hBounds.1,
      by simpa [hRetained] using hBounds.2⟩, hEquation18 i hi⟩
  · have hRetained : ∀ i : Nat, (hi : i < 7) →
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) i).toNat = G.outdegree (eP ⟨i, hi⟩).1 := by
      intro i hi
      exact labelledRetainedDegree_toNat G P H eP eH s i hi
        (hRoot i hi) (hDegree i hi) (by have := (hDegreeBounds i hi).2; omega)
    have hNatSum :
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 0).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 1).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 2).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 3).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 4).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 5).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 6).toNat = 58 := by
      rw [hRetained 0 (by omega), hRetained 1 (by omega),
        hRetained 2 (by omega), hRetained 3 (by omega),
        hRetained 4 (by omega), hRetained 5 (by omega),
        hRetained 6 (by omega)]
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using hDegreeSum
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sumCountSeven _ (by omega)]
    exact hNatSum

omit [DecidableEq V] in
/--
Package ordinary finset counts and pointwise degree data as the labelled core
consumed by the checked terminal certificate.
-/
theorem labelledAlphaOneCore_of_finsetData (P H : Finset V) (s : V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (eP i).1 (eP j).1 ∨ G.Adj (eP j).1 (eP i).1)
    (hPToH : edgeCount G P H = 16)
    (hHToP : 18 ≤ edgeCount G H P)
    (hRoot : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (eP ⟨i, hi⟩).1 s = if i = 0 then 0 else 1)
    (hDegree : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (eP ⟨i, hi⟩).1 =
        2 + epsilonAt G (eP ⟨i, hi⟩).1 s +
          directCount G H (eP ⟨i, hi⟩).1 + directCount G P (eP ⟨i, hi⟩).1)
    (hDegreeBounds : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (eP ⟨i, hi⟩).1 ∧ G.outdegree (eP ⟨i, hi⟩).1 ≤ 9)
    (hEquation18 : ∀ i : Nat, i < 7 →
      labelledEquation18At G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i = true)
    (hOrdered : labelledInterchangeableOrdered G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) = true)
    (hDegreeSum : ∑ i : Fin 7, G.outdegree (eP i).1 = 57) :
    LabelledAlphaOneCore G.Adj (fun j ↦ (eP j).1)
      (fun j ↦ (eH j).1) := by
  have hPToHLt : edgeCount G P H < 256 := by omega
  have hHToPLt : edgeCount G H P < 256 := by
    exact (Shared.edgeCount_le_card_mul_card G H P).trans_lt (by
      have hPCard : P.card = 7 := by
        simpa using (Fintype.card_congr eP).symm
      have hHCard : H.card = 5 := by
        simpa using (Fintype.card_congr eH).symm
      rw [hPCard, hHCard]
      omega)
  have hPToHNat := labelledTotalPToH_toNat G P H eP eH hPToHLt
  have hHToPNat := labelledTotalHToP_toNat G P H eP eH hHToPLt
  refine {
    loopless := hLoopless
    anti := hAnti
    completeP := hComplete
    totalPToH := ?_
    totalHToP := ?_
    perVertex := ?_
    ordered := hOrdered
    degreeSum := ?_
  }
  · apply BitVec.eq_of_toNat_eq
    have hOne : (1 : BitVec 8).toNat = 1 := by decide
    have hSeventeen : (17 : BitVec 8).toNat = 17 := by decide
    simp only [BitVec.toNat_add, Nat.reducePow, hPToHNat, hOne, hSeventeen]
    omega
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hHToPNat]
    exact hHToP
  · intro i hi
    have hRetained := labelledRetainedDegree_toNat G P H eP eH s i hi
      (hRoot i hi) (hDegree i hi) (by have := (hDegreeBounds i hi).2; omega)
    have hBounds := hDegreeBounds i hi
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
    exact ⟨⟨by simpa [hRetained] using hBounds.1,
      by simpa [hRetained] using hBounds.2⟩, hEquation18 i hi⟩
  · have hRetained : ∀ i : Nat, (hi : i < 7) →
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) i).toNat = G.outdegree (eP ⟨i, hi⟩).1 := by
      intro i hi
      exact labelledRetainedDegree_toNat G P H eP eH s i hi
        (hRoot i hi) (hDegree i hi) (by have := (hDegreeBounds i hi).2; omega)
    have hNatSum :
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 0).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 1).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 2).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 3).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 4).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 5).toNat +
        (labelledRetainedDegree G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) 6).toNat = 57 := by
      rw [hRetained 0 (by omega), hRetained 1 (by omega),
        hRetained 2 (by omega), hRetained 3 (by omega),
        hRetained 4 (by omega), hRetained 5 (by omega),
        hRetained 6 (by omega)]
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using hDegreeSum
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sumCountSeven _ (by omega)]
    exact hNatSum

/--
Graph-level closure of the degree-sum-57 alpha-one core.  This theorem chooses
the exceptional label, sorts the other six labels, and invokes the checked
UNSAT certificate.
-/
theorem alphaOne_impossible_of_graphData (P H : Finset V) (s : V)
    (hPCard : P.card = 7) (hHCard : H.card = 5)
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hTournament : ∀ {u : V}, u ∈ P → ∀ {v : V}, v ∈ P → u ≠ v →
      G.Adj u v ∨ G.Adj v u)
    (hPToH : edgeCount G P H = 16)
    (hHToP : 18 ≤ edgeCount G H P)
    (hRootCount : ∑ p ∈ P, epsilonAt G p s = 6)
    (hDegree : ∀ p ∈ P, G.outdegree p =
      2 + epsilonAt G p s + directCount G H p + directCount G P p)
    (hDegreeBounds : ∀ p ∈ P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 9)
    (hEquation18 : ∀ p ∈ P, qCount G P H p + 7 ≤ directCount G P p +
      2 * directCount G H p + 2 * epsilonAt G p s)
    (hDegreeSum : ∑ p ∈ P, G.outdegree p = 57) : False := by
  obtain ⟨eP, hRoot⟩ := exists_rootLabelEquiv G P s hPCard hRootCount
  let eH := finsetEquivFin H hHCard
  let ePS := sortedFinsetEquiv G.outdegree (directCount G H) P eP
  have hRootSorted : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (ePS ⟨i, hi⟩).1 s = if i = 0 then 0 else 1 := by
    exact sortedFinsetEquiv_root G G.outdegree (directCount G H) P eP s hRoot
  have hComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (ePS i).1 (ePS j).1 ∨ G.Adj (ePS j).1 (ePS i).1 := by
    intro i j hij
    apply hTournament (ePS i).2 (ePS j).2
    intro hEq
    exact hij (ePS.injective (Subtype.ext hEq))
  have hDegreeLabel : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (ePS ⟨i, hi⟩).1 =
        2 + epsilonAt G (ePS ⟨i, hi⟩).1 s +
          directCount G H (ePS ⟨i, hi⟩).1 + directCount G P (ePS ⟨i, hi⟩).1 := by
    intro i hi
    exact hDegree _ (ePS ⟨i, hi⟩).2
  have hBoundsLabel : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (ePS ⟨i, hi⟩).1 ∧ G.outdegree (ePS ⟨i, hi⟩).1 ≤ 9 := by
    intro i hi
    exact hDegreeBounds _ (ePS ⟨i, hi⟩).2
  have hEquationLabel : ∀ i : Nat, i < 7 →
      labelledEquation18At G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i = true := by
    intro i hi
    exact labelledEquation18At_true_of_graph G P H s ePS eH i hi
      (hRootSorted i hi) (hEquation18 _ (ePS ⟨i, hi⟩).2)
  have hCountLt : ∀ v, directCount G H v < 256 := by
    intro v
    have hLe := Finset.card_le_card
      (Finset.filter_subset (p := G.Adj v) H)
    unfold directCount CertificateBridge.internalFirstNeighbors
    omega
  have hRetained : ∀ i : Fin 7,
      (labelledRetainedDegree G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i).toNat = G.outdegree (ePS i).1 := by
    intro i
    exact labelledRetainedDegree_toNat G P H ePS eH s i.val i.isLt
      (hRootSorted i.val i.isLt) (hDegreeLabel i.val i.isLt) (by
        have := (hBoundsLabel i.val i.isLt).2
        omega)
  have hHCount : ∀ i : Fin 7,
      (labelledPToHCount G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i).toNat = directCount G H (ePS i).1 := by
    intro i
    have h := labelledPToHCount_toNat G (fun j ↦ (ePS j).1) H eH i.val
    rw [pAt_of_lt (fun j ↦ (ePS j).1) i.val i.isLt] at h
    exact h
  have hOrdered : labelledInterchangeableOrdered G.Adj (fun j ↦ (ePS j).1)
      (fun j ↦ (eH j).1) = true := by
    change labelledInterchangeableOrdered G.Adj
      (sortedP G.outdegree (directCount G H) (fun j ↦ (eP j).1))
      (fun j ↦ (eH j).1) = true
    apply labelledInterchangeableOrdered_sortedP G.Adj G.outdegree
      (directCount G H) (fun j ↦ (eP j).1) (fun j ↦ (eH j).1) hCountLt
    · intro i
      simpa [ePS] using hRetained i
    · intro i
      simpa [ePS] using hHCount i
  have hDegreeSumLabel : ∑ i : Fin 7, G.outdegree (ePS i).1 = 57 := by
    rw [← sum_finset_eq_sum_fin P ePS G.outdegree]
    exact hDegreeSum
  let core := labelledAlphaOneCore_of_finsetData G P H s ePS eH hLoopless
    hAnti hComplete hPToH hHToP hRootSorted hDegreeLabel hBoundsLabel
    hEquationLabel hOrdered hDegreeSumLabel
  exact LabelledAlphaOneCore.impossible core

/--
Graph-level closure for any of the ordered internal-edge certificates.  It
chooses the exceptional root label, canonically sorts the other six vertices,
and transfers all ordinary finset counts to the checked Boolean core.
-/
theorem orderedEdge_impossible_of_graphData (P H : Finset V) (s : V)
    (alpha internalEdges degreeSum : BitVec 8)
    (hUnsat : ∀ bits : BitVec 119,
      orderedOneMissingRootEdgeCore bits alpha internalEdges degreeSum = false)
    (hPCard : P.card = 7) (hHCard : H.card = 5)
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hInternal : edgeCount G P P = internalEdges.toNat)
    (hPToH : edgeCount G P H + alpha.toNat = 17)
    (hHToP : 18 ≤ edgeCount G H P)
    (hRootCount : ∑ p ∈ P, epsilonAt G p s = 6)
    (hDegree : ∀ p ∈ P, G.outdegree p =
      2 + epsilonAt G p s + directCount G H p + directCount G P p)
    (hDegreeBounds : ∀ p ∈ P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 9)
    (hEquation18 : ∀ p ∈ P, qCount G P H p + 7 ≤ directCount G P p +
      2 * directCount G H p + 2 * epsilonAt G p s)
    (hDegreeSum : ∑ p ∈ P, G.outdegree p = degreeSum.toNat) : False := by
  obtain ⟨eP, hRoot⟩ := exists_rootLabelEquiv G P s hPCard hRootCount
  let eH := finsetEquivFin H hHCard
  let ePS := sortedFinsetEquiv G.outdegree (directCount G H) P eP
  have hRootSorted : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (ePS ⟨i, hi⟩).1 s = if i = 0 then 0 else 1 := by
    exact sortedFinsetEquiv_root G G.outdegree (directCount G H) P eP s hRoot
  have hDegreeLabel : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (ePS ⟨i, hi⟩).1 =
        2 + epsilonAt G (ePS ⟨i, hi⟩).1 s +
          directCount G H (ePS ⟨i, hi⟩).1 + directCount G P (ePS ⟨i, hi⟩).1 := by
    intro i hi
    exact hDegree _ (ePS ⟨i, hi⟩).2
  have hBoundsLabel : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (ePS ⟨i, hi⟩).1 ∧ G.outdegree (ePS ⟨i, hi⟩).1 ≤ 9 := by
    intro i hi
    exact hDegreeBounds _ (ePS ⟨i, hi⟩).2
  have hEquationLabel : ∀ i : Nat, i < 7 →
      labelledEquation18At G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i = true := by
    intro i hi
    exact labelledEquation18At_true_of_graph G P H s ePS eH i hi
      (hRootSorted i hi) (hEquation18 _ (ePS ⟨i, hi⟩).2)
  have hCountLt : ∀ v, directCount G H v < 256 := by
    intro v
    have hLe := Finset.card_le_card
      (Finset.filter_subset (p := G.Adj v) H)
    unfold directCount CertificateBridge.internalFirstNeighbors
    omega
  have hRetained : ∀ i : Fin 7,
      (labelledRetainedDegree G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i).toNat = G.outdegree (ePS i).1 := by
    intro i
    exact labelledRetainedDegree_toNat G P H ePS eH s i.val i.isLt
      (hRootSorted i.val i.isLt) (hDegreeLabel i.val i.isLt) (by
        have := (hBoundsLabel i.val i.isLt).2
        omega)
  have hHCount : ∀ i : Fin 7,
      (labelledPToHCount G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i).toNat = directCount G H (ePS i).1 := by
    intro i
    have h := labelledPToHCount_toNat G (fun j ↦ (ePS j).1) H eH i.val
    rw [pAt_of_lt (fun j ↦ (ePS j).1) i.val i.isLt] at h
    exact h
  have hOrdered : labelledInterchangeableOrdered G.Adj (fun j ↦ (ePS j).1)
      (fun j ↦ (eH j).1) = true := by
    change labelledInterchangeableOrdered G.Adj
      (sortedP G.outdegree (directCount G H) (fun j ↦ (eP j).1))
      (fun j ↦ (eH j).1) = true
    apply labelledInterchangeableOrdered_sortedP G.Adj G.outdegree
      (directCount G H) (fun j ↦ (eP j).1) (fun j ↦ (eH j).1) hCountLt
    · intro i
      simpa [ePS] using hRetained i
    · intro i
      simpa [ePS] using hHCount i
  have hDegreeSumLabel :
      ∑ i : Fin 7, G.outdegree (ePS i).1 = degreeSum.toNat := by
    rw [← sum_finset_eq_sum_fin P ePS G.outdegree]
    exact hDegreeSum
  let core := labelledOrderedEdgeCore_of_finsetData G P H s ePS eH
    alpha internalEdges degreeSum hLoopless hAnti hInternal hPToH hHToP
    hRootSorted hDegreeLabel hBoundsLabel hEquationLabel hOrdered hDegreeSumLabel
  exact LabelledOrderedEdgeCore.impossible core hUnsat

/--
Graph-level closure of the complete degree-sum-58 core, permitting retained
degrees up to ten.
-/
theorem degreeTen_impossible_of_graphData (P H : Finset V) (s : V)
    (hPCard : P.card = 7) (hHCard : H.card = 5)
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hInternal : edgeCount G P P = 21)
    (hPToH : edgeCount G P H = 17)
    (hHToP : 18 ≤ edgeCount G H P)
    (hRootCount : ∑ p ∈ P, epsilonAt G p s = 6)
    (hDegree : ∀ p ∈ P, G.outdegree p =
      2 + epsilonAt G p s + directCount G H p + directCount G P p)
    (hDegreeBounds : ∀ p ∈ P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 10)
    (hEquation18 : ∀ p ∈ P, qCount G P H p + 7 ≤ directCount G P p +
      2 * directCount G H p + 2 * epsilonAt G p s)
    (hDegreeSum : ∑ p ∈ P, G.outdegree p = 58) : False := by
  obtain ⟨eP, hRoot⟩ := exists_rootLabelEquiv G P s hPCard hRootCount
  let eH := finsetEquivFin H hHCard
  let ePS := sortedFinsetEquiv G.outdegree (directCount G H) P eP
  have hRootSorted : ∀ i : Nat, (hi : i < 7) →
      epsilonAt G (ePS ⟨i, hi⟩).1 s = if i = 0 then 0 else 1 := by
    exact sortedFinsetEquiv_root G G.outdegree (directCount G H) P eP s hRoot
  have hDegreeLabel : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (ePS ⟨i, hi⟩).1 =
        2 + epsilonAt G (ePS ⟨i, hi⟩).1 s +
          directCount G H (ePS ⟨i, hi⟩).1 + directCount G P (ePS ⟨i, hi⟩).1 := by
    intro i hi
    exact hDegree _ (ePS ⟨i, hi⟩).2
  have hBoundsLabel : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (ePS ⟨i, hi⟩).1 ∧ G.outdegree (ePS ⟨i, hi⟩).1 ≤ 10 := by
    intro i hi
    exact hDegreeBounds _ (ePS ⟨i, hi⟩).2
  have hEquationLabel : ∀ i : Nat, i < 7 →
      labelledEquation18At G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i = true := by
    intro i hi
    exact labelledEquation18At_true_of_graph G P H s ePS eH i hi
      (hRootSorted i hi) (hEquation18 _ (ePS ⟨i, hi⟩).2)
  have hCountLt : ∀ v, directCount G H v < 256 := by
    intro v
    have hLe := Finset.card_le_card
      (Finset.filter_subset (p := G.Adj v) H)
    unfold directCount CertificateBridge.internalFirstNeighbors
    omega
  have hRetained : ∀ i : Fin 7,
      (labelledRetainedDegree G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i).toNat = G.outdegree (ePS i).1 := by
    intro i
    exact labelledRetainedDegree_toNat G P H ePS eH s i.val i.isLt
      (hRootSorted i.val i.isLt) (hDegreeLabel i.val i.isLt) (by
        have := (hBoundsLabel i.val i.isLt).2
        omega)
  have hHCount : ∀ i : Fin 7,
      (labelledPToHCount G.Adj (fun j ↦ (ePS j).1)
        (fun j ↦ (eH j).1) i).toNat = directCount G H (ePS i).1 := by
    intro i
    have h := labelledPToHCount_toNat G (fun j ↦ (ePS j).1) H eH i.val
    rw [pAt_of_lt (fun j ↦ (ePS j).1) i.val i.isLt] at h
    exact h
  have hOrdered : labelledInterchangeableOrdered G.Adj (fun j ↦ (ePS j).1)
      (fun j ↦ (eH j).1) = true := by
    change labelledInterchangeableOrdered G.Adj
      (sortedP G.outdegree (directCount G H) (fun j ↦ (eP j).1))
      (fun j ↦ (eH j).1) = true
    apply labelledInterchangeableOrdered_sortedP G.Adj G.outdegree
      (directCount G H) (fun j ↦ (eP j).1) (fun j ↦ (eH j).1) hCountLt
    · intro i
      simpa [ePS] using hRetained i
    · intro i
      simpa [ePS] using hHCount i
  have hDegreeSumLabel : ∑ i : Fin 7, G.outdegree (ePS i).1 = 58 := by
    rw [← sum_finset_eq_sum_fin P ePS G.outdegree]
    exact hDegreeSum
  let core := labelledDegreeTenCore_of_finsetData G P H s ePS eH
    hLoopless hAnti hInternal hPToH hHToP hRootSorted hDegreeLabel
    hBoundsLabel hEquationLabel hOrdered hDegreeSumLabel
  exact LabelledDegreeTenCore.impossible core

/--
Shared local-configuration reduction for the ordered terminal defect rows.
The row-specific theorems below only have to derive the numerical equalities.
-/
theorem terminal_orderedEdge_impossible_of_counts (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (alpha internalEdges degreeSum : BitVec 8)
    (hUnsat : ∀ bits : BitVec 119,
      orderedOneMissingRootEdgeCore bits alpha internalEdges degreeSum = false)
    (hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6)
    (hPToHEq : edgeCount G C.P C.H + alpha.toNat = 17)
    (hInternal : edgeCount G C.P C.P = internalEdges.toNat)
    (hDegreeUpper : ∀ p ∈ C.P, G.outdegree p ≤ 9)
    (hDegreeSum : ∑ p ∈ C.P, G.outdegree p = degreeSum.toNat) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hHP : 18 ≤ edgeCount G C.H C.P :=
    BSevenKOneTerminal.eighteen_le_H_to_P G C hG hMin hRootDegree
      hBCard hk hx
  have hFullPZ := all_P_to_Z_of_edgeCount_fourteen G C.P C.Z
    D.pCard D.zCard D.pToZCount
  have hPB := FinalDefects.p_eq_B_of_cards (G := G) C D.pCard D.bCard
  have hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
    intro p hp
    exact Shared.outgoingCaptured_of_p_eq_B G C hG hPB p hp
  have hDegree : ∀ p ∈ C.P, G.outdegree p =
      2 + epsilonAt G p C.s + directCount G C.H p + directCount G C.P p := by
    intro p hp
    exact outdegree_eq_local_counts G C hG D.zCard hFullPZ hCaptured p hp
  have hBounds : ∀ p ∈ C.P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 9 := by
    intro p hp
    exact ⟨hMin p, hDegreeUpper p hp⟩
  obtain ⟨z0, hz0Z, hz0Sink⟩ :=
    FinalBranch.exists_sink_in_pair G C.Z D.zCard hG
  let W := G.outNeighborFinset z0
  have hz0W : ∀ w ∈ W, G.Adj z0 w := by
    intro w hw
    exact (Digraph.mem_outNeighborFinset (G := G)).mp hw
  have hWZ : Disjoint W C.Z := by
    rw [Finset.disjoint_left]
    intro w hwW hwZ
    exact hz0Sink w hwZ (hz0W w hwW)
  have hWP : Disjoint W C.P := by
    rw [Finset.disjoint_left]
    intro p hpW hpP
    exact hG.2 (hFullPZ p hpP z0 hz0Z) (hz0W p hpW)
  have hWCard : 8 ≤ W.card := by
    change 8 ≤ G.outdegree z0
    exact hMin z0
  have hEquation : ∀ p ∈ C.P, qCount G C.P C.H p + 7 ≤
      directCount G C.P p + 2 * directCount G C.H p +
        2 * epsilonAt G p C.s := by
    intro p hp
    exact equation18_of_commonZ G C.P C.H W p C.s z0 hp
      (hFullPZ p hp z0 hz0Z) hz0W hWP hWCard
      (direct_W_bound_of_captured G C hCaptured W hWZ hWP p hp)
      (D.noSeymour p) (hDegree p hp)
  exact orderedEdge_impossible_of_graphData G C.P C.H C.s
    alpha internalEdges degreeSum hUnsat D.pCard hHCard hG.1 hG.2
    hInternal hPToHEq hHP hRootCount hDegree hBounds hEquation hDegreeSum

/-- Shared local-configuration reduction for the degree-sum-58 core. -/
theorem terminal_degreeTen_impossible_of_counts (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6)
    (hPToH : edgeCount G C.P C.H = 17)
    (hInternal : edgeCount G C.P C.P = 21)
    (hDegreeUpper : ∀ p ∈ C.P, G.outdegree p ≤ 10)
    (hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 58) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hHP : 18 ≤ edgeCount G C.H C.P :=
    BSevenKOneTerminal.eighteen_le_H_to_P G C hG hMin hRootDegree
      hBCard hk hx
  have hFullPZ := all_P_to_Z_of_edgeCount_fourteen G C.P C.Z
    D.pCard D.zCard D.pToZCount
  have hPB := FinalDefects.p_eq_B_of_cards (G := G) C D.pCard D.bCard
  have hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
    intro p hp
    exact Shared.outgoingCaptured_of_p_eq_B G C hG hPB p hp
  have hDegree : ∀ p ∈ C.P, G.outdegree p =
      2 + epsilonAt G p C.s + directCount G C.H p + directCount G C.P p := by
    intro p hp
    exact outdegree_eq_local_counts G C hG D.zCard hFullPZ hCaptured p hp
  have hBounds : ∀ p ∈ C.P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 10 := by
    intro p hp
    exact ⟨hMin p, hDegreeUpper p hp⟩
  obtain ⟨z0, hz0Z, hz0Sink⟩ :=
    FinalBranch.exists_sink_in_pair G C.Z D.zCard hG
  let W := G.outNeighborFinset z0
  have hz0W : ∀ w ∈ W, G.Adj z0 w := by
    intro w hw
    exact (Digraph.mem_outNeighborFinset (G := G)).mp hw
  have hWZ : Disjoint W C.Z := by
    rw [Finset.disjoint_left]
    intro w hwW hwZ
    exact hz0Sink w hwZ (hz0W w hwW)
  have hWP : Disjoint W C.P := by
    rw [Finset.disjoint_left]
    intro p hpW hpP
    exact hG.2 (hFullPZ p hpP z0 hz0Z) (hz0W p hpW)
  have hWCard : 8 ≤ W.card := by
    change 8 ≤ G.outdegree z0
    exact hMin z0
  have hEquation : ∀ p ∈ C.P, qCount G C.P C.H p + 7 ≤
      directCount G C.P p + 2 * directCount G C.H p +
        2 * epsilonAt G p C.s := by
    intro p hp
    exact equation18_of_commonZ G C.P C.H W p C.s z0 hp
      (hFullPZ p hp z0 hz0Z) hz0W hWP hWCard
      (direct_W_bound_of_captured G C hCaptured W hWZ hWP p hp)
      (D.noSeymour p) (hDegree p hp)
  exact degreeTen_impossible_of_graphData G C.P C.H C.s D.pCard hHCard
    hG.1 hG.2 hInternal hPToH hHP hRootCount hDegree hBounds hEquation
    hDegreeSum

/--
The graph-level terminal defect row `(m,alpha,beta)=(1,1,0)` is impossible.
-/
theorem terminal_one_one_zero_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hAlpha : BSevenKOneTerminal.alphaDefect G C = 1)
    (hBeta : BSevenKOneTerminal.betaDefect G C = 0) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hExcessEq := FinalDefects.FinalTightDefects.degreeExcessEquation
    (G := G) D
  have hExcess : ∑ p ∈ C.P, (G.outdegree p - 8) = 1 := by omega
  have hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6 := by
    have hMissing := D.missingEquation
    have hPZ := D.pToZCount
    omega
  have hPH : edgeCount G C.P C.H = 16 := by
    have hEq := D.alphaEquation
    omega
  have hPP : edgeCount G C.P C.P = 21 := by
    have hEq := D.betaEquation
    omega
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hHP : 18 ≤ edgeCount G C.H C.P :=
    BSevenKOneTerminal.eighteen_le_H_to_P G C hG hMin hRootDegree
      hBCard hk hx
  have hTournament : ∀ {u : V}, u ∈ C.P → ∀ {v : V}, v ∈ C.P → u ≠ v →
      G.Adj u v ∨ G.Adj v u :=
    RawFinalBranch.tournament_of_edgeCount_eq_twentyOne
      G C.P D.pCard hG hPP
  have hFullPZ := all_P_to_Z_of_edgeCount_fourteen G C.P C.Z
    D.pCard D.zCard D.pToZCount
  have hPB := FinalDefects.p_eq_B_of_cards (G := G) C D.pCard D.bCard
  have hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
    intro p hp
    exact Shared.outgoingCaptured_of_p_eq_B G C hG hPB p hp
  have hDegree : ∀ p ∈ C.P, G.outdegree p =
      2 + epsilonAt G p C.s + directCount G C.H p + directCount G C.P p := by
    intro p hp
    exact outdegree_eq_local_counts G C hG D.zCard hFullPZ hCaptured p hp
  have hBounds : ∀ p ∈ C.P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 9 := by
    intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) := by
      exact Finset.single_le_sum (s := C.P)
        (f := fun q ↦ G.outdegree q - 8) (fun _ _ ↦ Nat.zero_le _) hp
    exact ⟨hMin p, by omega⟩
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 57 := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := hMin p
        omega
      _ = 57 := by
        rw [Finset.sum_add_distrib, hExcess]
        simp [D.pCard]
  obtain ⟨z0, hz0Z, hz0Sink⟩ :=
    FinalBranch.exists_sink_in_pair G C.Z D.zCard hG
  let W := G.outNeighborFinset z0
  have hz0W : ∀ w ∈ W, G.Adj z0 w := by
    intro w hw
    exact (Digraph.mem_outNeighborFinset (G := G)).mp hw
  have hWZ : Disjoint W C.Z := by
    rw [Finset.disjoint_left]
    intro w hwW hwZ
    exact hz0Sink w hwZ (hz0W w hwW)
  have hWP : Disjoint W C.P := by
    rw [Finset.disjoint_left]
    intro p hpW hpP
    exact hG.2 (hFullPZ p hpP z0 hz0Z) (hz0W p hpW)
  have hWCard : 8 ≤ W.card := by
    change 8 ≤ G.outdegree z0
    exact hMin z0
  have hEquation : ∀ p ∈ C.P, qCount G C.P C.H p + 7 ≤
      directCount G C.P p + 2 * directCount G C.H p +
        2 * epsilonAt G p C.s := by
    intro p hp
    exact equation18_of_commonZ G C.P C.H W p C.s z0 hp
      (hFullPZ p hp z0 hz0Z) hz0W hWP hWCard
      (direct_W_bound_of_captured G C hCaptured W hWZ hWP p hp)
      (D.noSeymour p) (hDegree p hp)
  exact alphaOne_impossible_of_graphData G C.P C.H C.s D.pCard hHCard
    hG.1 hG.2 hTournament hPH hHP hRootCount hDegree hBounds hEquation
    hDegreeSum

/-- The graph-level terminal defect row `(m,alpha,beta)=(1,0,1)` is impossible. -/
theorem terminal_one_zero_one_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hAlpha : BSevenKOneTerminal.alphaDefect G C = 0)
    (hBeta : BSevenKOneTerminal.betaDefect G C = 1) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hExcessEq := FinalDefects.FinalTightDefects.degreeExcessEquation
    (G := G) D
  have hExcess : ∑ p ∈ C.P, (G.outdegree p - 8) = 1 := by omega
  have hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6 := by
    have hMissing := D.missingEquation
    have hPZ := D.pToZCount
    omega
  have hPH : edgeCount G C.P C.H = 17 := by
    have hEq := D.alphaEquation
    omega
  have hPP : edgeCount G C.P C.P = 20 := by
    have hEq := D.betaEquation
    omega
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 57 := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := hMin p
        omega
      _ = 57 := by
        rw [Finset.sum_add_distrib, hExcess]
        simp [D.pCard]
  apply terminal_orderedEdge_impossible_of_counts G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ 0 20 57
    alphaZeroBetaOne_unsat hRootCount
  · have hZero : (0 : BitVec 8).toNat = 0 := by decide
    omega
  · have hTwenty : (20 : BitVec 8).toNat = 20 := by decide
    omega
  · intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) := by
      exact Finset.single_le_sum (s := C.P)
        (f := fun q ↦ G.outdegree q - 8) (fun _ _ ↦ Nat.zero_le _) hp
    omega
  · exact hDegreeSum

/-- The graph-level terminal defect row `(m,alpha,beta)=(1,1,1)` is impossible. -/
theorem terminal_one_one_one_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hAlpha : BSevenKOneTerminal.alphaDefect G C = 1)
    (hBeta : BSevenKOneTerminal.betaDefect G C = 1) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hExcessEq := FinalDefects.FinalTightDefects.degreeExcessEquation
    (G := G) D
  have hExcess : ∑ p ∈ C.P, (G.outdegree p - 8) = 0 := by omega
  have hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6 := by
    have hMissing := D.missingEquation
    have hPZ := D.pToZCount
    omega
  have hPH : edgeCount G C.P C.H = 16 := by
    have hEq := D.alphaEquation
    omega
  have hPP : edgeCount G C.P C.P = 20 := by
    have hEq := D.betaEquation
    omega
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 56 := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := hMin p
        omega
      _ = 56 := by
        rw [Finset.sum_add_distrib, hExcess]
        simp [D.pCard]
  apply terminal_orderedEdge_impossible_of_counts G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ 1 20 56
    alphaOneBetaOne_unsat hRootCount
  · have hOne : (1 : BitVec 8).toNat = 1 := by decide
    omega
  · have hTwenty : (20 : BitVec 8).toNat = 20 := by decide
    omega
  · intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) := by
      exact Finset.single_le_sum (s := C.P)
        (f := fun q ↦ G.outdegree q - 8) (fun _ _ ↦ Nat.zero_le _) hp
    omega
  · exact hDegreeSum

/-- The graph-level terminal defect row `(m,alpha,beta)=(1,0,2)` is impossible. -/
theorem terminal_one_zero_two_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hAlpha : BSevenKOneTerminal.alphaDefect G C = 0)
    (hBeta : BSevenKOneTerminal.betaDefect G C = 2) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hExcessEq := FinalDefects.FinalTightDefects.degreeExcessEquation
    (G := G) D
  have hExcess : ∑ p ∈ C.P, (G.outdegree p - 8) = 0 := by omega
  have hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6 := by
    have hMissing := D.missingEquation
    have hPZ := D.pToZCount
    omega
  have hPH : edgeCount G C.P C.H = 17 := by
    have hEq := D.alphaEquation
    omega
  have hPP : edgeCount G C.P C.P = 19 := by
    have hEq := D.betaEquation
    omega
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 56 := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := hMin p
        omega
      _ = 56 := by
        rw [Finset.sum_add_distrib, hExcess]
        simp [D.pCard]
  apply terminal_orderedEdge_impossible_of_counts G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ 0 19 56
    alphaZeroBetaTwo_unsat hRootCount
  · have hZero : (0 : BitVec 8).toNat = 0 := by decide
    omega
  · have hNineteen : (19 : BitVec 8).toNat = 19 := by decide
    omega
  · intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) := by
      exact Finset.single_le_sum (s := C.P)
        (f := fun q ↦ G.outdegree q - 8) (fun _ _ ↦ Nat.zero_le _) hp
    omega
  · exact hDegreeSum

/-- The complete degree-sum-58 row `(m,alpha,beta)=(1,0,0)` is impossible. -/
theorem terminal_one_zero_zero_impossible
    (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hAlpha : BSevenKOneTerminal.alphaDefect G C = 0)
    (hBeta : BSevenKOneTerminal.betaDefect G C = 0) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hExcessEq := FinalDefects.FinalTightDefects.degreeExcessEquation
    (G := G) D
  have hExcess : ∑ p ∈ C.P, (G.outdegree p - 8) = 2 := by omega
  have hRootCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6 := by
    have hMissing := D.missingEquation
    have hPZ := D.pToZCount
    omega
  have hPH : edgeCount G C.P C.H = 17 := by
    have hEq := D.alphaEquation
    omega
  have hPP : edgeCount G C.P C.P = 21 := by
    have hEq := D.betaEquation
    omega
  have hDegreeUpper : ∀ p ∈ C.P, G.outdegree p ≤ 10 := by
    intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) := by
      exact Finset.single_le_sum (s := C.P)
        (f := fun q ↦ G.outdegree q - 8) (fun _ _ ↦ Nat.zero_le _) hp
    have hpMin := hMin p
    omega
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 58 := by
    calc
      (∑ p ∈ C.P, G.outdegree p) =
          ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := hMin p
        omega
      _ = 58 := by
        rw [Finset.sum_add_distrib, hExcess]
        simp [D.pCard]
  exact terminal_degreeTen_impossible_of_counts G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ hRootCount hPH hPP
    hDegreeUpper hDegreeSum

/--
Degree-at-most-nine specialization of `terminal_one_zero_zero_impossible`.
-/
theorem terminal_one_zero_zero_impossible_of_degree_le_nine
    (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hAlpha : BSevenKOneTerminal.alphaDefect G C = 0)
    (hBeta : BSevenKOneTerminal.betaDefect G C = 0)
    (_hDegreeUpper : ∀ p ∈ C.P, G.outdegree p ≤ 9) : False :=
  terminal_one_zero_zero_impossible G C hG hMin hNoSeymour hRootDegree
    hBCard hk hx hz hEpsilon hPToZ hm hAlpha hBeta

/--
The five degree-sum-56/57 cores exhaust the tight row once
`1 ≤ alpha + beta ≤ 2`.
-/
theorem terminal_five_core_rows_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hDefectLower : 1 ≤ BSevenKOneTerminal.alphaDefect G C +
      BSevenKOneTerminal.betaDefect G C)
    (hDefectUpper : BSevenKOneTerminal.alphaDefect G C +
      BSevenKOneTerminal.betaDefect G C ≤ 2) : False := by
  have hCases :
      (BSevenKOneTerminal.alphaDefect G C = 0 ∧
        BSevenKOneTerminal.betaDefect G C = 1) ∨
      (BSevenKOneTerminal.alphaDefect G C = 1 ∧
        BSevenKOneTerminal.betaDefect G C = 0) ∨
      (BSevenKOneTerminal.alphaDefect G C = 0 ∧
        BSevenKOneTerminal.betaDefect G C = 2) ∨
      (BSevenKOneTerminal.alphaDefect G C = 1 ∧
        BSevenKOneTerminal.betaDefect G C = 1) ∨
      (BSevenKOneTerminal.alphaDefect G C = 2 ∧
        BSevenKOneTerminal.betaDefect G C = 0) := by
    omega
  rcases hCases with h01 | h10 | h02 | h11 | h20
  · exact terminal_one_zero_one_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPToZ hm h01.1 h01.2
  · exact terminal_one_one_zero_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPToZ hm h10.1 h10.2
  · exact terminal_one_zero_two_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPToZ hm h02.1 h02.2
  · exact terminal_one_one_one_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPToZ hm h11.1 h11.2
  · exact BSevenKOneTerminal.terminal_one_two_zero_impossible G C hG hMin
      hNoSeymour hRootDegree hBCard hk hx hz hEpsilon hPToZ hm h20.1 h20.2

/--
All six terminal defect cores with `alpha + beta ≤ 2` are impossible,
including the degree-sum-58 core `(alpha,beta)=(0,0)`.
-/
theorem terminal_six_core_rows_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1)
    (hDefectUpper : BSevenKOneTerminal.alphaDefect G C +
      BSevenKOneTerminal.betaDefect G C ≤ 2) : False := by
  by_cases hZero : BSevenKOneTerminal.alphaDefect G C +
      BSevenKOneTerminal.betaDefect G C = 0
  · have hAlpha : BSevenKOneTerminal.alphaDefect G C = 0 := by omega
    have hBeta : BSevenKOneTerminal.betaDefect G C = 0 := by omega
    exact terminal_one_zero_zero_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPToZ hm hAlpha hBeta
  · apply terminal_five_core_rows_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPToZ hm
    · omega
    · exact hDefectUpper

/--
The exact terminal branch isolated by the preceding deletion reduction is
impossible; the degree-excess identity supplies the defect bound needed by
the six cores.
-/
theorem terminal_final_slice_impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hPToZ : edgeCount G C.P C.Z = 14)
    (hm : BSevenKOneTerminal.mDefect G C = 1) : False := by
  let D := BSevenKOneTerminal.toFinalTightDefects G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ
  have hExcessEq := FinalDefects.FinalTightDefects.degreeExcessEquation
    (G := G) D
  have hDefectUpper : BSevenKOneTerminal.alphaDefect G C +
      BSevenKOneTerminal.betaDefect G C ≤ 2 := by
    omega
  exact terminal_six_core_rows_impossible G C hG hMin hNoSeymour
    hRootDegree hBCard hk hx hz hEpsilon hPToZ hm hDefectUpper

/--
After closing the root-target alternative, any hypothetical one-defect
configuration must have its unique missing external arc aimed at `Z`.
-/
theorem terminal_one_defect_forces_missing_Z (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hm : BSevenKOneTerminal.mDefect G C = 1) :
    edgeCount G C.P C.Z = 13 ∧
      ∑ p ∈ C.P, epsilonAt G p C.s = 7 := by
  rcases BSevenKOneTerminal.one_defect_target_split G C hG hMin hBCard hk
      hz hEpsilon hm with hRoot | hZ
  · exact (terminal_final_slice_impossible G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hRoot.1 hm).elim
  · exact hZ

/--
Complete graph-side interface for the `m=1` alternative with one missing
`P→Z` arc and a five-vertex exact-degree-eight deletion tail.
-/
theorem terminal_one_defect_residual
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : Shared.epsilonS G C = 1)
    (hm : BSevenKOneTerminal.mDefect G C = 1) :
    edgeCount G C.P C.Z = 13 ∧
      (∑ p ∈ C.P, epsilonAt G p C.s = 7) ∧
      ∃ T : Finset V, T ⊆ C.P ∧ T.card = 5 ∧
        (∀ p ∈ T, G.outdegree p = 8) ∧
        ∀ p ∈ T, ∀ u, G.Adj p u →
          7 ≤ (G.outNeighborFinsetOf (G.outNeighborFinset p |>.erase u) \
            ((G.outNeighborFinset p |>.erase u) ∪ {p})).card := by
  have hMissing := terminal_one_defect_forces_missing_Z G C hG hMin
    hNoSeymour hRootDegree hBCard hk hx hz hEpsilon hm
  obtain ⟨T, hTP, hTCard, hTDegree, hDeletion⟩ :=
    BSevenKOneTerminal.exists_degreeEightDeletionTail G hBound C hG hMin
      hNoSeymour hRootDegree hBCard hk hx hz hEpsilon
  refine ⟨hMissing.1, hMissing.2, T, hTP, ?_, hTDegree, hDeletion⟩
  omega

end SeymourEight.TerminalCoreGraphBridge
