import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Labels
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.GraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactLabels

set_option linter.style.header false

/-! Canonical labels for an almost-complete `P × Z` rectangle. -/

namespace SeymourEight.FourZExactSevenPZLabels

open FourZExactSeven FourZExactSevenBridge FourZExactSevenLabels FiveZExactLabels
  TerminalCoreGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem rows_four_of_total (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hPZ : edgeCount G C.P C.Z = 28) (u : V) (hu : u ∈ C.P) :
    directCount G C.Z u = 4 := by
  have huLe : directCount G C.Z u ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hRestLe : ∑ q ∈ C.P.erase u, directCount G C.Z q ≤ 24 := by
    calc
      _ ≤ ∑ _q ∈ C.P.erase u, 4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      _ = 24 := by simp [Finset.card_erase_of_mem hu, hPCard]
  have hSplit := Finset.sum_erase_add C.P (directCount G C.Z) hu
  change (∑ q ∈ C.P, directCount G C.Z q) = 28 at hPZ
  omega

private theorem exists_exceptional_row (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hPZ : edgeCount G C.P C.Z = 27) :
    ∃ u ∈ C.P, directCount G C.Z u = 3 ∧
      ∀ q ∈ C.P, q ≠ u → directCount G C.Z q = 4 := by
  have hEachLe : ∀ q ∈ C.P, directCount G C.Z q ≤ 4 := by
    intro q hq
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hSome : ∃ u ∈ C.P, directCount G C.Z u < 4 := by
    by_contra hn
    push Not at hn
    have hall : ∀ u ∈ C.P, directCount G C.Z u = 4 := by
      intro u hu
      exact Nat.le_antisymm (hEachLe u hu) (hn u hu)
    change (∑ q ∈ C.P, directCount G C.Z q) = 27 at hPZ
    have : (∑ q ∈ C.P, directCount G C.Z q) = 28 := by
      calc _ = ∑ _q ∈ C.P, 4 := Finset.sum_congr rfl hall
           _ = 28 := by simp [hPCard]
    omega
  obtain ⟨u, hu, huLt⟩ := hSome
  have hRestLe : ∑ q ∈ C.P.erase u, directCount G C.Z q ≤ 24 := by
    calc
      _ ≤ ∑ _q ∈ C.P.erase u, 4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact hEachLe q (Finset.mem_of_mem_erase hq)
      _ = 24 := by simp [Finset.card_erase_of_mem hu, hPCard]
  have hSplit := Finset.sum_erase_add C.P (directCount G C.Z) hu
  change (∑ q ∈ C.P, directCount G C.Z q) = 27 at hPZ
  have huThree : directCount G C.Z u = 3 := by omega
  refine ⟨u, hu, huThree, ?_⟩
  intro q hq hqu
  have hqLe := hEachLe q hq
  by_contra hne
  have hqThree : directCount G C.Z q ≤ 3 := by omega
  have hqErase : q ∈ C.P.erase u := Finset.mem_erase.mpr ⟨hqu, hq⟩
  have hOthers : ∑ t ∈ (C.P.erase u).erase q, directCount G C.Z t ≤ 20 := by
    calc
      _ ≤ ∑ _t ∈ (C.P.erase u).erase q, 4 := by
        apply Finset.sum_le_sum
        intro t ht
        exact hEachLe t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
      _ = 20 := by
        simp [Finset.card_erase_of_mem hqErase,
          Finset.card_erase_of_mem hu, hPCard]
  have hSplit2 := Finset.sum_erase_add (C.P.erase u)
    (directCount G C.Z) hqErase
  omega

structure Data (C : G.LocalConfiguration) (missing : Nat) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  z : Fin 4 ≃ {v : V // v ∈ C.Z}
  rows : ∀ i : Nat, (hi : i < 7) →
    directCount G C.Z (p ⟨i, hi⟩).1 =
      if missing = 1 ∧ i = 0 then 3 else 4
  pToZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
    (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
      FourZExactSeven.pToZ missing i j = true)
  sorted : ∀ (q : Nat)
      (hq : q < 6 - (if missing = 1 then 1 else 0)),
    let i := q + (if missing = 1 then 1 else 0)
    G.outdegree (p ⟨i + 1, by omega⟩).1 ≤
        G.outdegree (p ⟨i, by omega⟩).1 ∧
      (G.outdegree (p ⟨i, by omega⟩).1 =
          G.outdegree (p ⟨i + 1, by omega⟩).1 →
        directCount G C.H (p ⟨i + 1, by omega⟩).1 ≤
          directCount G C.H (p ⟨i, by omega⟩).1)

private theorem all_adj_of_row_four (C : G.LocalConfiguration)
    (hZCard : C.Z.card = 4) (u : V) (hRow : directCount G C.Z u = 4) :
    ∀ z ∈ C.Z, G.Adj u z := by
  intro v hv
  have heq : C.Z.filter (G.Adj u) = C.Z := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa [directCount, CertificateBridge.internalFirstNeighbors, hZCard]
      using hRow.symm.le
  have : v ∈ C.Z.filter (G.Adj u) := by rw [heq]; exact hv
  exact (Finset.mem_filter.mp this).2

/-- At density 28, arbitrary `Z` labels and the fully sorted `P` labels give
the exact implicit rectangle. -/
theorem exists_data_zero (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hHCard : C.H.card = 4) (hPZ : edgeCount G C.P C.Z = 28) :
    Nonempty (Data G C 0) := by
  let eP : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let p := sortedAllFinsetEquiv G.outdegree (directCount G C.H) C.P eP
  let z : Fin 4 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  have hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if 0 = 1 ∧ i = 0 then 3 else 4 := by
    intro i hi
    simp only [zero_ne_one, false_and, ↓reduceIte]
    exact rows_four_of_total G C hPCard hZCard hPZ _ (p ⟨i, hi⟩).2
  have hCountLt : ∀ v, directCount G C.H v < 256 := by
    intro v
    have := (Finset.card_le_card (Finset.filter_subset (G.Adj v) C.H)).trans_eq
      hHCard
    exact this.trans_lt (by omega)
  refine ⟨{ p := p, z := z, rows := hRows, pToZ := ?_, sorted := ?_ }⟩
  · intro i j hi hj
    have hadj := all_adj_of_row_four G C hZCard
      (p ⟨i, hi⟩).1 (by simpa using hRows i hi)
      (z ⟨j, hj⟩).1 (z ⟨j, hj⟩).2
    simp [FourZExactSeven.pToZ, hadj]
  · intro q hq
    simpa [p] using sortedAllFinsetEquiv_order G.outdegree (directCount G C.H)
      C.P eP hCountLt q (by simpa using hq)

/-- At density 27, choose the unique deficient row as `p0`, its unique
missing target as `z0`, and sort the remaining six `P` labels. -/
theorem exists_data_one (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hHCard : C.H.card = 4) (hPZ : edgeCount G C.P C.Z = 27) :
    Nonempty (Data G C 1) := by
  obtain ⟨u, huP, huThree, huUnique⟩ :=
    exists_exceptional_row G C hPCard hZCard hPZ
  let T := C.Z \ C.Z.filter (G.Adj u)
  have hTCard : T.card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _),
      hZCard]
    change (C.Z.filter (G.Adj u)).card = 3 at huThree
    omega
  obtain ⟨v, hT⟩ := Finset.card_eq_one.mp hTCard
  have hvT : v ∈ T := by simp [hT]
  have hvZ : v ∈ C.Z := (Finset.mem_sdiff.mp hvT).1
  have huv : ¬G.Adj u v := by
    intro huv
    exact (Finset.mem_sdiff.mp hvT).2 (Finset.mem_filter.mpr ⟨hvZ, huv⟩)
  let eP := TerminalCoreGraphBridge.finsetEquivFinAtZero C.P hPCard u huP
  let p := sortedFinsetEquiv G.outdegree (directCount G C.H) C.P eP
  have hp0 : (p 0).1 = u := by
    calc
      (p 0).1 = (eP 0).1 := by rfl
      _ = u := TerminalCoreGraphBridge.finsetEquivFinAtZero_zero
        C.P hPCard u huP
  let z := FiveZExactLabels.finsetEquivFinAtZero C.Z (by omega) hZCard v hvZ
  have hz0 : (z 0).1 = v :=
    FiveZExactLabels.finsetEquivFinAtZero_zero C.Z (by omega) hZCard v hvZ
  have hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if 1 = 1 ∧ i = 0 then 3 else 4 := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa [hp0] using huThree
    · rw [if_neg (by simp [hi0])]
      apply huUnique _ (p ⟨i, hi⟩).2
      intro heq
      have : (p ⟨i, hi⟩).1 = (p 0).1 := by simpa [hp0] using heq
      exact hi0 (Fin.ext_iff.mp (p.injective (Subtype.ext this)))
  have hCountLt : ∀ x, directCount G C.H x < 256 := by
    intro x
    have := (Finset.card_le_card (Finset.filter_subset (G.Adj x) C.H)).trans_eq
      hHCard
    exact this.trans_lt (by omega)
  refine ⟨{ p := p, z := z, rows := hRows, pToZ := ?_, sorted := ?_ }⟩
  · intro i j hi hj
    by_cases hi0 : i = 0
    · subst i
      by_cases hj0 : j = 0
      · subst j
        simp [FourZExactSeven.pToZ, hp0, hz0, huv]
      · have hzNe : (z ⟨j, hj⟩).1 ≠ v := by
          intro heq
          have hzEq : z ⟨j, hj⟩ = z 0 := Subtype.ext (by simpa [hz0] using heq)
          exact hj0 (Fin.ext_iff.mp (z.injective hzEq))
        have hzNotT : (z ⟨j, hj⟩).1 ∉ T := by simp [hT, hzNe]
        have hAdj : G.Adj u (z ⟨j, hj⟩).1 := by
          by_contra hn
          apply hzNotT
          exact Finset.mem_sdiff.mpr ⟨(z ⟨j, hj⟩).2,
            fun hm ↦ hn (Finset.mem_filter.mp hm).2⟩
        simp [FourZExactSeven.pToZ, hp0, hj0, hAdj]
    · have hpu : (p ⟨i, hi⟩).1 ≠ u := by
        intro heq
        have hpEq : p ⟨i, hi⟩ = p 0 := Subtype.ext (by simpa [hp0] using heq)
        exact hi0 (Fin.ext_iff.mp (p.injective hpEq))
      have hFour := huUnique _ (p ⟨i, hi⟩).2 hpu
      have hAdj := all_adj_of_row_four G C hZCard _ hFour
        (z ⟨j, hj⟩).1 (z ⟨j, hj⟩).2
      simp [FourZExactSeven.pToZ, hi0, hAdj]
  · intro q hq
    simpa [p] using sortedTailFinsetEquiv_order G.outdegree (directCount G C.H)
      C.P eP hCountLt q (by simpa using hq)

/-- Orientation turns the implicit `P → Z` rectangle into the exact
exceptional `Z → P` predicate used by the finite core. -/
theorem zToP_iff_exceptional (C : G.LocalConfiguration) (hG : G.IsOriented)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) (a : Fin 8 → V) (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 → V)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true)) :
    ∀ i j : Nat, (hi : i < 4) → (hj : j < 7) →
      (G.Adj (z ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 ↔
        exceptionalZToP missing (coreBits G.Adj (fun q ↦ (p q).1) h a
          (fun q ↦ (z q).1) w) i j = true) := by
  intro i j hi hj
  rw [exceptionalZToP, z0ToP0_coreBits]
  by_cases hex : missing = 1 ∧ i = 0 ∧ j = 0
  · rcases hex with ⟨hm, rfl, rfl⟩
    simp [hm]
  · have hDirect : G.Adj (p ⟨j, hj⟩).1 (z ⟨i, hi⟩).1 := by
      apply (hPZ j i hj hi).2
      simp only [FourZExactSeven.pToZ, Bool.not_eq_true', decide_eq_false_iff_not]
      intro hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      exact hex ⟨hs.1.1, hs.2, hs.1.2⟩
    have hReverse := hG.2 hDirect
    constructor
    · intro hbad
      exact (hReverse hbad).elim
    · intro hrhs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrhs
      rcases hrhs with ⟨⟨⟨hm, hi0⟩, hj0⟩, _⟩
      exact (hex ⟨hm, hi0, hj0⟩).elim

end SeymourEight.FourZExactSevenPZLabels
