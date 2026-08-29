import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.Encoding
import SeymourEight.Cases.BSevenKTwo.RSix.XThreeNoRoot.Assembly
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective
import SeymourEight.Cases.BSevenKTwo.Counting
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.GraphBridge

open Shared Shared.FiniteCore CertificateBridge
open Labels Encoding Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private noncomputable def finsetEquivAtZero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    Fin n ≃ {w : V // w ∈ S} :=
  let e := finsetEquivFin S hCard
  (Equiv.swap ⟨0, hn⟩ (e.symm ⟨v, hv⟩)).trans e

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem finsetEquivAtZero_zero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    (finsetEquivAtZero S hn hCard v hv ⟨0, hn⟩).1 = v := by
  classical
  simp [finsetEquivAtZero]

/-- One `A₁` vertex has no outneighbor in `A₁`; minimality then forces its
two internal outneighbors to be precisely the two vertices of `X`. -/
theorem exists_distinguished_aOne (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 2) (hx : C.x = 2) :
    ∃ u ∈ C.A1, Shared.directCount G C.A u = 2 ∧
      Shared.directCount G C.A1 u = 0 ∧ ∀ x ∈ C.X, G.Adj u x := by
  have hAOneCard : C.A1.card = 2 := hk
  have hXCard : C.X.card = 2 := hx
  have hInternal := internal_edgeCount_le_choose_two G C.A1 hG
  rw [hAOneCard] at hInternal
  norm_num [Nat.choose] at hInternal
  have hZero : ∃ u ∈ C.A1, Shared.directCount G C.A1 u = 0 := by
    by_contra hn
    push Not at hn
    have hTwo : 2 ≤ edgeCount G C.A1 C.A1 := by
      unfold edgeCount
      calc
        2 = ∑ _u ∈ C.A1, 1 := by simp [hAOneCard]
        _ ≤ ∑ u ∈ C.A1, Shared.directCount G C.A1 u := by
          apply Finset.sum_le_sum
          intro u hu
          have := hn u hu
          omega
    omega
  obtain ⟨u, huAOne, huZero⟩ := hZero
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.A1_subset_A (G := G) C huAOne
  have hMinA : 2 ≤ Shared.directCount G C.A u := by
    simpa [Shared.directCount, internalFirstNeighbors, hk] using
      (hPivot u huA).1
  have hSubset := BSixKThree.A1_A_neighbors_subset_H G C hG u huAOne
  have hAH : Shared.directCount G C.A u ≤ Shared.directCount G C.H u :=
    Finset.card_le_card hSubset
  have hSplit : Shared.directCount G C.H u =
      Shared.directCount G C.A1 u + Shared.directCount G C.X u := by
    exact directCount_union_of_disjoint G C.A1 C.X u
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hXUpper : Shared.directCount G C.X u ≤ 2 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hXCard
  have hXEq : Shared.directCount G C.X u = 2 := by omega
  have hAEq : Shared.directCount G C.A u = 2 := by omega
  refine ⟨u, huAOne, hAEq, huZero, ?_⟩
  intro x hxMem
  have hFilterEq : C.X.filter (G.Adj u) = C.X := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa [Shared.directCount, internalFirstNeighbors, hXCard] using
      (Nat.le_of_eq hXEq.symm)
  exact (Finset.mem_filter.mp (hFilterEq.symm ▸ hxMem)).2

private abbrev graphBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) : Core.Encoding := Encoding.coreBits G.Adj L

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

noncomputable def hEquiv (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hHCard : C.H.card = 4) :
    Fin 4 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 4 → {v : V // v ∈ C.H} := fun i =>
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, by
      by_cases hi : i.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi⟩)
      · exact Finset.mem_union_right C.A1 (by
          simpa [show i.val - 2 + 3 = i.val + 1 by omega] using
            L.a_x ⟨i.val - 2, by omega⟩)⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have haval : i.val + 1 = j.val + 1 := Fin.ext_iff.mp ha
    omega
  · simpa using hHCard.symm

@[simp] theorem hEquiv_val (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hHCard : C.H.card = 4) (i : Fin 4) :
    (hEquiv G C q L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

noncomputable def aOneEquiv (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hk : C.k = 2) :
    Fin 2 ≃ {v : V // v ∈ C.A1} := by
  let f : Fin 2 → {v : V // v ∈ C.A1} := fun i =>
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, L.a_aOne i⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    have hval : i.val + 1 = j.val + 1 := Fin.ext_iff.mp ha
    omega
  · change C.A1.card = 2 at hk
    simpa using hk.symm

@[simp] theorem aOneEquiv_val (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hk : C.k = 2) (i : Fin 2) :
    (aOneEquiv G C q L hk i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

theorem orientedP_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented) :
    orientedP (graphBits G L) = true := by
  rw [orientedP, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  rw [pArc_coreBits G.Adj L i j hi hj,
    pArc_coreBits G.Adj L j i hj hi]
  by_cases hij : i = j
  · simp [hij]
  · by_cases h : G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1
    · simp [hij, h, hG.2 h]
    · simp [hij, h]

theorem orientedPH_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented) :
    orientedPH (graphBits G L) = true := by
  rw [orientedPH, all_eq_true_iff]
  intro p hp
  rw [all_eq_true_iff]
  intro h hh
  rw [pToH_coreBits G.Adj L p h hp hh,
    hToP_coreBits G.Adj L h p hh hp]
  by_cases ha : G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1
  · simp [ha, hG.2 ha]
  · simp [ha]

theorem orientedHH_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented) :
    orientedHH (graphBits G L) = true := by
  rw [orientedHH, all_eq_true_iff]
  intro h hh
  rw [Bool.and_eq_true, all_eq_true_iff]
  constructor
  · rw [hArc, aArc_coreBits G.Adj L (1 + h) (1 + h) (by omega) (by omega)]
    simpa using hG.1 (L.a ⟨1 + h, by omega⟩).1
  · intro k hk
    rw [hArc, hArc,
      aArc_coreBits G.Adj L (1 + h) (1 + k) (by omega) (by omega),
      aArc_coreBits G.Adj L (1 + k) (1 + h) (by omega) (by omega)]
    by_cases hhk : h = k
    · simp [hhk]
    · by_cases ha : G.Adj (L.a ⟨1 + h, by omega⟩).1
          (L.a ⟨1 + k, by omega⟩).1
      · simp [hhk, ha, hG.2 ha]
      · simp [hhk, ha]

theorem fixedA_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (_hG : G.IsOriented) :
    fixedA (graphBits G L) = true := by
  let bits := graphBits G L
  have h01 : aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj L 0 1 (by omega) (by omega)]
    exact decide_eq_true (by
      have ha0 : (⟨0, by omega⟩ : Fin 8) = 0 := rfl
      rw [ha0, L.a_zero]
      simpa using (Finset.mem_filter.mp (L.a_aOne 0)).2)
  have h02 : aArc bits 0 2 = true := by
    rw [aArc_coreBits G.Adj L 0 2 (by omega) (by omega)]
    exact decide_eq_true (by
      have ha0 : (⟨0, by omega⟩ : Fin 8) = 0 := rfl
      rw [ha0, L.a_zero]
      simpa using (Finset.mem_filter.mp (L.a_aOne 1)).2)
  have hTail : all 5 (fun i => !aArc bits 0 (3 + i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [aArc_coreBits G.Adj L 0 (3 + i) (by omega) (by omega)]
    have ha0 : (⟨0, by omega⟩ : Fin 8) = 0 := rfl
    rw [ha0, L.a_zero]
    by_cases hi2 : i < 2
    · have hx := L.a_x ⟨i, hi2⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
          (Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩)
          (by simpa [Nat.add_comm] using hx)
      simp [hn]
    · have hr := L.a_r ⟨i - 2, by omega⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        exact (Finset.mem_sdiff.mp hr).2 (by
          simpa [show i - 2 + 5 = 3 + i by omega] using
            Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
      simp [hn]
  have hA1R : all 6 (fun k =>
      !aArc bits (1 + k / 3) (5 + k % 3)) = true := by
    rw [all_eq_true_iff]
    intro k hk
    rw [aArc_coreBits G.Adj L (1 + k / 3) (5 + k % 3)
      (by omega) (by omega)]
    have hn := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
      G C (L.a ⟨1 + k / 3, by omega⟩).1
      (L.a ⟨5 + k % 3, by omega⟩).1
      (by simpa [Nat.add_comm] using L.a_aOne ⟨k / 3, by omega⟩)
      (by simpa [Nat.add_comm] using L.a_r ⟨k % 3, by omega⟩)
    simpa using decide_eq_false hn
  simp only [fixedA, Bool.and_eq_true]
  exact ⟨⟨⟨h01, h02⟩, hTail⟩, hA1R⟩

theorem aOne_not_to_pivot_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented) :
    all 2 (fun a => !aArc (graphBits G L) (1 + a) 0) = true := by
  rw [all_eq_true_iff]
  intro a ha
  rw [aArc_coreBits G.Adj L (1 + a) 0 (by omega) (by omega)]
  have hpivot : G.Adj (L.a 0).1 (L.a ⟨1 + a, by omega⟩).1 := by
    rw [L.a_zero]
    simpa [Nat.add_comm] using (Finset.mem_filter.mp (L.a_aOne ⟨a, ha⟩)).2
  simpa using decide_eq_false (hG.2 hpivot)

theorem hIrreflexive_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented) :
    all 4 (fun h => !hArc (graphBits G L) h h) = true := by
  rw [all_eq_true_iff]
  intro h hh
  rw [hArc, aArc_coreBits G.Adj L (1 + h) (1 + h) (by omega) (by omega)]
  simpa using decide_eq_false (hG.1 (L.a ⟨1 + h, by omega⟩).1)

theorem pBlockCounts {eCount : Nat} (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hHCard : C.H.card = 4) (E : Finset V)
    (eEq : Fin eCount ≃ {v : V // v ∈ E})
    (heBound : eCount ≤ 5)
    (hELab : ∀ i : Fin eCount,
      L.e ⟨i.val, lt_of_lt_of_le i.isLt heBound⟩ = (eEq i).1)
    (p : Nat) (hp : p < 6) :
    (pOut (graphBits G L) p).toNat =
        Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ∧
    (pHOut (graphBits G L) p).toNat =
        Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ∧
    (pEOut eCount (graphBits G L) p).toNat =
        Shared.directCount G E (L.p ⟨p, hp⟩).1 := by
  constructor
  · rw [pOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P L.p _
    intro j
    rw [pArc_coreBits G.Adj L p j hp j.isLt]
    by_cases hpj : p = j.val
    · have he : (⟨p, hp⟩ : Fin 6) = j := Fin.ext hpj
      simp [hpj, hG.1 (L.p j).1]
    · simp [hpj]
  constructor
  · rw [pHOut, toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H (hEquiv G C q L hHCard) _
    intro j
    rw [pToH_coreBits G.Adj L p j hp j.isLt]
    simp
  · rw [pEOut, toNat_count_eq_fin_sum eCount _ (by omega)]
    symm
    apply directCount_eq_sum_bool G E eEq _
    intro j
    rw [pToE_coreBits G.Adj L p j hp (by omega), hELab]
    simp

theorem hPOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (h : Nat) (hh : h < 4) :
    (hPOut (graphBits G L) h).toNat =
      Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1 := by
  rw [hPOut, toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [hToP_coreBits G.Adj L h j hh j.isLt]
  simp

theorem totalPToH_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hHCard : C.H.card = 4) :
    (totalPToH (graphBits G L)).toNat = edgeCount G C.P C.H := by
  rw [totalPToH, toNat_sumCount]
  have hEach : ∀ i : Fin 6, (pHOut (graphBits G L) i).toNat =
      Shared.directCount G C.H (L.p i).1 := by
    intro i
    rw [pHOut, toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H (hEquiv G C q L hHCard) _
    intro j
    rw [pToH_coreBits G.Adj L i j i.isLt j.isLt]
    simp
  have hSum : (∑ i ∈ Finset.range 6, (pHOut (graphBits G L) i).toNat) =
      edgeCount G C.P C.H := by
    rw [edgeCount_eq_sum_fin G C.P C.H L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hp, hHCard] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem totalHToP_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hHCard : C.H.card = 4) :
    (totalHToP (graphBits G L)).toNat = edgeCount G C.H C.P := by
  rw [totalHToP, toNat_sumCount]
  have hEach : ∀ i : Fin 4, (hPOut (graphBits G L) i).toNat =
      Shared.directCount G C.P (L.a ⟨i.val + 1, by omega⟩).1 := by
    intro i
    exact hPOut_toNat G C q L i i.isLt
  have hSum : (∑ i ∈ Finset.range 4, (hPOut (graphBits G L) i).toNat) =
      edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hEquiv G C q L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simpa using hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hp] at hCap
  exact Nat.mod_eq_of_lt (by omega)

def structuralTargets (C : G.LocalConfiguration) : Finset V := {C.a1} ∪ C.R

noncomputable def structuralEquiv (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hRCard : C.R.card = 3) :
    Fin 4 ≃ {v : V // v ∈ structuralTargets G C} := by
  let f : Fin 4 → {v : V // v ∈ structuralTargets G C} := fun i =>
    if hi : i.val = 0 then
      ⟨C.a1, Finset.mem_union_left C.R (Finset.mem_singleton_self _)⟩
    else
      ⟨(L.a ⟨i.val + 4, by omega⟩).1,
        Finset.mem_union_right {C.a1} (by
          simpa [show i.val - 1 + 5 = i.val + 4 by omega] using
            L.a_r ⟨i.val - 1, by omega⟩)⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · apply Fin.ext; omega
      · exfalso
        have hiFin : i = 0 := Fin.ext hi
        have hjFin : j ≠ 0 := by intro h; exact hj (congrArg Fin.val h)
        have heq : C.a1 = (L.a ⟨j.val + 4, by omega⟩).1 := by
          simpa [f, hiFin, hjFin] using congrArg Subtype.val hij
        have hjR : (L.a ⟨j.val + 4, by omega⟩).1 ∈ C.R := by
          simpa [show j.val - 1 + 5 = j.val + 4 by omega] using
            L.a_r ⟨j.val - 1, by omega⟩
        rw [← heq] at hjR
        exact (Finset.mem_sdiff.mp hjR).2
          (Finset.mem_union_right (C.A1 ∪ C.X)
            (Finset.mem_singleton_self C.a1))
    · by_cases hj : j.val = 0
      · exfalso
        have hiFin : i ≠ 0 := by intro h; exact hi (congrArg Fin.val h)
        have hjFin : j = 0 := Fin.ext hj
        have heq : (L.a ⟨i.val + 4, by omega⟩).1 = C.a1 := by
          simpa [f, hiFin, hjFin] using congrArg Subtype.val hij
        have hiR : (L.a ⟨i.val + 4, by omega⟩).1 ∈ C.R := by
          simpa [show i.val - 1 + 5 = i.val + 4 by omega] using
            L.a_r ⟨i.val - 1, by omega⟩
        rw [heq] at hiR
        exact (Finset.mem_sdiff.mp hiR).2
          (Finset.mem_union_right (C.A1 ∪ C.X)
            (Finset.mem_singleton_self C.a1))
      · have ha : L.a ⟨i.val + 4, by omega⟩ =
            L.a ⟨j.val + 4, by omega⟩ := by
          have hiFin : i ≠ 0 := by intro h; exact hi (congrArg Fin.val h)
          have hjFin : j ≠ 0 := by intro h; exact hj (congrArg Fin.val h)
          apply Subtype.ext
          simpa [f, hiFin, hjFin] using congrArg Subtype.val hij
        have hval : i.val + 4 = j.val + 4 :=
          Fin.ext_iff.mp (L.a.injective ha)
        apply Fin.ext
        omega
  · have hDis : Disjoint ({C.a1} : Finset V) C.R := by
      rw [Finset.disjoint_left]
      intro v hva1 hvR
      have hv : v = C.a1 := Finset.mem_singleton.mp hva1
      subst v
      exact (Finset.mem_sdiff.mp hvR).2 (by
        exact Finset.mem_union_right (C.A1 ∪ C.X)
          (Finset.mem_singleton_self C.a1))
    rw [show Fintype.card {v : V // v ∈ structuralTargets G C} =
        (structuralTargets G C).card by simp,
      structuralTargets, Finset.card_union_of_disjoint hDis]
    simp [hRCard]

@[simp] theorem structuralEquiv_zero (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hRCard : C.R.card = 3) :
    (structuralEquiv G C q L hRCard 0).1 = C.a1 := by
  simp [structuralEquiv]

@[simp] theorem structuralEquiv_succ (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hRCard : C.R.card = 3) (i : Fin 3) :
    (structuralEquiv G C q L hRCard ⟨i.val + 1, by omega⟩).1 =
      (L.a ⟨i.val + 5, by omega⟩).1 := by
  simp [structuralEquiv, show (⟨i.val + 1, by omega⟩ : Fin 4) ≠ 0 by
    intro h; have := congrArg Fin.val h; simp at this]

theorem xToTCount_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hRCard : C.R.card = 3)
    (x : Nat) (hx : x < 2) :
    (count 4 (xToT (graphBits G L) x)).toNat =
      Shared.directCount G (structuralTargets G C)
        (L.a ⟨x + 3, by omega⟩).1 := by
  rw [toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (structuralTargets G C)
    (structuralEquiv G C q L hRCard) _
  intro t
  rw [xToT, aArc_coreBits G.Adj L (3 + x)
    (if t.val = 0 then 0 else 4 + t.val) (by omega) (by
      split <;> omega)]
  by_cases ht : t.val = 0
  · have ht0 : t = 0 := Fin.ext ht
    simp [ht0, L.a_zero, Nat.add_comm]
  · have htPos : 0 < t.val := by omega
    let i : Fin 3 := ⟨t.val - 1, by omega⟩
    have htEq : t = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [htEq, structuralEquiv_succ]
    rw [decide_eq_true_eq]
    have hiNZ : i.val + 1 ≠ 0 := by omega
    simp only [if_neg hiNZ]
    have hs : (L.a ⟨3 + x, by omega⟩).1 =
        (L.a ⟨x + 3, by omega⟩).1 := by
      apply congrArg Subtype.val
      apply congrArg L.a
      apply Fin.ext
      simp
      omega
    have htarget : (L.a ⟨4 + (i.val + 1), by omega⟩).1 =
        (L.a ⟨i.val + 5, by omega⟩).1 := by
      apply congrArg Subtype.val
      apply congrArg L.a
      apply Fin.ext
      simp
      omega
    rw [hs, htarget]

set_option linter.flexible false in
theorem hArcCount_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hHCard : C.H.card = 4)
    (h : Nat) (hh : h < 4) :
    (count 4 (hArc (graphBits G L) h)).toNat =
      Shared.directCount G C.H (L.a ⟨h + 1, by omega⟩).1 := by
  rw [toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H (hEquiv G C q L hHCard) _
  intro k
  rw [hArc, aArc_coreBits G.Adj L (1 + h) (1 + k) (by omega) (by omega)]
  simp
  have hs : (L.a ⟨1 + h, by omega⟩).1 =
      (L.a ⟨h + 1, by omega⟩).1 := by
    apply congrArg Subtype.val
    apply congrArg L.a
    apply Fin.ext
    simp
    omega
  have ht : (L.a ⟨1 + k.val, by omega⟩).1 =
      (L.a ⟨k.val + 1, by omega⟩).1 := by
    apply congrArg Subtype.val
    apply congrArg L.a
    apply Fin.ext
    simp
    omega
  rw [hs, ht]

theorem hToQCount_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (h : Nat) (hh : h < 4) :
    (bitCount (hToQCore 0 (graphBits G L) h)).toNat =
      Shared.directCount G {q} (L.a ⟨h + 1, by omega⟩).1 := by
  rw [hToQCore, aToQ_coreBits G.Adj L (1 + h) (by omega)]
  unfold Shared.directCount internalFirstNeighbors
  rw [Finset.filter_singleton]
  have hs : (L.a ⟨1 + h, by omega⟩).1 =
      (L.a ⟨h + 1, by omega⟩).1 := by
    apply congrArg Subtype.val
    apply congrArg L.a
    apply Fin.ext
    simp
    omega
  rw [hs]
  by_cases ha : G.Adj (L.a ⟨h + 1, by omega⟩).1 q <;>
    simp [bitCount, ha]

theorem hDirectCore_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hRCard : C.R.card = 3) (h : Nat) (hh : h < 4) :
    (hDirectCore 0 (graphBits G L) h).toNat =
      G.outdegree (L.a ⟨h + 1, by omega⟩).1 := by
  let u := (L.a ⟨h + 1, by omega⟩).1
  have huH : u ∈ C.H := (hEquiv G C q L hHCard ⟨h, hh⟩).2
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.H_subset_A (G := G) C huH
  have hAB := RSix.XThreeNoRoot.Assembly.A_outdegree_eq_A_add_B
    G C hG u huA
  have hHT : C.H ∪ structuralTargets G C = C.A := by
    simpa [Digraph.LocalConfiguration.H, structuralTargets,
      Finset.union_assoc] using
      Digraph.LocalConfiguration.local_parts_union_R (G := G) C
  have hDisHT : Disjoint C.H (structuralTargets G C) := by
    change Disjoint C.H (BSixKTwoCoreGraphBridge.protectedTargets G C)
    exact BSixKTwoCoreGraphBridge.disjoint_H_protectedTargets G C hG
  have hDisPQ : Disjoint C.P {q} := by
    rw [Finset.disjoint_left]
    intro v hvP hvq
    have hv : v = q := Finset.mem_singleton.mp hvq
    subst v
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hqQ
  have hB : C.P ∪ {q} = C.B := by
    rw [← hQ]
    exact Digraph.LocalConfiguration.P_union_Q (G := G) C
  rw [← hHT,
    directCount_union_of_disjoint G C.H (structuralTargets G C) u hDisHT,
    ← hB, directCount_union_of_disjoint G C.P {q} u hDisPQ] at hAB
  have hH := hArcCount_toNat G C q L hHCard h hh
  have hP := hPOut_toNat G C q L h hh
  have hq := hToQCount_toNat G C q L h hh
  dsimp [u] at *
  by_cases ha : h < 2
  · have huAOne : u ∈ C.A1 := by
      simpa [u, Nat.add_comm] using L.a_aOne ⟨h, ha⟩
    have hTZero := BSixKTwoCoreGraphBridge.directCount_protected_eq_zero_of_mem_A1
      G C hG u huAOne
    have hTZero' : Shared.directCount G (structuralTargets G C) u = 0 := by
      change Shared.directCount G (BSixKTwoCoreGraphBridge.protectedTargets G C) u = 0
      exact hTZero
    simp only [hDirectCore, BitVec.toNat_add, if_pos ha]
    norm_num [BitVec.toNat_ofNat]
    rw [hH, hP, hq]
    norm_num [BitVec.toNat_ofNat]
    have hSmall : Shared.directCount G C.H u + Shared.directCount G C.P u +
        Shared.directCount G {q} u < 256 := by
      have h1 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) C.H)
      have h2 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) C.P)
      have h3 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) ({q} : Finset V))
      have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
      change Shared.directCount G C.H u ≤ C.H.card at h1
      change Shared.directCount G C.P u ≤ C.P.card at h2
      change Shared.directCount G {q} u ≤ ({q} : Finset V).card at h3
      have h3' : Shared.directCount G {q} u ≤ 1 := by
        simpa only [Finset.card_singleton] using h3
      rw [hHCard] at h1
      rw [hp] at h2
      omega
    rw [← directCount_singleton]
    have hZero : (0 : BitVec 8).toNat = 0 := by decide
    rw [hZero, Nat.add_zero]
    dsimp [u] at hSmall hAB hTZero'
    rw [Nat.mod_eq_of_lt hSmall]
    omega
  · have hxIndex : h - 2 < 2 := by omega
    have hT := xToTCount_toNat G C q L hRCard (h - 2) hxIndex
    have huEq : (L.a ⟨h - 2 + 3, by omega⟩).1 = u := by
      dsimp [u]
      apply congrArg Subtype.val
      apply congrArg L.a
      apply Fin.ext
      simp
      omega
    rw [huEq] at hT
    dsimp [u] at hT
    simp only [hDirectCore, BitVec.toNat_add, if_neg ha]
    have hSmall : Shared.directCount G C.H u + Shared.directCount G C.P u +
        Shared.directCount G {q} u +
        Shared.directCount G (structuralTargets G C) u < 256 := by
      have h1 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) C.H)
      have h2 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) C.P)
      have h3 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) ({q} : Finset V))
      have h4 := Finset.card_le_card
        (Finset.filter_subset (G.Adj u) (structuralTargets G C))
      have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
      have htCard : (structuralTargets G C).card = 4 := by
        simpa using (Fintype.card_congr (structuralEquiv G C q L hRCard)).symm
      change Shared.directCount G C.H u ≤ C.H.card at h1
      change Shared.directCount G C.P u ≤ C.P.card at h2
      change Shared.directCount G {q} u ≤ ({q} : Finset V).card at h3
      change Shared.directCount G (structuralTargets G C) u ≤
        (structuralTargets G C).card at h4
      rw [hHCard] at h1
      rw [hp] at h2
      have h3' : Shared.directCount G {q} u ≤ 1 := by
        simpa only [Finset.card_singleton] using h3
      rw [htCard] at h4
      omega
    dsimp [u] at hH hP hq hT hAB hSmall ⊢
    rw [hH, hP, hq, hT]
    norm_num [BitVec.toNat_ofNat]
    rw [← directCount_singleton, Nat.mod_eq_of_lt hSmall]
    omega

theorem aOneMinimum_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hHCard : C.H.card = 4) (hk : C.k = 2) (hr : C.r = 6) :
    all 2 (fun a => (2 : BitVec 8).ule
        (count 4 (hArc (graphBits G L) a)) &&
      (!(count 4 (hArc (graphBits G L) a) == 2) ||
        (6 : BitVec 8).ule
          (hPOut (graphBits G L) a +
            bitCount (hToQCore 0 (graphBits G L) a)))) = true := by
  rw [all_eq_true_iff]
  intro a ha
  let u := (L.a ⟨a + 1, by omega⟩).1
  have huAOne : u ∈ C.A1 := by
    simpa [u, Nat.add_comm] using L.a_aOne ⟨a, ha⟩
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.A1_subset_A (G := G) C huAOne
  have hAH := BSixKThree.A1_A_neighbors_subset_H G C hG u huAOne
  have hCountA : Shared.directCount G C.A u = Shared.directCount G C.H u := by
    apply Nat.le_antisymm
    · exact Finset.card_le_card hAH
    · apply Finset.card_le_card
      intro v hv
      have hvH := (Finset.mem_filter.mp hv).1
      exact Finset.mem_filter.mpr
        ⟨Digraph.LocalConfiguration.H_subset_A (G := G) C hvH,
          (Finset.mem_filter.mp hv).2⟩
  have hHCount := hArcCount_toNat G C q L hHCard a (by omega)
  have hPCount := hPOut_toNat G C q L a (by omega)
  have hQCount := hToQCount_toNat G C q L a (by omega)
  have hPivotU := hPivot u huA
  have hDisPQ : Disjoint C.P {q} := by
    rw [Finset.disjoint_left]
    intro v hvP hvq
    have hv : v = q := Finset.mem_singleton.mp hvq
    subst v
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hqQ
  have hB : C.P ∪ {q} = C.B := by
    rw [← hQ]
    exact Digraph.LocalConfiguration.P_union_Q (G := G) C
  have hBCount : Shared.directCount G C.B u =
      Shared.directCount G C.P u + Shared.directCount G {q} u := by
    rw [← hB, directCount_union_of_disjoint G C.P {q} u hDisPQ]
  rw [Bool.and_eq_true]
  constructor
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHCount, ← hCountA]
    simpa [Shared.directCount, internalFirstNeighbors, hk] using hPivotU.1
  · rw [Bool.or_eq_true]
    by_cases heq : count 4 (hArc (graphBits G L) a) = 2
    · right
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
      have hNatural : 6 ≤ Shared.directCount G C.P u +
          Shared.directCount G {q} u := by
        rw [← hBCount]
        have hHExact : Shared.directCount G C.H u = 2 := by
          dsimp [u]
          rw [← hHCount]
          simpa using congrArg BitVec.toNat heq
        have hAExact : Shared.directCount G C.A u = 2 := by
          rw [hCountA, hHExact]
        have hTie := hPivotU.2 (by
          simpa [Shared.directCount, internalFirstNeighbors, hk] using hAExact)
        simpa [Shared.directCount, internalFirstNeighbors, hr] using hTie
      rw [hPCount, hQCount]
      have hSmall : Shared.directCount G C.P u +
          Shared.directCount G {q} u < 256 := by
        have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
        have h1 := Finset.card_le_card
          (Finset.filter_subset (G.Adj u) C.P)
        have h2 := Finset.card_le_card
          (Finset.filter_subset (G.Adj u) ({q} : Finset V))
        change Shared.directCount G C.P u ≤ C.P.card at h1
        change Shared.directCount G {q} u ≤ ({q} : Finset V).card at h2
        rw [hp] at h1
        have h2' : Shared.directCount G {q} u ≤ 1 := by
          simpa only [Finset.card_singleton] using h2
        omega
      rw [Nat.mod_eq_of_lt hSmall]
      exact hNatural
    · left
      simpa using heq

theorem hMinimum_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 4) (hRCard : C.R.card = 3) :
    all 4 (fun h => (8 : BitVec 8).ule
      (hDirectCore 0 (graphBits G L) h)) = true := by
  rw [all_eq_true_iff]
  intro h hh
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hDirectCore_toNat G C q hqQ hQ L hG hHCard hRCard h hh]
  exact hMin _

theorem distinguishedAOne_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hZero : Shared.directCount G C.A1 (L.a 1).1 = 0)
    (hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x) :
    distinguishedAOne (graphBits G L) = true := by
  have h00 : ¬G.Adj (L.a 1).1 (L.a 1).1 := hG.1 _
  have h01 : ¬G.Adj (L.a 1).1 (L.a 2).1 := by
    intro h
    have hp : 0 < Shared.directCount G C.A1 (L.a 1).1 := by
      unfold Shared.directCount internalFirstNeighbors
      apply Finset.card_pos.mpr
      exact ⟨(L.a 2).1, Finset.mem_filter.mpr ⟨L.a_aOne 1, h⟩⟩
    omega
  have h02 : G.Adj (L.a 1).1 (L.a 3).1 := hX _ (L.a_x 0)
  have h03 : G.Adj (L.a 1).1 (L.a 4).1 := hX _ (L.a_x 1)
  simp [distinguishedAOne, hArc, count, bitCount, aArc_coreBits,
    h00, h01, h02, h03]

theorem everyXReached_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hk : C.k = 2) :
    everyXReached (graphBits G L) = true := by
  rw [everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := (aOneEquiv G C q L hk).surjective ⟨u, huA1⟩
    refine ⟨i.val, i.isLt, ?_⟩
    rw [aArc_coreBits G.Adj L (1 + i.val) (3 + x) (by omega) (by omega)]
    have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u :=
      congrArg Subtype.val hi
    simpa [Nat.add_comm, hiVal] using hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨i.val, i.isLt, ?_⟩
    rw [pToH_coreBits G.Adj L i (2 + x) i.isLt (by omega)]
    have hiVal : (L.p i).1 = u := congrArg Subtype.val hi
    simpa [Nat.add_comm, Nat.add_left_comm, hiVal] using hux

theorem qStructureReached_true (C : G.LocalConfiguration) (q : V)
    (_hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (heZero : L.e 0 = q)
    (hy : BSevenKTwo.y G C = 1) (c : Nat)
    (hc : edgeCount G C.A1 {q} = c) :
    ((decide (0 < c)) || any 6 (fun p => pToE (graphBits G L) p 0) ||
      any 2 (fun x => hToQCore c (graphBits G L) (2 + x))) = true := by
  by_cases hcPos : 0 < c
  · simp [hcPos]
  have hcZero : c = 0 := by omega
  have hReachedCard : (reachedQ G C).card = 1 := hy
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
  have hwQ := (Finset.mem_inter.mp hw).1
  have hwq : w = q := by simpa [hQ] using hwQ
  subst w
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hw).2 with ⟨u, hu, huq⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · have huDirect : 0 < Shared.directCount G {q} u := by
      simp [Shared.directCount_singleton, epsilonAt, huq]
    have huLe : Shared.directCount G {q} u ≤ edgeCount G C.A1 {q} := by
      unfold edgeCount
      exact Finset.single_le_sum (s := C.A1)
        (f := fun v => Shared.directCount G {q} v)
        (fun _ _ => Nat.zero_le _) huA1
    omega
  · have hPAny : any 6 (fun p => pToE (graphBits G L) p 0) = true := by
      rw [any_eq_true_iff]
      obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
      refine ⟨i.val, i.isLt, ?_⟩
      rw [pToE_coreBits G.Adj L i 0 i.isLt (by omega)]
      have hiVal : (L.p i).1 = u := congrArg Subtype.val hi
      simpa [hiVal, heZero] using huq
    simp [hcZero, hPAny]

theorem pMinimumDegreeReached_true {eCount : Nat}
    (C : G.LocalConfiguration) (q : V) (hqQ : q ∈ C.Q)
    (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoRoot : epsilonS G C = 0)
    (E : Finset V) (hE : E = {q} ∪ C.Z)
    (eEq : Fin eCount ≃ {v : V // v ∈ E}) (heBound : eCount ≤ 5)
    (hELab : ∀ i : Fin eCount,
      L.e ⟨i.val, lt_of_lt_of_le i.isLt heBound⟩ = (eEq i).1) :
    all 6 (fun p => (8 : BitVec 8).ule
      (pOut (graphBits G L) p + pHOut (graphBits G L) p +
        pEOut eCount (graphBits G L) p)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C q L hG hHCard E eEq heBound hELab p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hCaptured : G.outNeighborFinset v ⊆ C.P ∪ C.H ∪ E := by
    intro w hw
    have hc := BSixKThree.P_outgoingCaptured_general G C hG v hvP hw
    simp only [Finset.mem_union] at hc ⊢
    rcases hc with (((hwH | hwP) | hwQ) | hwExt)
    · exact Or.inl (Or.inr hwH)
    · exact Or.inl (Or.inl hwP)
    · have hwq : w = q := by simpa [hQ] using hwQ
      subst w
      exact Or.inr (by rw [hE]; exact Finset.mem_union_left C.Z (by simp))
    · exact Or.inr (by rw [hE]; exact Finset.mem_union_right {q} (hExt ▸ hwExt))
  have hPH : Disjoint C.P C.H :=
    (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [hE, Finset.disjoint_left]
    intro w hwPH hwE
    rcases Finset.mem_union.mp hwPH with hwP | hwH
    · rcases Finset.mem_union.mp hwE with hwq | hwZ
      · have hwEq : w = q := Finset.mem_singleton.mp hwq
        subst w
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
    · rcases Finset.mem_union.mp hwE with hwq | hwZ
      · have hwEq : w = q := Finset.mem_singleton.mp hwq
        subst w
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hwZ hwH
  have hDegree := outdegree_eq_directCount_of_captured G
    (C.P ∪ C.H ∪ E) v hCaptured
  rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
    directCount_union_of_disjoint G C.P C.H v hPH] at hDegree
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  have hSmall : Shared.directCount G C.P v + Shared.directCount G C.H v +
      Shared.directCount G E v < 256 := by
    have h1 := Finset.card_le_card (Finset.filter_subset (G.Adj v) C.P)
    have h2 := Finset.card_le_card (Finset.filter_subset (G.Adj v) C.H)
    have h3 := Finset.card_le_card (Finset.filter_subset (G.Adj v) E)
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have hECard : E.card = eCount := by
      simpa using (Fintype.card_congr eEq).symm
    change Shared.directCount G C.P v ≤ C.P.card at h1
    change Shared.directCount G C.H v ≤ C.H.card at h2
    change Shared.directCount G E v ≤ E.card at h3
    rw [hpCard] at h1
    rw [hHCard] at h2
    rw [hECard] at h3
    omega
  have hSmallPH : Shared.directCount G C.P v +
      Shared.directCount G C.H v < 256 := by omega
  dsimp [v] at hDegree hSmall hSmallPH
  rw [Nat.mod_eq_of_lt hSmallPH, Nat.mod_eq_of_lt hSmall]
  rw [← hDegree]
  exact hMin v

theorem labelledZReached_true {zCount offset : Nat}
    (C : G.LocalConfiguration) (q : V) (L : ReachedLabels G C q)
    (eZ : Fin zCount ≃ {v : V // v ∈ C.Z})
    (hBound : offset + zCount ≤ 5)
    (hLabel : ∀ z : Fin zCount,
      L.e ⟨offset + z.val, by omega⟩ = (eZ z).1) :
    all zCount (fun z => any 6 fun p =>
      pToE (graphBits G L) p (offset + z)) = true := by
  rw [all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem : (eZ ⟨z, hz⟩).1 ∈ C.Z := (eZ ⟨z, hz⟩).2
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
  refine ⟨i.val, i.isLt, ?_⟩
  rw [pToE_coreBits G.Adj L i (offset + z) i.isLt (by omega)]
  have hiVal : (L.p i).1 = p := congrArg Subtype.val hi
  simpa [hiVal, hLabel ⟨z, hz⟩] using hpz

set_option linter.flexible false in
theorem pSecondP_true_mem (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (_hG : G.IsOriented)
    (p j : Nat) (hp : p < 6) (hj : j < 6)
    (hs : (!pArc (graphBits G L) p j && reachesPH (graphBits G L) p j) = true) :
    (L.p ⟨j, hj⟩).1 ∈
      G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1 := by
  simp only [Bool.and_eq_true] at hs
  rcases hs with ⟨hNotDirect, hReach⟩
  simp only [reachesPH, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hReach
  rcases hReach with ⟨hpj, hDirect | hVia⟩
  · simp [hDirect] at hNotDirect
  have hpj' : p ≠ j := by simpa using hpj
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 10 _).mp hVia
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  have hFirstGraph : G.Adj (L.p ⟨p, hp⟩).1
      (if hmid : middle < 6 then (L.p ⟨middle, hmid⟩).1
       else (L.a ⟨middle - 6 + 1, by omega⟩).1) := by
    split <;> rename_i hmid
    · simp [hmid] at hFirst
      rw [pArc_coreBits G.Adj L p middle hp hmid] at hFirst
      exact (of_decide_eq_true hFirst).2
    · have hm4 : middle - 6 < 4 := by omega
      have hw8 : 1 + (middle - 6) < 8 := by omega
      have hw5 : 1 + (middle - 6) < 5 := by omega
      simp [hmid, pToA, hw8, hw5] at hFirst
      rw [pToH_coreBits G.Adj L p (middle - 6) hp hm4] at hFirst
      simpa [Nat.add_comm] using of_decide_eq_true hFirst
  have hLastGraph : G.Adj
      (if hmid : middle < 6 then (L.p ⟨middle, hmid⟩).1
       else (L.a ⟨middle - 6 + 1, by omega⟩).1)
      (L.p ⟨j, hj⟩).1 := by
    split <;> rename_i hmid
    · simp [hmid] at hLast
      rw [pArc_coreBits G.Adj L middle j hmid hj] at hLast
      exact (of_decide_eq_true hLast).2
    · have hm4 : middle - 6 < 4 := by omega
      have hw8 : 1 + (middle - 6) < 8 := by omega
      have hw5 : 1 + (middle - 6) < 5 := by omega
      simp [hmid, aToP, hw8, hw5] at hLast
      rw [hToP_coreBits G.Adj L (middle - 6) j hm4 hj] at hLast
      simpa [Nat.add_comm] using of_decide_eq_true hLast
  have hNotGraph : ¬G.Adj (L.p ⟨p, hp⟩).1 (L.p ⟨j, hj⟩).1 := by
    rw [pArc_coreBits G.Adj L p j hp hj] at hNotDirect
    simpa [hpj'] using hNotDirect
  have hNe : (L.p ⟨j, hj⟩).1 ≠ (L.p ⟨p, hp⟩).1 := by
    intro heq
    have hij : (⟨j, hj⟩ : Fin 6) = ⟨p, hp⟩ := by
      apply L.p.injective
      exact Subtype.ext heq
    exact hpj' (by simpa using congrArg Fin.val hij.symm)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, hFirstGraph, hLastGraph⟩, hNotGraph, hNe⟩

theorem pSecondPCount_le_graph (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (p : Nat) (hp : p < 6) :
    (pSecondPCount (graphBits G L) p).toNat ≤
      (C.P.filter fun v =>
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply RSeven.XThreeNoRoot.GraphFacts.count_le_filterCard C.P L.p
    (fun j => !pArc (graphBits G L) p j && reachesPH (graphBits G L) p j)
    (fun v => v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro j hj
  exact pSecondP_true_mem G C q L hG p j hp j.isLt hj

theorem totalPToE_toNat {eCount : Nat}
    (C : G.LocalConfiguration) (q : V) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (E : Finset V) (eEq : Fin eCount ≃ {v : V // v ∈ E})
    (heBound : eCount ≤ 5)
    (hELab : ∀ i : Fin eCount,
      L.e ⟨i.val, lt_of_lt_of_le i.isLt heBound⟩ = (eEq i).1) :
    (totalPToE eCount (graphBits G L)).toNat = edgeCount G C.P E := by
  rw [totalPToE, toNat_sumCount]
  have hEach : ∀ i : Fin 6,
      (pEOut eCount (graphBits G L) i).toNat =
        Shared.directCount G E (L.p i).1 := by
    intro i
    exact (pBlockCounts G C q L hG hHCard E eEq heBound hELab
      i i.isLt).2.2
  have hSum :
      (∑ i ∈ Finset.range 6, (pEOut eCount (graphBits G L) i).toNat) =
        edgeCount G C.P E := by
    rw [edgeCount_eq_sum_fin G C.P E L.p, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P E
  have hp : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have he : E.card = eCount := by
    simpa using (Fintype.card_congr eEq).symm
  rw [hp, he] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem aOneToQ_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (eAOne : Fin 2 ≃ {v : V // v ∈ C.A1})
    (hAOne : ∀ i : Fin 2, (L.a ⟨i.val + 1, by omega⟩).1 = (eAOne i).1) :
    (aOneToQ (graphBits G L)).toNat = edgeCount G C.A1 {q} := by
  rw [aOneToQ, Shared.FiniteCore.toNat_count_eq_fin_sum 2 _ (by omega),
    edgeCount_eq_sum_fin G C.A1 {q} eAOne]
  apply Finset.sum_congr rfl
  intro i hi
  rw [aToQ_coreBits G.Adj L (1 + i.val) (by omega)]
  have ha : (⟨1 + i.val, by omega⟩ : Fin 8) =
      ⟨i.val + 1, by omega⟩ := Fin.ext (Nat.add_comm 1 i.val)
  rw [ha, hAOne]
  unfold Shared.directCount CertificateBridge.internalFirstNeighbors
  rw [Finset.filter_singleton]
  by_cases hadj : G.Adj (eAOne i).1 q <;> simp [hadj]

theorem H_to_P_lower (C : G.LocalConfiguration) (q : V)
    (_hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 2) (hx : C.x = 2) (hRCard : C.R.card = 3) :
    16 - edgeCount G C.A1 {q} ≤ edgeCount G C.H C.P := by
  have hH : C.H.card = 4 := by
    rw [BSevenKTwo.H_card_eq_x_add_two G C hk, hx]
  have hQCard : C.Q.card = 1 := by simp [hQ]
  have hA1Q : edgeCount G C.A1 C.Q = edgeCount G C.A1 {q} := by rw [hQ]
  have hXQ : edgeCount G C.X C.Q ≤ 2 := by
    exact (edgeCount_le_card_mul_card G C.X C.Q).trans_eq (by
      rw [show C.X.card = 2 from hx, hQCard])
  have hSplit : edgeCount G C.H C.Q =
      edgeCount G C.A1 C.Q + edgeCount G C.X C.Q := by
    simpa [Digraph.LocalConfiguration.H] using
      BSixKThree.edgeCount_source_union G C.A1 C.X C.Q
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hRefined : edgeCount G C.H C.Q ≤ edgeCount G C.A1 {q} + 2 := by
    omega
  have hBasic := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
  have hA := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  have hLower : 32 ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      32 = ∑ _u ∈ C.H, 8 := by simp [hH]
      _ ≤ ∑ u ∈ C.H, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  rw [hBasic] at hLower
  rw [hH, hx, hRCard] at hA
  norm_num [Nat.choose] at hA
  omega

theorem H_to_P_add_missing_le (C : G.LocalConfiguration) (q : V)
    (hQ : C.Q = {q}) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 6)
    (hNoRoot : epsilonS G C = 0) (hHCard : C.H.card = 4)
    (hZCard : C.Z.card = 4) :
    edgeCount G C.H C.P + (30 - edgeCount G C.P ({q} ∪ C.Z)) ≤ 21 := by
  have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hDis : Disjoint {q} C.Z := by
    rw [Finset.disjoint_left]
    intro v hvq hvZ
    have hvEq : v = q := Finset.mem_singleton.mp hvq
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (by rw [hQ]; simp))
      (hExt ▸ hvZ)
  have hPE : edgeCount G C.P ({q} ∪ C.Z) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} C.Z hDis, ← hQ, ← hExt]
  rw [hHCard] at hCap
  rw [← hPE] at hCap
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
  have hpCard : C.P.card = 6 := hr
  have hECard : ({q} ∪ C.Z).card = 5 := by
    rw [Finset.card_union_of_disjoint hDis]
    simp [hZCard]
  rw [hpCard, hECard] at hPECap
  omega

theorem H_to_P_add_missing_four_le (C : G.LocalConfiguration) (q : V)
    (hQ : C.Q = {q}) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 6)
    (hNoRoot : epsilonS G C = 0) (hHCard : C.H.card = 4)
    (hZCard : C.Z.card = 3) :
    edgeCount G C.H C.P + (24 - edgeCount G C.P ({q} ∪ C.Z)) ≤ 15 := by
  have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hDis : Disjoint {q} C.Z := by
    rw [Finset.disjoint_left]
    intro v hvq hvZ
    have hvEq : v = q := Finset.mem_singleton.mp hvq
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (by rw [hQ]; simp))
      (hExt ▸ hvZ)
  have hPE : edgeCount G C.P ({q} ∪ C.Z) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} C.Z hDis, ← hQ, ← hExt]
  rw [hHCard, ← hPE] at hCap
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
  have hpCard : C.P.card = 6 := hr
  have hECard : ({q} ∪ C.Z).card = 4 := by
    rw [Finset.card_union_of_disjoint hDis]
    simp [hZCard]
  rw [hpCard, hECard] at hPECap
  omega

theorem directAux_to_P_capacity_five (C : G.LocalConfiguration)
    (hG : G.IsOriented) (E : Finset V)
    (hPCard : C.P.card = 6) (hECard : E.card = 5)
    (p : V) (hpP : p ∈ C.P) :
    edgeCount G (RSix.XFourNoRoot.directAuxNeighbors G E p) C.P ≤
      (30 - edgeCount G C.P E) -
        (5 - (RSix.XFourNoRoot.directAuxNeighbors G E p).card) := by
  let S := RSix.XFourNoRoot.directAuxNeighbors G E p
  let T := E \ S
  have hS : S ⊆ E := RSix.XFourNoRoot.directAuxNeighbors_subset G E p
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = E := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 5 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hECard]
  have hpT : Shared.directCount G T p = 0 := by
    unfold Shared.directCount CertificateBridge.internalFirstNeighbors
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e heT hpe
    exact (Finset.mem_sdiff.mp heT).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp heT).1, hpe⟩)
  have hPT : edgeCount G C.P T ≤ 5 * T.card := by
    calc
      edgeCount G C.P T ≤ ∑ r ∈ C.P, if r = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro r hr
        by_cases hrp : r = p
        · subst r; simp [hpT]
        · simp only [hrp, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 * T.card := by
        rw [← Finset.sum_erase_add C.P
          (fun r => if r = p then 0 else T.card) hpP,
          if_pos rfl, Nat.add_zero]
        calc
          (∑ r ∈ C.P.erase p, if r = p then 0 else T.card) =
              ∑ _r ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [if_neg (Finset.mem_erase.mp hr).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 5 * T.card := by rw [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit : edgeCount G C.P E =
      edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = 5 := by
    rw [hTCard]
    have hSLe : S.card ≤ 5 := (Finset.card_le_card hS).trans_eq hECard
    omega
  have hPEUpper := edgeCount_le_card_mul_card G C.P E
  rw [hPCard, hECard] at hPEUpper
  change edgeCount G S C.P ≤
    (30 - edgeCount G C.P E) - (5 - S.card)
  omega

private theorem effectiveFive_arithmetic
    (m s u internal reverse : Nat) (hm : m ≤ 7) (hs : s ≤ 5)
    (hRow : 5 - s ≤ m)
    (hLower : s * (8 - u) ≤ internal + reverse)
    (hInternal : internal ≤ s.choose 2)
    (hReverse : reverse ≤ m - (5 - s)) :
    (individualEffectiveLowerFiveAt (BitVec.ofNat 8 m)
      (BitVec.ofNat 8 s)).toNat ≤ u := by
  interval_cases m <;> interval_cases s <;>
    simp [individualEffectiveLowerFiveAt, effectiveAtRowSize, Nat.choose]
      at hRow hLower hInternal hReverse ⊢ <;> omega

theorem individualEffectiveLowerFive_graph (C : G.LocalConfiguration)
    (q : V) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 4)
    (E : Finset V) (hEP : Disjoint E C.P)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (hmBound : 30 - edgeCount G C.P E ≤ 7)
    (p : Nat) (hp : p < 6) :
    (individualEffectiveLowerFive (graphBits G L) p).toNat ≤
      (RSix.XFourNoRoot.directAuxEffectiveUnion G C E
        (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G L
  let v := (L.p ⟨p, hp⟩).1
  let S := RSix.XFourNoRoot.directAuxNeighbors G E v
  let U := RSix.XFourNoRoot.directAuxEffectiveUnion G C E v
  let m := 30 - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = 5 := by
    simpa using (Fintype.card_congr eEq).symm
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ 5 :=
    (Finset.card_le_card
      (RSix.XFourNoRoot.directAuxNeighbors_subset G E v)).trans_eq hECard
  have hRow : 5 - s ≤ m := by
    have hOther : ∑ r ∈ C.P.erase v, Shared.directCount G E r ≤ 25 := by
      calc
        _ ≤ ∑ _r ∈ C.P.erase v, 5 := by
          apply Finset.sum_le_sum
          intro r hr
          exact (Finset.card_le_card
            (Finset.filter_subset _ _)).trans_eq hECard
        _ = 25 := by simp [Finset.card_erase_of_mem hvP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (Shared.directCount G E) hvP
    have hSv : s = Shared.directCount G E v := rfl
    have hEdge : edgeCount G C.P E =
        ∑ r ∈ C.P, Shared.directCount G E r := rfl
    dsimp [m]
    omega
  have hLower := RSix.XFourNoRoot.directAuxEffective_capacity_lower
    G C hMin E hEP v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directAux_to_P_capacity_five G C hG E hPCard hECard v hvP
  have hTotal := totalPToE_toNat G C q L hG hHCard E eEq
    (by omega) hELab
  have hM : (externalMissing 5 bits).toNat = m := by
    rw [externalMissing, BitVec.toNat_sub]
    change ((256 - (totalPToE 5 bits).toNat + 30) % 256) = m
    rw [hTotal]
    have hCap := edgeCount_le_card_mul_card G C.P E
    rw [hPCard, hECard] at hCap
    have heq : 256 - edgeCount G C.P E + 30 =
        256 + (30 - edgeCount G C.P E) := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
    have hlt : 30 - edgeCount G C.P E < 256 := by omega
    dsimp [m]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  have hS : (pEOut 5 bits p).toNat = s := by
    rw [(pBlockCounts G C q L hG hHCard E eEq (by omega) hELab p hp).2.2]
    rfl
  have hMBV : externalMissing 5 bits = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    dsimp [m]
    omega
  have hSBV : pEOut 5 bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hmLe : m ≤ 7 := by simpa [m] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (5 - s) at hToP
  change (individualEffectiveLowerFive bits p).toNat ≤ U.card
  simp only [individualEffectiveLowerFive]
  rw [hMBV, hSBV]
  exact effectiveFive_arithmetic m s U.card (edgeCount G S S)
    (edgeCount G S C.P) hmLe hs hRow hLower hInternal hToP

theorem pEffectiveConditionFive_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hNoRoot : epsilonS G C = 0)
    (hHCard : C.H.card = 4) (hy : BSevenKTwo.y G C = 1)
    (E : Finset V) (hE : E = {q} ∪ C.Z)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (hmBound : 30 - edgeCount G C.P E ≤ 7) :
    all 6 (pEffectiveCondition 5 true (graphBits G L)) = true := by
  let bits := graphBits G L
  have hAux : E = RSix.XFourNoRoot.auxiliarySet G C := by
    rw [hE]
    exact (RSix.XThreeNoRoot.Assembly.auxiliarySet_eq_E
      G C q hQ hy hNoRoot).symm
  have hEP : Disjoint E C.P := by
    rw [hE, Finset.disjoint_left]
    intro w hwE hwP
    rcases Finset.mem_union.mp hwE with hwq | hwZ
    · have hwEq : w = q := Finset.mem_singleton.mp hwq
      subst w
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hBlocks := pBlockCounts G C q L hG hHCard E eEq (by omega) hELab p hp
  have hTable := individualEffectiveLowerFive_graph G C q L hG hMin
    hHCard E hEP eEq hELab hmBound p hp
  have hPS := pSecondPCount_le_graph G C q L hG p hp
  have hUnion :=
    RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG E hAux v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨v, hs⟩)
  have hDegree : G.outdegree v = Shared.directCount G C.P v +
      Shared.directCount G C.H v + Shared.directCount G E v := by
    have hRootEmpty : rootSecondFinset G C = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [epsilonS] using hNoRoot
    have hExt : externalTargets G C = C.Z := by
      simp [externalTargets, hRootEmpty]
    have hCaptured : G.outNeighborFinset v ⊆ C.P ∪ C.H ∪ E := by
      intro w hw
      have hc := BSixKThree.P_outgoingCaptured_general G C hG v hvP hw
      simp only [Finset.mem_union] at hc ⊢
      rcases hc with (((hwH | hwP) | hwQ) | hwExt)
      · exact Or.inl (Or.inr hwH)
      · exact Or.inl (Or.inl hwP)
      · have hwq : w = q := by simpa [hQ] using hwQ
        subst w
        exact Or.inr (by rw [hE]; exact Finset.mem_union_left C.Z (by simp))
      · exact Or.inr (by rw [hE]; exact Finset.mem_union_right {q} (hExt ▸ hwExt))
    have hPH : Disjoint C.P C.H :=
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
    have hPHE : Disjoint (C.P ∪ C.H) E := by
      rw [Finset.disjoint_left]
      intro w hwPH hwE
      rcases Finset.mem_union.mp hwPH with hwP | hwH
      · exact (Finset.disjoint_left.mp hEP) hwE hwP
      · rw [hE] at hwE
        rcases Finset.mem_union.mp hwE with hwq | hwZ
        · have hwEq : w = q := Finset.mem_singleton.mp hwq
          subst w
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hwZ hwH
    have hd := outdegree_eq_directCount_of_captured G (C.P ∪ C.H ∪ E) v hCaptured
    rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
      directCount_union_of_disjoint G C.P C.H v hPH] at hd
    exact hd
  have hNatural : (pSecondPCount bits p).toNat +
      (individualEffectiveLowerFive bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pEOut 5 bits p).toNat := by
    dsimp [v, bits] at hPS hTable hUnion hNS hDegree hBlocks ⊢
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    omega
  simp only [pEffectiveCondition, individualEffectiveLower,
    BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pSecondPCount bits p).toNat +
      (individualEffectiveLowerFive bits p).toNat + 1) % 256 ≤
    ((pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pEOut 5 bits p).toNat) % 256
  have hRightSmall : (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pEOut 5 bits p).toNat < 256 := by
    have hpLe : (pOut bits p).toNat ≤ 6 := by
      rw [hBlocks.1]
      have hc : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
    have hhLe : (pHOut bits p).toNat ≤ 4 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have heLe : (pEOut 5 bits p).toNat ≤ 5 := by
      rw [hBlocks.2.2]
      have hc : E.card = 5 := by simpa using (Fintype.card_congr eEq).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
    omega
  rw [Nat.mod_eq_of_lt hRightSmall,
    Nat.mod_eq_of_lt (hNatural.trans_lt hRightSmall)]
  exact hNatural

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.GraphBridge
