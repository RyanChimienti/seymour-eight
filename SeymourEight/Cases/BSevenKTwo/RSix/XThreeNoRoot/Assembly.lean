import SeymourEight.Cases.BSevenKTwo.RSix.XThreeNoRoot.GraphFacts
import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective
import SeymourEight.Cases.BSevenKTwo.Counting
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Assembly

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (L : Labels G C q) : Core.Encoding :=
  Encoding.coreBits G.Adj L

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem orientedA_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented) :
    orientedA (graphBits G L) = true := by
  have hArc (i j : Nat) (hi : i < 8) (hj : j < 8) :
      SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.aArc
          (graphBits G L) i j =
        decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) :=
    aArc_coreBits G.Adj L i j hi hj
  rw [orientedA, SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.orientedA,
    all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true, hArc i i hi hi]
  constructor
  · simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [hArc i j hi hj, hArc j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    · by_cases h : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
      · simp [h, hG.2 h]
      · simp [h]

theorem orientedP_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented) :
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
    (L : Labels G C q) (hG : G.IsOriented) :
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

theorem fixedA_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (_hG : G.IsOriented) :
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
    by_cases hi3 : i < 3
    · have hx := L.a_x ⟨i, hi3⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
          (Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩)
          (by simpa [Nat.add_comm] using hx)
      simp [hn]
    · have hr := L.a_r ⟨i - 3, by omega⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        exact (Finset.mem_sdiff.mp hr).2 (by
          simpa [show i - 3 + 6 = 3 + i by omega] using
            Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
      simp [hn]
  have hA1R : all 4 (fun k =>
      !aArc bits (1 + k / 2) (6 + k % 2)) = true := by
    rw [all_eq_true_iff]
    intro k hk
    rw [aArc_coreBits G.Adj L (1 + k / 2) (6 + k % 2)
      (by omega) (by omega)]
    have hn := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
      G C (L.a ⟨1 + k / 2, by omega⟩).1
      (L.a ⟨6 + k % 2, by omega⟩).1
      (by simpa [Nat.add_comm] using L.a_aOne ⟨k / 2, by omega⟩)
      (by simpa [Nat.add_comm] using L.a_r ⟨k % 2, by omega⟩)
    simpa using decide_eq_false hn
  simp only [fixedA,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.fixedA,
    Bool.and_eq_true]
  exact ⟨⟨⟨h01, h02⟩, hTail⟩, hA1R⟩

theorem everyXReached_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hk : C.k = 2) :
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
    obtain ⟨i, hi⟩ := (GraphFacts.aOneEquiv G C q L hk).surjective ⟨u, huA1⟩
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
    have hh : (⟨2 + x + 1, by omega⟩ : Fin 8) = ⟨x + 3, by omega⟩ :=
      Fin.ext (show 2 + x + 1 = x + 3 by omega)
    rw [hh]
    simpa [hiVal] using hux

theorem qReached_true (C : G.LocalConfiguration) (q : V)
    (_hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hk : C.k = 2) (hy : BSevenKTwo.y G C = 1) :
    qReached (graphBits G L) = true := by
  have hCard : (reachedQ G C).card = 1 := hy
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
  have hvQ := (Finset.mem_inter.mp hv).1
  have hvq : v = q := by simpa [hQ] using hvQ
  subst v
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hv).2 with ⟨u, hu, huq⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [qReached, Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := (GraphFacts.aOneEquiv G C q L hk).surjective ⟨u, huA1⟩
    refine ⟨i.val, i.isLt, ?_⟩
    rw [aToQ_coreBits G.Adj L (1 + i.val) (by omega)]
    have hiVal : (L.a ⟨i.val + 1, by omega⟩).1 = u := congrArg Subtype.val hi
    have hai : (⟨1 + i.val, by omega⟩ : Fin 8) =
        ⟨i.val + 1, by omega⟩ := Fin.ext (show 1 + i.val = i.val + 1 by omega)
    rw [hai, hiVal]
    simpa using huq
  · rw [qReached, Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨i, hi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨i.val, i.isLt, ?_⟩
    rw [pToE_coreBits G.Adj L i 0 i.isLt (by omega)]
    have hiVal : (L.p i).1 = u := congrArg Subtype.val hi
    have he0 : (⟨0, by omega⟩ : Fin 4) = 0 := rfl
    rw [hiVal, he0, L.e_zero]
    exact decide_eq_true huq

theorem allZReached_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : allZReached (graphBits G L) = true := by
  rw [allZReached, all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := L.e_tail_Z ⟨z, hz⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
  refine ⟨i.val, i.isLt, ?_⟩
  rw [pToE_coreBits G.Adj L i (1 + z) i.isLt (by omega)]
  have hiVal : (L.p i).1 = p := congrArg Subtype.val hi
  have he : (⟨z + 1, by omega⟩ : Fin 4) = ⟨1 + z, by omega⟩ :=
    Fin.ext (show z + 1 = 1 + z by omega)
  simpa [hiVal, he] using hpz

theorem A_outdegree_eq_A_add_B (C : G.LocalConfiguration)
    (hG : G.IsOriented) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = Shared.directCount G C.A u + Shared.directCount G C.B u := by
  have hAB : Disjoint C.A C.B :=
    Digraph.LocalConfiguration.disjoint_A_B (G := G) C
  have h := outdegree_eq_directCount_of_captured G (C.A ∪ C.B) u
    (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG u hu)
  rw [directCount_union_of_disjoint G C.A C.B u hAB] at h
  exact h

theorem aMinimumAndDegree_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hk : C.k = 2) (hr : C.r = 6) :
    aMinimumAndDegree (graphBits G L) = true := by
  let bits := graphBits G L
  rw [aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C q L a ha
  have hBO := aBOut_toNat G C q hqQ hQ L a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 2 ≤ (aOut bits a).toNat := by
    rw [hAO]
    simpa [hk, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (aOut bits a).toNat = 2 → 6 ≤ (aBOut bits a).toNat := by
    intro heq
    rw [hBO]
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change Shared.directCount G C.A (L.a ⟨a, ha⟩).1 = 2
      rw [← hAO]
      exact heq
    simpa [hr, Shared.directCount,
      CertificateBridge.internalFirstNeighbors] using hPivotA.2 hCardEq
  have hTotal : 8 ≤ (aOut bits a).toNat + (aBOut bits a).toNat := by
    rw [hAO, hBO, ← A_outdegree_eq_A_add_B G C hG _ (L.a _).2]
    exact hMin _
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
      exact hAmin
    · rw [Bool.or_eq_true]
      by_cases heq : aOut bits a = 2
      · right
        norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
        exact hTie (congrArg BitVec.toNat heq)
      · left; simpa using heq
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    have hSmall : (aOut bits a).toNat + (aBOut bits a).toNat < 256 := by
      have hA : Shared.directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hB : Shared.directCount G C.B (L.a ⟨a, ha⟩).1 ≤ C.B.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hcA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
      have hcB : C.B.card = 7 := by
        rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
          Finset.card_union_of_disjoint
            (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C), hQ]
        have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
        simp [hp]
      rw [hAO, hBO]
      omega
    rw [Nat.mod_eq_of_lt hSmall]
    exact hTotal

theorem pMinimumDegree_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 5)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoRoot : epsilonS G C = 0) :
    pMinimumDegree (graphBits G L) = true := by
  rw [pMinimumDegree, all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C q L hG hHCard p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add]
  have hSmall : (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat < 256 := by
    have hP : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hH : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    rw [hBlocks.1, hBlocks.2.1]
    omega
  rw [Nat.mod_eq_of_lt hSmall]
  have hSmall' : (pOut (graphBits G L) p).toNat +
      (pHOut (graphBits G L) p).toNat +
      (pEOut (graphBits G L) p).toNat < 256 := by
    have hP : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hH : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hE : Shared.directCount G ({q} ∪ C.Z) (L.p ⟨p, hp⟩).1 ≤
        ({q} ∪ C.Z).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have heCard : ({q} ∪ C.Z).card = 4 := by
      rw [← Fintype.card_coe]
      have he' := (Fintype.card_congr L.e).symm
      norm_num at he'
      simpa only [Finset.mem_union, Finset.mem_singleton] using he'
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    omega
  rw [Nat.mod_eq_of_lt hSmall', hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by simp [externalTargets, hRootEmpty]
  have hCaptured : G.outNeighborFinset (L.p ⟨p, hp⟩).1 ⊆
      C.P ∪ C.H ∪ ({q} ∪ C.Z) := by
    intro v hv
    have hc := BSixKThree.P_outgoingCaptured_general G C hG _ (L.p _).2 hv
    simp only [Finset.mem_union] at hc ⊢
    rcases hc with (((hvH | hvP) | hvQ) | hvExt)
    · exact Or.inl (Or.inr hvH)
    · exact Or.inl (Or.inl hvP)
    · have hvq : v = q := by simpa [hQ] using hvQ
      subst v
      exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (hExt ▸ hvExt))
  have hPH : Disjoint C.P C.H :=
    Digraph.LocalConfiguration.disjoint_H_P (G := G) C |>.symm
  have hPHE : Disjoint (C.P ∪ C.H) ({q} ∪ C.Z) := by
    rw [Finset.disjoint_left]
    intro v hvPH hvE
    rcases Finset.mem_union.mp hvPH with hvP | hvH
    · rcases Finset.mem_union.mp hvE with hvq | hvZ
      · have hvEq : v = q := Finset.mem_singleton.mp hvq
        subst v
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
          hqQ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · rcases Finset.mem_union.mp hvE with hvq | hvZ
      · have hvB : v ∈ C.B := by
          have hvEq : v = q := Finset.mem_singleton.mp hvq
          subst v
          exact Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH) hvB
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
  have hDegree := outdegree_eq_directCount_of_captured G
    (C.P ∪ C.H ∪ ({q} ∪ C.Z)) (L.p ⟨p, hp⟩).1 hCaptured
  rw [directCount_union_of_disjoint G (C.P ∪ C.H) ({q} ∪ C.Z) _ hPHE,
    directCount_union_of_disjoint G C.P C.H _ hPH] at hDegree
  have hm := hMin (L.p ⟨p, hp⟩).1
  change 8 ≤ Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
    Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G ({q} ∪ C.Z) (L.p ⟨p, hp⟩).1
  omega

theorem aNonSeymour_all_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hNoRoot : epsilonS G C = 0)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 8 (aNonSeymour (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro a ha
  exact nonSeymour_graphBits_true G C q hqQ hQ L hG hNoRoot
    hNoSeymour a (by omega)

theorem pNonSeymour_all_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hNoRoot : epsilonS G C = 0)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 6 (pNonSeymour (graphBits G L)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  exact nonSeymour_graphBits_true G C q hqQ hQ L hG hNoRoot
    hNoSeymour (8 + p) (by omega)

theorem totalPToE_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented) (hHCard : C.H.card = 5) :
    (totalPToE (graphBits G L)).toNat = edgeCount G C.P ({q} ∪ C.Z) := by
  rw [totalPToE, toNat_sumCount]
  have hEach : ∀ i : Fin 6, (pEOut (graphBits G L) i).toNat =
      Shared.directCount G ({q} ∪ C.Z) (L.p i).1 := by
    intro i
    exact (pBlockCounts G C q L hG hHCard i i.isLt).2.2
  have hSum : (∑ i ∈ Finset.range 6, (pEOut (graphBits G L) i).toNat) =
      edgeCount G C.P ({q} ∪ C.Z) := by
    rw [edgeCount_eq_sum_fin G C.P ({q} ∪ C.Z) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have he : ({q} ∪ C.Z).card = 4 := by
    rw [← Fintype.card_coe]
    have he' := (Fintype.card_congr L.e).symm
    norm_num at he'
    simpa only [Finset.mem_union, Finset.mem_singleton] using he'
  rw [hp, he] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented) (hHCard : C.H.card = 5) :
    (externalMissing (graphBits G L)).toNat =
      24 - edgeCount G C.P ({q} ∪ C.Z) := by
  rw [externalMissing, BitVec.toNat_sub,
    totalPToE_toNat G C q L hG hHCard]
  have hCap := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have he : ({q} ∪ C.Z).card = 4 := by
    simpa using (show ({q} ∪ C.Z).card = 4 from by
      rw [← Fintype.card_coe]
      have he' := (Fintype.card_congr L.e).symm
      norm_num at he'
      simpa only [Finset.mem_union, Finset.mem_singleton] using he')
  rw [hp, he] at hCap
  norm_num [BitVec.toNat_ofNat]
  change ((256 - edgeCount G C.P ({q} ∪ C.Z) + 24) % 256) = _
  have heq : 256 - edgeCount G C.P ({q} ∪ C.Z) + 24 =
      256 + (24 - edgeCount G C.P ({q} ∪ C.Z)) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  have hlt : 24 - edgeCount G C.P ({q} ∪ C.Z) < 256 := by omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
  simp only [Finset.singleton_union]

theorem totalHToP_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hHCard : C.H.card = 5) :
    (totalHToP (graphBits G L)).toNat = edgeCount G C.H C.P := by
  rw [totalHToP, toNat_sumCount]
  have hEach : ∀ i : Fin 5, (hPOut (graphBits G L) i).toNat =
      Shared.directCount G C.P (L.a ⟨i.val + 1, by omega⟩).1 := by
    intro i
    exact hPOut_toNat G C q L i i.isLt
  have hSum : (∑ i ∈ Finset.range 5, (hPOut (graphBits G L) i).toNat) =
      edgeCount G C.H C.P := by
    rw [edgeCount_eq_sum_fin G C.H C.P (hEquiv G C q L hHCard),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simpa using hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hHCard, hp] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem aOneToQ_toNat (C : G.LocalConfiguration) (q : V)
    (_hqQ : q ∈ C.Q) (L : Labels G C q) (hk : C.k = 2) :
    (aOneToQ (graphBits G L)).toNat = edgeCount G C.A1 {q} := by
  rw [aOneToQ, toNat_count_eq_fin_sum 2 _ (by omega),
    edgeCount_eq_sum_fin G C.A1 {q} (aOneEquiv G C q L hk)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [aToQ_coreBits G.Adj L (1 + i.val) (by omega)]
  have ha : (⟨1 + i.val, by omega⟩ : Fin 8) =
      ⟨i.val + 1, by omega⟩ := Fin.ext
        (show 1 + i.val = i.val + 1 by omega)
  rw [ha]
  unfold Shared.directCount CertificateBridge.internalFirstNeighbors
  rw [Finset.filter_singleton]
  by_cases hadj : G.Adj (L.a ⟨i.val + 1, by omega⟩).1 q <;> simp [hadj]

theorem H_to_P_lower (C : G.LocalConfiguration) (q : V)
    (_hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 2) (hx : C.x = 3) (hRCard : C.R.card = 2)
    (_hy : BSevenKTwo.y G C = 1) :
    18 - edgeCount G C.A1 {q} ≤ edgeCount G C.H C.P := by
  have hH : C.H.card = 5 := by
    rw [BSevenKTwo.H_card_eq_x_add_two G C hk, hx]
  have hQCard : C.Q.card = 1 := by simp [hQ]
  have hA1Q : edgeCount G C.A1 C.Q = edgeCount G C.A1 {q} := by rw [hQ]
  have hXQ : edgeCount G C.X C.Q ≤ 3 := by
    exact (edgeCount_le_card_mul_card G C.X C.Q).trans_eq (by
      rw [show C.X.card = 3 from hx, hQCard])
  have hSplit : edgeCount G C.H C.Q =
      edgeCount G C.A1 C.Q + edgeCount G C.X C.Q := by
    simpa [Digraph.LocalConfiguration.H] using
      BSixKThree.edgeCount_source_union G C.A1 C.X C.Q
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hRefined : edgeCount G C.H C.Q ≤ edgeCount G C.A1 {q} + 3 := by omega
  have hBasic := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
  have hA := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  have hLower : 40 ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      40 = ∑ _u ∈ C.H, 8 := by simp [hH]
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
    (hNoRoot : epsilonS G C = 0) (hHCard : C.H.card = 5)
    (hZCard : C.Z.card = 3) :
    edgeCount G C.H C.P + (24 - edgeCount G C.P ({q} ∪ C.Z)) ≤ 21 := by
  have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by simp [externalTargets, hRootEmpty]
  have hDis : Disjoint {q} C.Z := by
    rw [Finset.disjoint_left]
    intro v hvq hvZ
    have hvEq : v = q := Finset.mem_singleton.mp hvq
    subst v
    exact (Finset.disjoint_left.mp
      (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (by
        rw [hQ]; simp)) (hExt ▸ hvZ)
  have hPE : edgeCount G C.P ({q} ∪ C.Z) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} C.Z hDis, ← hQ, ← hExt]
  rw [hHCard] at hCap
  rw [← hPE] at hCap
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
  have hpCard : C.P.card = 6 := hr
  have hECard : ({q} ∪ C.Z).card = 4 := by
    have hqNotZ : q ∉ C.Z := by
      intro hz
      exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C (by rw [hQ]; simp))
        (hExt ▸ hz)
    rw [Finset.card_union_of_disjoint]
    · simp [hZCard]
    · rw [Finset.disjoint_left]
      intro v hvq hvz
      exact hqNotZ (Finset.mem_singleton.mp hvq ▸ hvz)
  rw [hpCard, hECard] at hPECap
  omega

theorem orderedP_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hNoRoot : epsilonS G C = 0)
    (hOrder : ∀ i : Fin 5,
      G.outdegree (L.p ⟨i.val + 1, by omega⟩).1 ≤
        G.outdegree (L.p ⟨i.val, by omega⟩).1) :
    orderedP (graphBits G L) = true := by
  rw [orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  have h1 := directCount_graphBits_toNat G C q hqQ hQ L hG hNoRoot
    (9 + p) (by omega)
  have h0 := directCount_graphBits_toNat G C q hqQ hQ L hG hNoRoot
    (8 + p) (by omega)
  rw [h1, h0]
  simp only [labelledVertex, dif_neg (by omega : ¬9 + p < 8),
    dif_pos (by omega : 9 + p < 14), dif_neg (by omega : ¬8 + p < 8),
    dif_pos (by omega : 8 + p < 14)]
  have he1 : (⟨9 + p - 8, by omega⟩ : Fin 6) =
      ⟨p + 1, by omega⟩ := Fin.ext (show 9 + p - 8 = p + 1 by omega)
  have he0 : (⟨8 + p - 8, by omega⟩ : Fin 6) =
      ⟨p, by omega⟩ := Fin.ext (show 8 + p - 8 = p by omega)
  rw [he1, he0]
  exact hOrder ⟨p, hp⟩

theorem orderedStructuralClasses_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hAOne : ∀ i : Fin 1, Labels.structuralKey G C
        (L.a ⟨i.val + 2, by omega⟩).1 ≤
      Labels.structuralKey G C (L.a ⟨i.val + 1, by omega⟩).1)
    (hX : ∀ i : Fin 2, Labels.structuralKey G C
        (L.a ⟨4 + i.val, by omega⟩).1 ≤
      Labels.structuralKey G C (L.a ⟨3 + i.val, by omega⟩).1)
    (hR : ∀ i : Fin 1, Labels.structuralKey G C
        (L.a ⟨i.val + 7, by omega⟩).1 ≤
      Labels.structuralKey G C (L.a ⟨i.val + 6, by omega⟩).1) :
    orderedStructuralClasses (graphBits G L) = true := by
  have hAB (a : Nat) (ha : a < 8) :
      (aBOut (graphBits G L) a).toNat =
        Labels.structuralKey G C (L.a ⟨a, ha⟩).1 :=
    aBOut_toNat G C q hqQ hQ L a ha
  simp only [orderedStructuralClasses, Bool.and_eq_true,
    BitVec.ule_eq_decide, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hAB 2 (by omega), hAB 1 (by omega)]; exact hAOne 0
  · rw [all_eq_true_iff]
    intro x hx
    simp only [decide_eq_true_eq]
    rw [hAB (4 + x) (by omega), hAB (3 + x) (by omega)]
    exact hX ⟨x, hx⟩
  · rw [hAB 7 (by omega), hAB 6 (by omega)]; exact hR 0

theorem directAux_to_P_capacity_four (C : G.LocalConfiguration)
    (hG : G.IsOriented) (E : Finset V)
    (hPCard : C.P.card = 6) (hECard : E.card = 4)
    (p : V) (hpP : p ∈ C.P) :
    edgeCount G (RSix.XFourNoRoot.directAuxNeighbors G E p) C.P ≤
      (24 - edgeCount G C.P E) -
        (4 - (RSix.XFourNoRoot.directAuxNeighbors G E p).card) := by
  let S := RSix.XFourNoRoot.directAuxNeighbors G E p
  let T := E \ S
  have hS : S ⊆ E := RSix.XFourNoRoot.directAuxNeighbors_subset G E p
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = E := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 4 - S.card := by
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
        rw [← Finset.sum_erase_add C.P (fun r => if r = p then 0 else T.card) hpP,
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
  have hSCard : S.card + T.card = 4 := by
    rw [hTCard]
    have hSLe : S.card ≤ 4 := (Finset.card_le_card hS).trans_eq hECard
    omega
  have hPEUpper := edgeCount_le_card_mul_card G C.P E
  rw [hPCard, hECard] at hPEUpper
  change edgeCount G S C.P ≤
    (24 - edgeCount G C.P E) - (4 - S.card)
  omega

theorem individualEffectiveLower_graph (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : Labels G C q) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 5)
    (hmBound : 24 - edgeCount G C.P ({q} ∪ C.Z) ≤ 5)
    (p : Nat) (hp : p < 6) :
    (individualEffectiveLower (graphBits G L) p).toNat ≤
      (RSix.XFourNoRoot.directAuxEffectiveUnion G C ({q} ∪ C.Z)
        (L.p ⟨p, hp⟩).1).card := by
  let bits := graphBits G L
  let E := {q} ∪ C.Z
  let v := (L.p ⟨p, hp⟩).1
  let S := RSix.XFourNoRoot.directAuxNeighbors G E v
  let U := RSix.XFourNoRoot.directAuxEffectiveUnion G C E v
  let m := 24 - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = 4 := by
    dsimp [E]
    rw [← Fintype.card_coe]
    have he' := (Fintype.card_congr L.e).symm
    norm_num at he'
    simpa only [Finset.singleton_union, Finset.mem_insert,
      Finset.mem_singleton] using he'
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hEP : Disjoint E C.P := by
    rw [Finset.disjoint_left]
    intro w hwE hwP
    rcases Finset.mem_union.mp hwE with hwq | hwZ
    · have hwEq : w = q := Finset.mem_singleton.mp hwq
      subst w
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP
        hqQ
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
  have hs : s ≤ 4 :=
    (Finset.card_le_card
      (RSix.XFourNoRoot.directAuxNeighbors_subset G E v)).trans_eq hECard
  have hRow : 4 - s ≤ m := by
    have hOther : ∑ r ∈ C.P.erase v, Shared.directCount G E r ≤ 20 := by
      calc
        _ ≤ ∑ _r ∈ C.P.erase v, 4 := by
          apply Finset.sum_le_sum
          intro r hr
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 20 := by simp [Finset.card_erase_of_mem hvP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (Shared.directCount G E) hvP
    have hSv : s = Shared.directCount G E v := rfl
    have hEdge : edgeCount G C.P E =
        ∑ r ∈ C.P, Shared.directCount G E r := rfl
    dsimp [m]
    omega
  have hLower := RSix.XFourNoRoot.directAuxEffective_capacity_lower
    G C hMin E hEP v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directAux_to_P_capacity_four G C hG E hPCard hECard v hvP
  have hM : (externalMissing bits).toNat = m := by
    exact externalMissing_toNat G C q L hG hHCard
  have hS : (pEOut bits p).toNat = s := by
    rw [(pBlockCounts G C q L hG hHCard p hp).2.2]
    rfl
  have hMBV : externalMissing bits = BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    dsimp [m]
    omega
  have hSBV : pEOut bits p = BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hmLe : m ≤ 5 := by simpa [m, E] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (4 - s) at hToP
  change (individualEffectiveLower bits p).toNat ≤ U.card
  simp only [individualEffectiveLower]
  rw [hMBV, hSBV]
  interval_cases m <;> interval_cases s <;>
    simp only [BEq.rfl, BitVec.ofNat_eq_ofNat, BitVec.reduceBEq,
      BitVec.toNat_ofNat, Bool.false_eq_true, Nat.add_one_sub_one, Nat.choose,
      Nat.not_ofNat_le_one, Nat.one_le_ofNat, Nat.reduceAdd, Nat.reduceLeDiff,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, Nat.sub_eq_zero_of_le,
      Nat.zero_mod, OfNat.ofNat_ne_zero, Std.le_refl, add_zero,
      effectiveAtRowSize, nonpos_iff_eq_zero, one_mul, one_ne_zero,
      tsub_le_iff_right, tsub_self, tsub_zero, zero_le, zero_mul, zero_tsub,
      ↓reduceIte]
      at hInternal hToP hLower hRow ⊢ <;>
    omega

theorem pSecondPCount_le_graph (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : Labels G C q) (hG : G.IsOriented)
    (p : Nat) (hp : p < 6) :
    (pSecondPCount (graphBits G L) p).toNat ≤
      (C.P.filter fun v =>
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply RSeven.XThreeNoRoot.GraphFacts.count_le_filterCard C.P L.p
    (fun j => strictSecondLocal (graphBits G L) (8 + p) (8 + j))
    (fun v => v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro j hj
  have hm := strictSecondLocal_true_mem G C q hqQ L hG
    (8 + p) (8 + j) (by omega) (by omega) hj
  simpa [labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 14 by omega, show ¬8 + j.val < 8 by omega,
    show 8 + j.val < 14 by omega] using hm

theorem auxiliarySet_eq_E (C : G.LocalConfiguration) (q : V)
    (hQ : C.Q = {q}) (hy : BSevenKTwo.y G C = 1)
    (hNoRoot : epsilonS G C = 0) :
    RSix.XFourNoRoot.auxiliarySet G C = {q} ∪ C.Z := by
  have hReached : reachedQ G C = {q} := by
    have hc : (reachedQ G C).card = 1 := hy
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    have hvQ : v ∈ C.Q := (Finset.mem_inter.mp (by simp [hv] : v ∈ reachedQ G C)).1
    have hvq : v = q := by simpa [hQ] using hvQ
    simpa [hvq] using hv
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by simp [externalTargets, hRootEmpty]
  simp [RSix.XFourNoRoot.auxiliarySet, hReached, hExt]

theorem pEffectiveCondition_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hNoRoot : epsilonS G C = 0)
    (hHCard : C.H.card = 5) (hy : BSevenKTwo.y G C = 1)
    (hmBound : 24 - edgeCount G C.P ({q} ∪ C.Z) ≤ 5) :
    all 6 (pEffectiveCondition (graphBits G L)) = true := by
  let bits := graphBits G L
  let E := {q} ∪ C.Z
  have hAux : E = RSix.XFourNoRoot.auxiliarySet G C :=
    (auxiliarySet_eq_E G C q hQ hy hNoRoot).symm
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hBlocks := pBlockCounts G C q L hG hHCard p hp
  have hTable := individualEffectiveLower_graph G C q hqQ L hG hMin
    hHCard hmBound p hp
  have hPS := pSecondPCount_le_graph G C q hqQ L hG p hp
  have hUnion := RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
    G C hG E hAux v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨v, hs⟩)
  have hDegree : G.outdegree v = Shared.directCount G C.P v +
      Shared.directCount G C.H v + Shared.directCount G E v := by
    have hRootEmpty : rootSecondFinset G C = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [epsilonS] using hNoRoot
    have hExt : externalTargets G C = C.Z := by simp [externalTargets, hRootEmpty]
    have hCaptured : G.outNeighborFinset v ⊆ C.P ∪ C.H ∪ E := by
      intro w hw
      have hc := BSixKThree.P_outgoingCaptured_general G C hG v hvP hw
      simp only [Finset.mem_union] at hc ⊢
      rcases hc with (((hwH | hwP) | hwQ) | hwExt)
      · exact Or.inl (Or.inr hwH)
      · exact Or.inl (Or.inl hwP)
      · have hwq : w = q := by simpa [hQ] using hwQ
        subst w
        apply Or.inr
        exact Finset.mem_union_left C.Z (Finset.mem_singleton_self q)
      · apply Or.inr
        exact Finset.mem_union_right {q} (by simpa [hExt] using hwExt)
    have hPH : Disjoint C.P C.H :=
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
    have hPHE : Disjoint (C.P ∪ C.H) E := by
      rw [Finset.disjoint_left]
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
    have hd := outdegree_eq_directCount_of_captured G (C.P ∪ C.H ∪ E) v hCaptured
    rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
      directCount_union_of_disjoint G C.P C.H v hPH] at hd
    exact hd
  have hNatural : (pSecondPCount bits p).toNat +
      (individualEffectiveLower bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pEOut bits p).toNat := by
    dsimp [v, E, bits] at hPS hTable hUnion hNS hDegree hBlocks ⊢
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    omega
  simp only [pEffectiveCondition, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change ((pSecondPCount bits p).toNat +
      (individualEffectiveLower bits p).toNat + 1) % 256 ≤
    ((pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pEOut bits p).toNat) % 256
  have hRightSmall : (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
      (pEOut bits p).toNat < 256 := by
    have hpLe : (pOut bits p).toNat ≤ 6 := by
      rw [hBlocks.1]
      have hc : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
    have hhLe : (pHOut bits p).toNat ≤ 5 := by
      rw [hBlocks.2.1]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have heLe : (pEOut bits p).toNat ≤ 4 := by
      rw [hBlocks.2.2]
      have hc : ({q} ∪ C.Z).card = 4 := by
        rw [← Fintype.card_coe]
        have he' := (Fintype.card_congr L.e).symm
        norm_num at he'
        simpa only [Finset.singleton_union, Finset.mem_insert,
          Finset.mem_singleton] using he'
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hc
    omega
  rw [Nat.mod_eq_of_lt hRightSmall,
    Nat.mod_eq_of_lt (hNatural.trans_lt hRightSmall)]
  exact hNatural

theorem tightPrivate_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hNoRoot : epsilonS G C = 0) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 3) (hy : BSevenKTwo.y G C = 1) :
    tightPrivate (graphBits G L) = true := by
  let bits := graphBits G L
  let K := representedTargetSet G C q
  let T := G.secondOutNeighborFinset C.a1
  have hDegree : G.outdegree C.a1 = 8 := by
    rw [Shared.outdegree_a1_eq_k_add_r G C hG, hk, hr]
  have hOut : G.outNeighborFinset C.a1 = pivotNeighborSet G C := by
    exact Shared.outNeighborFinset_a1_eq_A1_union_P G C hG
  have hKSecond : K ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvX | hvE
    · exact BSixKThree.X_subset_second_a1 G C hG hvX
    · rcases Finset.mem_union.mp hvE with hvq | hvZ
      · have hvEq : v = q := Finset.mem_singleton.mp hvq
        subst v
        apply BSixKThree.Y_subset_second_a1 G C hG
        rw [BSixKThree.Y]
        apply Finset.mem_inter.mpr
        constructor
        · exact hqQ
        · have hReachedCard : (reachedQ G C).card = 1 := hy
          have hReachedEq : reachedQ G C = {q} := by
            obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hReachedCard
            have hwQ := (Finset.mem_inter.mp (by simp [hw] : w ∈ reachedQ G C)).1
            have hwq : w = q := by simpa [hQ] using hwQ
            simpa [hwq] using hw
          have hqReached : q ∈ reachedQ G C := by simp [hReachedEq]
          exact (Finset.mem_inter.mp hqReached).2
      · have hRootEmpty : rootSecondFinset G C = ∅ := by
          apply Finset.card_eq_zero.mp
          simpa [epsilonS] using hNoRoot
        apply BSixKThree.externalTargets_subset_second_a1 G C hG
        simpa [externalTargets, hRootEmpty] using hvZ
  have hTCard : T.card ≤ 7 := by
    have hNot : ¬G.IsSeymourVertex C.a1 := fun hs ↦ hNoSeymour ⟨C.a1, hs⟩
    have hlt := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
    unfold Digraph.secondOutdegree at hlt
    rw [hDegree] at hlt
    change T.card < 8 at hlt
    omega
  rw [tightPrivate, all_eq_true_iff]
  intro deleted hdeleted
  let d : Fin 8 := ⟨deleted, hdeleted⟩
  let u := pivotNeighborVertex G L deleted
  let S := (G.outNeighborFinset C.a1).erase u
  let E := G.outNeighborFinsetOf S \ (S ∪ {C.a1})
  have huOut : u ∈ G.outNeighborFinset C.a1 := by
    rw [hOut]
    exact (pivotNeighborEquiv G C q hqQ L hk d).2
  have hau : G.Adj C.a1 u :=
    (Digraph.mem_outNeighborFinset (G := G)).mp huOut
  have hExpansion : 7 ≤ E.card := by
    simpa [S, E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hau
  have hTargetSecond (target : Fin 7) :
      representedTargetVertex G L target.val ∈ T := by
    apply hKSecond
    exact (representedTargetEquiv G C q hqQ L hx target).2
  have hPrivateNotE (target : Fin 7)
      (hPrivate : privateTarget bits deleted target.val = true) :
      representedTargetVertex G L target.val ∉ E := by
    intro htE
    rcases Finset.mem_sdiff.mp htE with ⟨htReach, _⟩
    obtain ⟨middle, hmS, hmt⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
    have hmOut : middle ∈ G.outNeighborFinset C.a1 :=
      Finset.mem_of_mem_erase hmS
    have hmU : middle ∈ pivotNeighborSet G C := by simpa [hOut] using hmOut
    obtain ⟨other, hother⟩ :=
      (pivotNeighborEquiv G C q hqQ L hk).surjective ⟨middle, hmU⟩
    have hmiddle : pivotNeighborVertex G L other.val = middle :=
      congrArg Subtype.val hother
    have hne : other.val ≠ deleted := by
      intro heq
      have hmu : middle = u := by simp [u, ← hmiddle, heq]
      exact (Finset.mem_erase.mp hmS).1 hmu
    simp only [privateTarget, Bool.and_eq_true] at hPrivate
    have hAll := hPrivate.2
    rw [all_eq_true_iff] at hAll
    have hUnique := hAll other.val other.isLt
    simp only [hne, decide_false, Bool.false_or, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hUnique
    have hArc := coreArc_graphBits G C q hqQ L hG
      (uVertex other.val) (secondTarget target.val)
      (by unfold uVertex; split <;> omega)
      (by unfold secondTarget; split <;> omega)
    have hArcTrue : coreArc bits (uVertex other.val)
        (secondTarget target.val) = true := by
      rw [hArc]
      apply decide_eq_true
      change G.Adj (pivotNeighborVertex G L other.val)
        (representedTargetVertex G L target.val)
      simpa [hmiddle] using hmt
    rw [hArcTrue] at hUnique
    simp at hUnique
  have hMiss : (T \ E).card ≤ 1 := by
    simpa [T, S, E] using Digraph.oneArcDeletion_misses_at_most_one G hBound hG
      hNoSeymour hDegree hau
  have hCountOne : (count 7 (privateTarget bits deleted)).toNat ≤ 1 := by
    have hFilter := RSeven.XThreeNoRoot.GraphFacts.count_le_filterCard K
      (representedTargetEquiv G C q hqQ L hx)
      (privateTarget bits deleted) (fun v ↦ v ∈ T \ E) (by omega) (by
        intro target ht
        rw [representedTargetEquiv_val]
        exact Finset.mem_sdiff.mpr ⟨hTargetSecond target,
          hPrivateNotE target ht⟩)
    have hSubset : K.filter (fun v ↦ v ∈ T \ E) ⊆ T \ E := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    exact hFilter.trans ((Finset.card_le_card hSubset).trans hMiss)
  by_cases hReached : deletedReached bits deleted = true
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    change (count 7 (privateTarget bits deleted)).toNat ≤
      (bitCount (deletedReached bits deleted)).toNat
    rw [hReached]
    simpa [bitCount] using hCountOne
  · have hReachedFalse : deletedReached bits deleted = false :=
      Bool.eq_false_of_not_eq_true hReached
    have huNotE : u ∉ E := by
      intro huE
      rcases Finset.mem_sdiff.mp huE with ⟨huReach, _⟩
      obtain ⟨middle, hmS, hmu⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp huReach
      have hmOut : middle ∈ G.outNeighborFinset C.a1 :=
        Finset.mem_of_mem_erase hmS
      have hmU : middle ∈ pivotNeighborSet G C := by simpa [hOut] using hmOut
      obtain ⟨other, hother⟩ :=
        (pivotNeighborEquiv G C q hqQ L hk).surjective ⟨middle, hmU⟩
      have hmiddle : pivotNeighborVertex G L other.val = middle :=
        congrArg Subtype.val hother
      have hne : other.val ≠ deleted := by
        intro heq
        have hmu' : middle = u := by simp [u, ← hmiddle, heq]
        exact (Finset.mem_erase.mp hmS).1 hmu'
      have hArc := coreArc_graphBits G C q hqQ L hG
        (uVertex other.val) (uVertex deleted)
        (by unfold uVertex; split <;> omega)
        (by unfold uVertex; split <;> omega)
      have hArcTrue : coreArc bits (uVertex other.val) (uVertex deleted) = true := by
        rw [hArc]
        apply decide_eq_true
        change G.Adj (pivotNeighborVertex G L other.val) u
        simpa [hmiddle] using hmu
      have : deletedReached bits deleted = true := by
        rw [deletedReached, any_eq_true_iff]
        exact ⟨other.val, other.isLt, by simp [hne, hArcTrue]⟩
      exact hReached this
    have hESubset : E ⊆ T := by
      intro w hwE
      rcases Finset.mem_sdiff.mp hwE with ⟨hwReach, hwOutside⟩
      obtain ⟨middle, hmS, hmw⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
      have hwmid : G.Adj C.a1 middle :=
        (Digraph.mem_outNeighborFinset (G := G)).mp
          (Finset.mem_of_mem_erase hmS)
      have hwNeU : w ≠ u := fun hwu ↦ huNotE (hwu ▸ hwE)
      have hwNotS : w ∉ S := fun hwS ↦
        hwOutside (Finset.mem_union_left _ hwS)
      have hwNotDirect : ¬G.Adj C.a1 w := by
        intro haw
        have hwOut := (Digraph.mem_outNeighborFinset (G := G)).mpr haw
        exact hwNotS (Finset.mem_erase.mpr ⟨hwNeU, hwOut⟩)
      have hwNeA : w ≠ C.a1 := by
        intro hw
        subst w
        exact hwOutside (Finset.mem_union_right _ (Finset.mem_singleton_self C.a1))
      change w ∈ G.secondOutNeighborFinset C.a1
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨middle, hwmid, hmw⟩, hwNotDirect, hwNeA⟩
    have hNoPrivate : ∀ target : Fin 7,
        privateTarget bits deleted target.val = false := by
      intro target
      apply Bool.eq_false_of_not_eq_true
      intro ht
      have htNotE := hPrivateNotE target ht
      have hUnion : E ∪ {representedTargetVertex G L target.val} ⊆ T :=
        Finset.union_subset hESubset (by simpa using hTargetSecond target)
      have hCard := Finset.card_le_card hUnion
      have hUnionCard :
          (E ∪ {representedTargetVertex G L target.val}).card = E.card + 1 := by
        rw [Finset.card_union_of_disjoint]
        · simp
        · rw [Finset.disjoint_left]
          intro v hvE hvt
          exact htNotE (Finset.mem_singleton.mp hvt ▸ hvE)
      rw [hUnionCard] at hCard
      omega
    have hCountZero : (count 7 (privateTarget bits deleted)).toNat = 0 := by
      rw [toNat_count_eq_fin_sum 7 _ (by omega)]
      apply Finset.sum_eq_zero
      intro target _
      simp [hNoPrivate target]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    change (count 7 (privateTarget bits deleted)).toNat ≤
      (bitCount (deletedReached bits deleted)).toNat
    rw [hReachedFalse, hCountZero]
    simp [bitCount]

theorem anyExact_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : Labels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoRoot : epsilonS G C = 0) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 3) (hRCard : C.R.card = 2)
    (hy : BSevenKTwo.y G C = 1) :
    any 6 (isExact (graphBits G L)) = true := by
  have hPCard : C.P.card = 6 := hr
  have hHCard : C.H.card = 5 := by
    rw [BSevenKTwo.H_card_eq_x_add_two G C hk, hx]
  have hAOneQCap : edgeCount G C.A1 {q} ≤ 2 := by
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  have hHP0 := H_to_P_lower G C q hqQ hQ hG hMin hk hx hRCard hy
  have hHP : 16 ≤ edgeCount G C.H C.P := by omega
  have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  rw [hHCard, hPCard] at hCross
  have hPH : edgeCount G C.P C.H ≤ 14 := by omega
  have hPP : edgeCount G C.P C.P ≤ 15 := by
    have h := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at h
    norm_num [Nat.choose] at h
    exact h
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExternal : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hqZ : q ∉ C.Z := by
    intro hqZ
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqZ
      (Finset.mem_union_right ({C.s} ∪ C.A)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
  have hPEsplit : edgeCount G C.P ({q} ∪ C.Z) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [hQ, hExternal]
    apply edgeCount_union_of_disjoint
    rw [Finset.disjoint_left]
    intro v hvq hvz
    exact hqZ (Finset.mem_singleton.mp hvq ▸ hvz)
  have hPE : edgeCount G C.P C.Q +
      edgeCount G C.P (externalTargets G C) ≤ 24 := by
    rw [← hPEsplit]
    have h := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
    have he : ({q} ∪ C.Z).card = 4 := by
      rw [← Fintype.card_coe]
      have he' := (Fintype.card_congr L.e).symm
      norm_num at he'
      simpa only [Finset.mem_union, Finset.mem_singleton] using he'
    rw [hPCard, he] at h
    exact h
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hSumUpper : ∑ p ∈ C.P, G.outdegree p ≤ 53 := by omega
  have hExists : ∃ p ∈ C.P, G.outdegree p = 8 := by
    by_contra hn
    push Not at hn
    have hLower : 54 ≤ ∑ p ∈ C.P, G.outdegree p := by
      calc
        54 = ∑ _p ∈ C.P, 9 := by simp [hPCard]
        _ ≤ ∑ p ∈ C.P, G.outdegree p := by
          apply Finset.sum_le_sum
          intro p hp
          have hpMin := hMin p
          have hpNe := hn p hp
          omega
    omega
  obtain ⟨p, hpP, hpDegree⟩ := hExists
  obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hpP⟩
  rw [any_eq_true_iff]
  refine ⟨i.val, i.isLt, ?_⟩
  rw [isExact, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [directCount_graphBits_toNat G C q hqQ hQ L hG hNoRoot
    (8 + i.val) (by omega)]
  simp only [labelledVertex, dif_neg (by omega : ¬8 + i.val < 8),
    dif_pos (by omega : 8 + i.val < 14)]
  have hIndex : (⟨8 + i.val - 8, by omega⟩ : Fin 6) = i := by
    apply Fin.ext
    simp
  rw [hIndex, congrArg Subtype.val hi, hpDegree]
  decide

theorem three_le_aOneToXCount (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hx : C.x = 3) :
    3 ≤ (count 6 fun k =>
      let a := k / 3
      let x := k % 3
      aArc (graphBits G L) (1 + a) (3 + x)).toNat := by
  have hA1Card : C.A1.card = 2 := hk
  have hInternal : edgeCount G C.A1 C.A1 ≤ 1 := by
    have h := internal_edgeCount_le_choose_two G C.A1 hG
    norm_num [hA1Card, Nat.choose] at h ⊢
    exact h
  have hA1A : 4 ≤ edgeCount G C.A1 C.A := by
    unfold edgeCount
    calc
      4 = ∑ _u ∈ C.A1, 2 := by simp [hA1Card]
      _ ≤ ∑ u ∈ C.A1, Shared.directCount G C.A u := by
        apply Finset.sum_le_sum
        intro u hu
        have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C hu
        simpa [hk, Shared.directCount,
          CertificateBridge.internalFirstNeighbors] using (hPivot u huA).1
  have hA1RZero : edgeCount G C.A1 C.R = 0 := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r hr
    exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
      G C u r hu hr
  have hA1a1Zero : edgeCount G C.A1 {C.a1} = 0 := by
    unfold edgeCount Shared.directCount CertificateBridge.internalFirstNeighbors
    apply Finset.sum_eq_zero
    intro u hu
    have hn : ¬G.Adj u C.a1 := hG.2 (Finset.mem_filter.mp hu).2
    simp [hn]
  have hPartsR := Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hHa1 : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hv
    have hvEq : v = C.a1 := Finset.mem_singleton.mp hv
    subst v
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  have hADecomp : edgeCount G C.A1 C.A =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X := by
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C,
      edgeCount_union_of_disjoint G C.A1 (C.A1 ∪ C.X ∪ {C.a1}) C.R hPartsR,
      edgeCount_union_of_disjoint G C.A1 (C.A1 ∪ C.X) {C.a1} hHa1,
      edgeCount_union_of_disjoint G C.A1 C.A1 C.X
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C),
      hA1RZero, hA1a1Zero]
    omega
  have hThree : 3 ≤ edgeCount G C.A1 C.X := by omega
  have hRow (a : Fin 2) :
      Shared.directCount G C.X (L.a ⟨a.val + 1, by omega⟩).1 =
        ∑ x : Fin 3, if aArc (graphBits G L)
          (1 + a.val) (3 + x.val) then 1 else 0 := by
    apply directCount_eq_sum_bool G C.X (xEquiv G C q L hx) _
    intro x
    rw [aArc_coreBits G.Adj L (1 + a.val) (3 + x.val)
      (by omega) (by omega)]
    have hs : (⟨1 + a.val, by omega⟩ : Fin 8) =
        ⟨a.val + 1, by omega⟩ := Fin.ext
          (show 1 + a.val = a.val + 1 by omega)
    have ht : (⟨3 + x.val, by omega⟩ : Fin 8) =
        ⟨x.val + 3, by omega⟩ := Fin.ext
          (show 3 + x.val = x.val + 3 by omega)
    simp [hs, ht]
  have hCount : (count 6 fun k =>
      aArc (graphBits G L) (1 + k / 3) (3 + k % 3)).toNat =
      edgeCount G C.A1 C.X := by
    rw [toNat_count_eq_fin_sum 6 _ (by omega),
      edgeCount_eq_sum_fin G C.A1 C.X (aOneEquiv G C q L hk)]
    simp_rw [show ∀ i : Fin 2,
      (aOneEquiv G C q L hk i).1 = (L.a ⟨i.val + 1, by omega⟩).1 by
        intro i; rfl]
    simp_rw [hRow]
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  rw [hCount]
  exact hThree

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Assembly
