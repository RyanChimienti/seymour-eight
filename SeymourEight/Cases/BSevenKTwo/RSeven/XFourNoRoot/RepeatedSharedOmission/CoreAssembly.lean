import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.Structure
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared RepeatedSharedOmissionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (ThetaFourCore.sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [ThetaFourCore.sumCount]
  | succ n ih =>
      rw [ThetaFourCore.sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem A_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outdegree u = directCount G C.A u + directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hCap := A_outgoingCaptured G C hG u hu
  have hEq := outdegree_eq_directCount_of_captured G (C.A ∪ C.P) u (by
    intro v hv
    simpa [hPB] using hCap hv)
  rw [directCount_union_of_disjoint G C.A C.P u hAP] at hEq
  exact hEq

theorem orientedA_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hG : G.IsOriented) :
    ThetaFourCore.orientedA
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = true := by
  rw [ThetaFourCore.orientedA, all_eq_true_iff]
  intro i hi
  rw [Bool.and_eq_true, aArc_coreBits G.Adj _ _ _ i i hi hi]
  constructor
  · simpa using hG.1 (L.a ⟨i, hi⟩).1
  · rw [all_eq_true_iff]
    intro j hj
    rw [aArc_coreBits G.Adj _ _ _ i j hi hj,
      aArc_coreBits G.Adj _ _ _ j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    · by_cases h : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
      · simp [h, hG.2 h]
      · simp [h]

theorem fixedA_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (_hG : G.IsOriented) :
    ThetaFourCore.fixedA
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = true := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have h01 : ThetaFourCore.aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj _ _ _ 0 1 (by omega) (by omega)]
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      have hfin : (⟨0, by omega⟩ : Fin 8) = 0 := by rfl
      rw [hfin]
      exact L.a_zero
    rw [ha0]
    simpa using (Finset.mem_filter.mp (L.a_aOne 0)).2
  have h02 : ThetaFourCore.aArc bits 0 2 = true := by
    rw [aArc_coreBits G.Adj _ _ _ 0 2 (by omega) (by omega)]
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      have hfin : (⟨0, by omega⟩ : Fin 8) = 0 := by rfl
      rw [hfin]
      exact L.a_zero
    rw [ha0]
    simpa using (Finset.mem_filter.mp (L.a_aOne 1)).2
  have hTail : ThetaFourCore.all 5 (fun i => !ThetaFourCore.aArc bits 0 (3+i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [aArc_coreBits G.Adj _ _ _ 0 (3+i) (by omega) (by omega)]
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      have hfin : (⟨0, by omega⟩ : Fin 8) = 0 := by rfl
      rw [hfin]
      exact L.a_zero
    rw [ha0]
    by_cases hi4 : i < 4
    · have hx := L.a_x ⟨i, hi4⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3+i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hA1
            (by simpa [Nat.add_comm] using hx)
      simp [hn]
    · have hiEq : i = 4 := by omega
      subst i
      have hn : ¬G.Adj C.a1 (L.a 7).1 := by
        intro ha
        have hA1 : (L.a 7).1 ∈ C.A1 := Finset.mem_filter.mpr ⟨(L.a 7).2, ha⟩
        exact (Finset.mem_sdiff.mp L.a_r).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
      simp [hn]
  have h17Arc : ThetaFourCore.aArc bits 1 7 = false := by
    rw [aArc_coreBits G.Adj _ _ _ 1 7 (by omega) (by omega)]
    exact decide_eq_false (by
      simpa using
      A1_not_adj_R G C _ _ (L.a_aOne 0) L.a_r
    )
  have h27Arc : ThetaFourCore.aArc bits 2 7 = false := by
    rw [aArc_coreBits G.Adj _ _ _ 2 7 (by omega) (by omega)]
    exact decide_eq_false (by
      simpa using
      A1_not_adj_R G C _ _ (L.a_aOne 1) L.a_r
    )
  have h17 : (!ThetaFourCore.aArc bits 1 7) = true := by simp [h17Arc]
  have h27 : (!ThetaFourCore.aArc bits 2 7) = true := by simp [h27Arc]
  simp only [ThetaFourCore.fixedA, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h01, h02⟩, hTail⟩, h17⟩, h27⟩

theorem everyXReached_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (hk : C.k = 2) :
    ThetaFourCore.everyXReached
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = true := by
  rw [ThetaFourCore.everyXReached, all_eq_true_iff]
  intro x hx
  have hxMem := L.a_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [any_eq_true_iff]
    have hne : (L.a (1 : Fin 8)).1 ≠ (L.a (2 : Fin 8)).1 := by
      intro h
      have := L.a.injective (Subtype.ext h)
      omega
    have hPairCard : ({(L.a (1 : Fin 8)).1, (L.a (2 : Fin 8)).1} : Finset V).card = 2 := by
      simp [hne]
    have hPairSubset : ({(L.a (1 : Fin 8)).1, (L.a (2 : Fin 8)).1} : Finset V) ⊆ C.A1 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact L.a_aOne 0
      · exact L.a_aOne 1
    have hA1Card : C.A1.card = 2 := by
      change C.k = 2
      exact hk
    have hA1Eq : ({(L.a (1 : Fin 8)).1, (L.a (2 : Fin 8)).1} : Finset V) = C.A1 :=
      Finset.eq_of_subset_of_card_le hPairSubset (by omega)
    have huCases : u = (L.a (1 : Fin 8)).1 ∨ u = (L.a (2 : Fin 8)).1 := by
      rw [← hA1Eq] at huA1
      simpa [eq_comm] using huA1
    rcases huCases with h1 | h2
    · refine ⟨0, by omega, ?_⟩
      rw [aArc_coreBits G.Adj _ _ _ 1 (3+x) (by omega) (by omega)]
      simpa [Nat.add_comm, h1] using hux
    · refine ⟨1, by omega, ?_⟩
      rw [aArc_coreBits G.Adj _ _ _ 2 (3+x) (by omega) (by omega)]
      simpa [Nat.add_comm, h2] using hux
  · rw [Bool.or_eq_true]
    right
    rw [any_eq_true_iff]
    obtain ⟨pi, hpi⟩ := L.p.surjective ⟨u, huP⟩
    refine ⟨pi, pi.isLt, ?_⟩
    rw [pToH_coreBits G.Adj _ _ _ pi (2+x) pi.isLt (by omega)]
    simpa [Nat.add_comm, Nat.add_left_comm, congrArg Subtype.val hpi] using hux

theorem aMinimumAndDegree_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hk : C.k = 2) :
    ThetaFourCore.aMinimumAndDegree
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) = true := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  rw [ThetaFourCore.aMinimumAndDegree, all_eq_true_iff]
  intro a ha
  have hAO := aOut_toNat G C L a ha
  have hPO := aPOut_toNat G C L T hG a ha
  have hPivotA := hPivot (L.a ⟨a, ha⟩).1 (L.a ⟨a, ha⟩).2
  have hAmin : 2 ≤ (ThetaFourCore.aOut bits a).toNat := by
    rw [hAO]
    simpa [hk, directCount, CertificateBridge.internalFirstNeighbors] using hPivotA.1
  have hTie : (ThetaFourCore.aOut bits a).toNat = 2 →
      7 ≤ (ThetaFourCore.aPOut bits a).toNat := by
    intro heq
    rw [hPO]
    have hr : C.r = 7 := by
      change C.P.card = 7
      simpa using (Fintype.card_congr L.p).symm
    have hCardEq : (C.A.filter (G.Adj (L.a ⟨a, ha⟩).1)).card = C.k := by
      rw [hk]
      change directCount G C.A (L.a ⟨a, ha⟩).1 = 2
      rw [← hAO]
      exact heq
    have hTieB := hPivotA.2 hCardEq
    change C.r ≤ directCount G C.B (L.a ⟨a, ha⟩).1 at hTieB
    rw [← T.p_eq_B] at hTieB
    simpa [hr] using hTieB
  have hTotal : 8 ≤ (ThetaFourCore.aOut bits a).toNat +
      (ThetaFourCore.aPOut bits a).toNat := by
    rw [hAO, hPO, ← A_outdegree_eq_A_add_P G C hG T.p_eq_B _ (L.a _).2]
    exact hMin _
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
      exact hAmin
    · rw [Bool.or_eq_true]
      by_cases heq : ThetaFourCore.aOut bits a = 2
      · right
        norm_num [BitVec.ule_eq_decide, decide_eq_true_eq]
        exact hTie (congrArg BitVec.toNat heq)
      · left
        simpa using heq
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [BitVec.toNat_add]
    have hlt : (ThetaFourCore.aOut bits a).toNat +
        (ThetaFourCore.aPOut bits a).toNat < 256 := by
      have hA : directCount G C.A (L.a ⟨a, ha⟩).1 ≤ C.A.card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have hP : directCount G C.P (L.a ⟨a, ha⟩).1 ≤ C.P.card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      rw [hAO, hPO]
      have hcA : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
      have hcP : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
      omega
    rw [Nat.mod_eq_of_lt hlt]
    exact hTotal

theorem pDegreeEight_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hRoot : edgeCount G C.P {C.s} = 0)
    (hHCard : C.H.card = 6) :
    ThetaFourCore.pDegreeEight
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = true := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  rw [ThetaFourCore.pDegreeEight, all_eq_true_iff]
  intro p hp
  have hBlocks := pBlockCounts G C L T hG hHCard p hp
  have hDegree := T.p_degree ⟨p, hp⟩
  have hCaptured : G.outNeighborFinset (L.p ⟨p, hp⟩).1 ⊆
      C.Z ∪ C.H ∪ C.P := by
    intro v hv
    have hc := outgoingCaptured_of_p_eq_B G C hG T.p_eq_B _ (L.p _).2 hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hc ⊢
    rcases hc with ((hz | hs) | hh) | hp'
    · exact Or.inl (Or.inl hz)
    · subst v
      exact (root_tail_absent G C hRoot (L.p _).2
        ((Digraph.mem_outNeighborFinset (G := G)).mp hv)).elim
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hp'
  have hZH : Disjoint C.Z C.H :=
    Digraph.LocalConfiguration.disjoint_Z_H (G := G) C
  have hZHP : Disjoint (C.Z ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hvZH hvP
    rcases Finset.mem_union.mp hvZH with hvZ | hvH
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  have hGraph : G.outdegree (L.p ⟨p, hp⟩).1 =
      directCount G C.Z (L.p ⟨p, hp⟩).1 +
      directCount G C.H (L.p ⟨p, hp⟩).1 +
      directCount G C.P (L.p ⟨p, hp⟩).1 := by
    have h := outdegree_eq_directCount_of_captured G (C.Z ∪ C.H ∪ C.P)
      (L.p ⟨p, hp⟩).1 hCaptured
    rw [directCount_union_of_disjoint G (C.Z ∪ C.H) C.P _ hZHP,
      directCount_union_of_disjoint G C.Z C.H _ hZH] at h
    exact h
  have hNat : (ThetaFourCore.pOut bits p).toNat +
      (ThetaFourCore.pHOut bits p).toNat +
      (ThetaFourCore.pZOut bits p).toNat = 8 := by
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    omega
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have hSmall : (ThetaFourCore.pOut bits p).toNat +
      (ThetaFourCore.pHOut bits p).toNat < 256 := by
    omega
  rw [Nat.mod_eq_of_lt hSmall]
  have hSmall' : (ThetaFourCore.pOut bits p).toNat +
      (ThetaFourCore.pHOut bits p).toNat +
      (ThetaFourCore.pZOut bits p).toNat < 256 := by
    omega
  rw [Nat.mod_eq_of_lt hSmall']
  exact hNat

theorem pHOutSum_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hHCard : C.H.card = 6) :
    ThetaFourCore.sumCount 7 (ThetaFourCore.pHOut
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1))) = 13 := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sumCount, show (13 : BitVec 8).toNat = 13 by decide]
  have hEach : ∀ i : Fin 7, (ThetaFourCore.pHOut bits i).toNat =
      directCount G C.H (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L T hG hHCard i i.isLt).2.1
  rw [show (∑ i ∈ Finset.range 7, (ThetaFourCore.pHOut bits i).toNat) =
      edgeCount G C.P C.H by
    rw [edgeCount_eq_sum_fin G C.P C.H L.p, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)]
  norm_num [T.p_to_h]

theorem profile_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hHCard : C.H.card = 6) :
    ThetaFourCore.profile
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = true := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hz (i : Fin 7) : (ThetaFourCore.pZOut bits i).toNat =
      profileDirectCount i := by
    rw [(pBlockCounts G C L T hG hHCard i i.isLt).2.2, L.p_z_count]
  simp only [ThetaFourCore.profile, Bool.and_eq_true, beq_iff_eq]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
  · simpa [profileDirectCount] using hz 0
  · simpa [profileDirectCount] using hz 1
  · simpa [profileDirectCount] using hz 2
  · simpa [profileDirectCount] using hz 3
  · simpa [profileDirectCount] using hz 4
  · simpa [profileDirectCount] using hz 5
  · simpa [profileDirectCount] using hz 6

theorem signatureCapacity_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) :
    ThetaFourCore.signatureCapacity
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = true := by
  rw [ThetaFourCore.signatureCapacity, Bool.and_eq_true]
  constructor
  · rw [all_eq_true_iff]
    intro mask hm
    rw [signatureCount_coreBits G.Adj _ _ _ mask hm]
    decide
  · rw [all_eq_true_iff]
    intro z hz
    simp [ThetaFourCore.sumCount, signatureCount_coreBits G.Adj]

theorem aNonSeymour_all_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0) :
    ThetaFourCore.all 8 (ThetaFourCore.aNonSeymour
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1))) = true := by
  rw [all_eq_true_iff]
  intro a ha
  exact nonSeymour_coreBits_true G C L T hG hNoSeymour hRoot a (by omega)

theorem pNonSeymour_all_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0) :
    ThetaFourCore.all 7 (ThetaFourCore.pNonSeymour
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1))) = true := by
  rw [all_eq_true_iff]
  intro p hp
  simp only [ThetaFourCore.pNonSeymour]
  have hOutside : ThetaFourCore.outsideSecondCount
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) p = 0 := by
    simp [ThetaFourCore.outsideSecondCount, ThetaFourCore.sumCount,
      signatureCount_coreBits G.Adj]
  simpa [hOutside] using
    nonSeymour_coreBits_true G C L T hG hNoSeymour hRoot (8 + p) (by omega)

theorem hMissingPairs_zero (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (_hG : G.IsOriented) :
    ThetaFourCore.hMissingPairs
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) = 0 := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  apply BitVec.eq_of_toNat_eq
  rw [ThetaFourCore.hMissingPairs, toNat_count_eq_fin_sum 36 _ (by omega)]
  change (∑ q : Fin 36, if
      (decide (q.1 / 6 < q.1 % 6) &&
        !ThetaFourCore.aArc bits (1 + q.1 / 6) (1 + q.1 % 6) &&
        !ThetaFourCore.aArc bits (1 + q.1 % 6) (1 + q.1 / 6))
      then 1 else 0) = 0
  apply Finset.sum_eq_zero
  intro q hq
  simp only [ite_eq_right_iff]
  intro hmiss
  rcases (Bool.and_eq_true _ _).mp hmiss with ⟨hleft, hjiArc⟩
  rcases (Bool.and_eq_true _ _).mp hleft with ⟨hijBool, hijArc⟩
  have hij := of_decide_eq_true hijBool
  have hi : q.1 / 6 < 6 := Nat.div_lt_of_lt_mul (by omega)
  have hj : q.1 % 6 < 6 := Nat.mod_lt _ (by omega)
  have hne : (⟨q.1 / 6, hi⟩ : Fin 6) ≠ ⟨q.1 % 6, hj⟩ := by
    intro heq
    have hval := Fin.ext_iff.mp heq
    exact (Nat.ne_of_lt hij) hval
  rcases T.h_complete ⟨q.1 / 6, hi⟩ ⟨q.1 % 6, hj⟩ hne with h | h
  · rw [aArc_coreBits G.Adj _ _ _ (1 + q.1 / 6) (1 + q.1 % 6) (by omega)
      (by omega)] at hijArc
    have h' : G.Adj (L.a ⟨1 + q.1 / 6, by omega⟩).1
        (L.a ⟨1 + q.1 % 6, by omega⟩).1 := by
      simpa [Nat.add_comm] using h
    simp [h'] at hijArc
  · rw [aArc_coreBits G.Adj _ _ _ (1 + q.1 % 6) (1 + q.1 / 6) (by omega)
      (by omega)] at hjiArc
    have h' : G.Adj (L.a ⟨1 + q.1 % 6, by omega⟩).1
        (L.a ⟨1 + q.1 / 6, by omega⟩).1 := by
      simpa [Nat.add_comm] using h
    simp [h'] at hjiArc

theorem mixedPatterns_true (C : G.LocalConfiguration)
    (L : MixedOmissionLabels G C) :
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 0 false false true true = true ∧
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 1 false true true true = true ∧
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 2 true true false true = true := by
  simp [ThetaFourCore.pZPattern, L.p0_pattern, L.p1_pattern, L.p2_pattern]

theorem selectedPatterns_true (C : G.LocalConfiguration)
    (L : RepeatedSharedOmissionLabels G C) :
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 0 false false true true = true ∧
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 1 false true true true = true ∧
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 2 true true false true = true ∧
    ThetaFourCore.pZPattern
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) 3 true true false true = true := by
  simp [ThetaFourCore.pZPattern, L.p0_pattern, L.p1_pattern,
    L.p2_pattern, L.p3_pattern]

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
