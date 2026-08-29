import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.Counts
import SeymourEight.DegreeEight

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared RepeatedSharedOmissionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (ThetaFourCore.count n f).toNat =
      ∑ i ∈ Finset.range n, (ThetaFourCore.bitCount (f i)).toNat := by
  induction n with
  | zero => simp [ThetaFourCore.count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hSumLe :
          (∑ i ∈ Finset.range n, (ThetaFourCore.bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [ThetaFourCore.count, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      have hLt0 :
          (∑ i ∈ Finset.range n,
            (ThetaFourCore.bitCount (f i)).toNat) < 256 := by omega
      have hLt1 :
          (∑ i ∈ Finset.range n,
            (ThetaFourCore.bitCount (f i)).toNat) + 1 < 256 := by omega
      cases hfn : f n
      · simpa [ThetaFourCore.bitCount, hfn] using Nat.mod_eq_of_lt hLt0
      · simpa [ThetaFourCore.bitCount, hfn] using Nat.mod_eq_of_lt hLt1

theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (ThetaFourCore.count n f).toNat = ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn,
    ← Fin.sum_univ_eq_sum_range
      (fun i ↦ (ThetaFourCore.bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [ThetaFourCore.bitCount]

theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    ThetaFourCore.all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [ThetaFourCore.all]
  | succ n ih =>
      simp only [ThetaFourCore.all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · simpa [show i = n by omega] using hn
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    ThetaFourCore.any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [ThetaFourCore.any]
  | succ n ih =>
      simp only [ThetaFourCore.any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hLast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hLast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · exact Or.inr (show i = n by omega ▸ hfi)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (ThetaFourCore.count n b).toNat ≤ (S.filter Q).card := by
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · simp [hb, hGood j hb]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

theorem root_tail_absent (C : G.LocalConfiguration)
    (hRoot : edgeCount G C.P {C.s} = 0) {p : V} (hp : p ∈ C.P) :
    ¬G.Adj p C.s := by
  intro hps
  have hPositive : 0 < directCount G {C.s} p := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    exact Finset.card_pos.mpr ⟨C.s,
      Finset.mem_filter.mpr ⟨Finset.mem_singleton_self _, hps⟩⟩
  have hTerm : directCount G {C.s} p ≤ edgeCount G C.P {C.s} := by
    unfold edgeCount
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
  omega

theorem A_outgoingCaptured_retained (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outNeighborFinset u ⊆ retainedVertexSet G C := by
  intro v hv
  rcases Finset.mem_union.mp (A_outgoingCaptured G C hG u hu hv) with hvA | hvB
  · exact Finset.mem_union_left C.Z (Finset.mem_union_left C.P hvA)
  · exact Finset.mem_union_left C.Z
      (Finset.mem_union_right C.A (by simpa [hPB] using hvB))

theorem P_outgoingCaptured_retained (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hRoot : edgeCount G C.P {C.s} = 0) (u : V) (hu : u ∈ C.P) :
    G.outNeighborFinset u ⊆ retainedVertexSet G C := by
  intro v hv
  have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hv
  have hcap := outgoingCaptured_of_p_eq_B G C hG hPB u hu hv
  simp only [Finset.mem_union, Finset.mem_singleton] at hcap
  rcases hcap with ((hvZ | hvs) | hvH) | hvP
  · exact Finset.mem_union_right (C.A ∪ C.P) hvZ
  · subst v
    exact (root_tail_absent G C hRoot hu hadj).elim
  · exact Finset.mem_union_left C.Z (Finset.mem_union_left C.P
      (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH))
  · exact Finset.mem_union_left C.Z (Finset.mem_union_right C.A hvP)

theorem directCount_coreBits_toNat (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hRoot : edgeCount G C.P {C.s} = 0)
    (source : Nat) (hs : source < 15) :
    (ThetaFourCore.directCount
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source).toNat =
      G.outdegree (labelledVertex G L source) := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  rw [ThetaFourCore.directCount, toNat_count_eq_fin_sum 19 _ (by omega)]
  have hCount : (∑ j : Fin 19, if ThetaFourCore.coreArc bits source j then 1 else 0) =
      directCount G (retainedVertexSet G C) (labelledVertex G L source) := by
    symm
    apply directCount_eq_sum_bool G (retainedVertexSet G C)
      (retainedLabelEquiv G C L) _
    intro j
    rw [retainedLabelEquiv_val]
    rw [coreArc_coreBits G C L hG T.p_complete T.ph_complete source j hs j.isLt]
    simp
  rw [hCount]
  apply (outdegree_eq_directCount_of_captured G _ _ ?_).symm
  by_cases hsA : source < 8
  · have heq : labelledVertex G L source = (L.a ⟨source, hsA⟩).1 := by
      simp [labelledVertex, hsA]
    rw [heq]
    exact A_outgoingCaptured_retained G C hG T.p_eq_B _ (L.a _).2
  · have heq : labelledVertex G L source = (L.p ⟨source - 8, by omega⟩).1 := by
      simp [labelledVertex, hsA, hs]
    rw [heq]
    exact P_outgoingCaptured_retained G C hG T.p_eq_B hRoot _ (L.p _).2

theorem strictSecondLocal_true_mem (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (source target : Nat) (hs : source < 15)
    (ht : target < 19)
    (hSecond : ThetaFourCore.strictSecondLocal
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source target = true) :
    labelledVertex G L target ∈ G.secondOutNeighborFinset (labelledVertex G L source) := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  simp only [ThetaFourCore.strictSecondLocal, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_coreBits G C L hG T.p_complete T.ph_complete source middle hs
    (by omega)]
    at hFirst
  rw [coreArc_coreBits G C L hG T.p_complete T.ph_complete middle target hm ht]
    at hLast
  rw [coreArc_coreBits G C L hG T.p_complete T.ph_complete source target hs ht]
    at hNotArc
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 19) = ⟨source, by omega⟩ := by
      apply (retainedLabelEquiv G C L).injective
      apply Subtype.ext
      simpa [retainedLabelEquiv_val] using heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

theorem localSecondCount_le_graph (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (source : Nat) (hs : source < 15) :
    (ThetaFourCore.localSecondCount
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hFiltered := count_le_filterCard (V := V) (retainedVertexSet G C)
    (retainedLabelEquiv G C L) (ThetaFourCore.strictSecondLocal bits source)
    (fun v => v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    (by omega) (by
      intro j hj
      rw [retainedLabelEquiv_val]
      exact strictSecondLocal_true_mem G C L T hG source j hs j.isLt hj)
  unfold ThetaFourCore.localSecondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

theorem nonSeymour_coreBits_true (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (source : Nat) (hs : source < 15) :
    (ThetaFourCore.localSecondCount
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source).ult
      (ThetaFourCore.directCount
        (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
          (fun i ↦ (L.z i).1)) source) = true := by
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [directCount_coreBits_toNat G C L T hG hRoot source hs]
  exact (localSecondCount_le_graph G C L T hG source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h => hNoSeymour ⟨labelledVertex G L source, h⟩))

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
