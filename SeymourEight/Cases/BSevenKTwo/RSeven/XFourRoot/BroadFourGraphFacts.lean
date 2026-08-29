import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.BroadFourLabels
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.BooleanBridge
import Mathlib.Data.Bool.Basic

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Graph facts for the broad four-`Z` certificate

The Boolean core stores only genuine adjacency blocks.  This file proves the
label and counting identities shared by the high-defect bridge.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge

open Shared XFourNoRoot.BroadFourCore BroadFourLabels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

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

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (count n b).toNat ≤ (S.filter Q).card := by
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · simp [hb, hGood j hb]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

def retainedVertexSet (C : G.LocalConfiguration) : Finset V := C.A ∪ C.P ∪ (externalTargets G C)

def labelledVertex (L : Labels G C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 15 then (L.p ⟨n - 8, by omega⟩).1
  else if hnZ : n < 19 then (L.z ⟨n - 15, by omega⟩).1
  else (L.z 0).1

noncomputable def retainedLabelEquiv (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) :
    Fin 19 ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin 19 → {v : V // v ∈ retainedVertexSet G C} := fun i ↦
    if hiA : i.val < 8 then
      ⟨(L.a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left (externalTargets G C) (Finset.mem_union_left C.P (L.a _).2)⟩
    else if hiP : i.val < 15 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left (externalTargets G C) (Finset.mem_union_right C.A (L.p _).2)⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1,
      Finset.mem_union_right (C.A ∪ C.P) (L.z _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAP | hvZ
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega,
          show i.val + 8 < 15 by omega] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 15 by omega] using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hAPZ : Disjoint (C.A ∪ C.P) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvAP hvZ
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
          · simp [rootSecondFinset, hReach] at hvRoot
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
          · simp [rootSecondFinset, hReach] at hvRoot
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp,
      retainedVertexSet, Finset.card_union_of_disjoint hAPZ,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hz : (externalTargets G C).card = 4 := by simpa using (Fintype.card_congr L.z).symm
    simp [ha, hp, hz]

@[simp] theorem retainedLabelEquiv_val (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (i : Fin 19) :
    (retainedLabelEquiv G C L hG i).1 = labelledVertex G L i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (L : Labels G C) (hHCard : C.H.card = 6) :
    Fin 6 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 6 → {v : V // v ∈ C.H} := fun i ↦
    ⟨(L.a ⟨i + 1, by omega⟩).1, by
      by_cases hi : i.val < 2
      · exact Finset.mem_union_left C.X (L.a_aOne ⟨i, hi⟩)
      · apply Finset.mem_union_right C.A1
        simpa [show i.val - 2 + 3 = i.val + 1 by omega] using
          L.a_x ⟨i - 2, by omega⟩⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have hidx : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hij
    exact Nat.add_right_cancel (congrArg Fin.val hidx)
  · simpa using hHCard.symm

@[simp] theorem hLabelEquiv_val (C : G.LocalConfiguration)
    (L : Labels G C) (hHCard : C.H.card = 6) (i : Fin 6) :
    (hLabelEquiv G C L hHCard i).1 = (L.a ⟨i + 1, by omega⟩).1 := by
  rfl

theorem A_not_adj_external (C : G.LocalConfiguration) (hG : G.IsOriented)
    (u v : V) (hu : u ∈ C.A) (hv : v ∈ externalTargets G C) : ¬G.Adj u v := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · exact XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
      G C hG u v hu hvZ
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      intro hus
      have hsu : G.Adj C.s u := (Digraph.mem_outNeighborFinset (G := G)).mp hu
      exact hG.2 hsu hus
    · simp [rootSecondFinset, hReach] at hvRoot

theorem A_outgoingCaptured_retained (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.A) :
    G.outNeighborFinset u ⊆ retainedVertexSet G C := by
  intro v hv
  rcases Finset.mem_union.mp
      (XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG u hu hv) with hvA | hvB
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvA)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa [hPB] using hvB))

theorem P_outgoingCaptured_retained (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.P) :
    G.outNeighborFinset u ⊆ retainedVertexSet G C := by
  intro v hv
  have huv := (Digraph.mem_outNeighborFinset (G := G)).mp hv
  have hcap := outgoingCaptured_of_p_eq_B G C hG hPB u hu hv
  simp only [Finset.mem_union, Finset.mem_singleton] at hcap
  rcases hcap with ((hvZ | hvs) | hvH) | hvP
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hvZ)
  · subst v
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (by
      simp [rootSecondFinset, show ∃ p ∈ C.P, G.Adj p C.s from ⟨u, hu, huv⟩]))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvP)

theorem coreArc_coreBits (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (source target : Nat)
    (hs : source < 15) (ht : target < 19) :
    coreArc (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  let bits := XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hA0P : ∀ i : Fin 7, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i ↦ hG.2 (hA0P i)
  have hPR : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 7).1 :=
    fun i ↦ XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R G C _ _ (L.p i).2 L.a_r
  unfold coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA, XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ source target hsA htA]
      simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP]
        have hti : target - 8 < 7 := by omega
        unfold aToP
        by_cases hs0 : source = 0
        · subst source
          simp [hA0P, labelledVertex, htA, htP]
        by_cases hs7 : source < 7
        · have hsh : source - 1 < 6 := by omega
          rw [if_neg hs0, if_pos hs7, XFourNoRoot.BroadFourBridge.hToP_coreBits G.Adj _ _ _
            (source - 1) (target - 8) hsh hti]
          have haeq : (L.a ⟨source - 1 + 1, by omega⟩).1 =
              (L.a ⟨source, hsA⟩).1 := by
            have hfin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
                ⟨source, hsA⟩ := Fin.ext (by simp; omega)
            rw [hfin]
          rw [haeq]
          simp [labelledVertex, hsA, htA, htP]
        · have hsEq : source = 7 := by omega
          subst source
          rw [if_neg (by omega : ¬7 = 0), if_neg (by omega : ¬7 < 7),
            XFourNoRoot.BroadFourBridge.rToP_coreBits G.Adj _ _ _ (target - 8) hti]
          simp [labelledVertex, htA, htP]
      · simp [htP, ht, labelledVertex, hsA, htA,
          A_not_adj_external G C hG (L.a ⟨source, hsA⟩).1
            (L.z ⟨target - 15, by omega⟩).1 (L.a _).2 (L.z _).2]
  · have hsP : source < 15 := hs
    rw [if_neg hsA, if_pos hsP]
    by_cases htA : target < 8
    · rw [if_pos htA]
      unfold pToA
      by_cases htH : 0 < target ∧ target < 7
      · rw [if_pos (by simpa [Bool.and_eq_true] using htH),
          XFourNoRoot.BroadFourBridge.pToH_coreBits G.Adj _ _ _ (source - 8) (target - 1)
            (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA,
          show target - 1 + 1 = target by omega]
      · rw [if_neg (by simpa [Bool.and_eq_true] using htH)]
        have htCase : target = 0 ∨ target = 7 := by omega
        rcases htCase with rfl | rfl
        · simp [labelledVertex, hsA, hsP, hP0]
        · simp [labelledVertex, hsA, hsP, hPR]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP, XFourNoRoot.BroadFourBridge.pArc_coreBits G.Adj _ _ _
          (source - 8) (target - 8) (by omega) (by omega)]
        have hImp : G.Adj (L.p ⟨source - 8, by omega⟩).1
            (L.p ⟨target - 8, by omega⟩).1 →
            source - 8 ≠ target - 8 := by
          intro hadj hij
          apply hG.1 (L.p ⟨source - 8, by omega⟩).1
          have hfin : (⟨source - 8, by omega⟩ : Fin 7) =
              ⟨target - 8, by omega⟩ := Fin.ext hij
          simpa [hfin] using hadj
        rw [show decide (source - 8 ≠ target - 8 ∧
            G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) =
            decide (G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) by
          exact Bool.decide_congr ⟨And.right, fun h ↦ ⟨hImp h, h⟩⟩]
        simp [labelledVertex, hsA, hsP, htA, htP]
      · rw [if_neg htP, if_pos ht,
          XFourNoRoot.BroadFourBridge.pToZ_coreBits G.Adj _ _ _ (source - 8) (target - 15)
            (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, htP, ht]

theorem directCount_coreBits_toNat (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (source : Nat) (hs : source < 15) :
    (XFourNoRoot.BroadFourCore.directCount (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1)
      (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)) source).toNat =
      G.outdegree (labelledVertex G L source) := by
  let bits := XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  rw [XFourNoRoot.BroadFourCore.directCount, toNat_count_eq_fin_sum 19 _ (by omega)]
  have hCount : (∑ j : Fin 19, if coreArc bits source j then 1 else 0) =
      Shared.directCount G (retainedVertexSet G C)
        (labelledVertex G L source) := by
    symm
    apply directCount_eq_sum_bool G (retainedVertexSet G C)
      (retainedLabelEquiv G C L hG) _
    intro j
    rw [retainedLabelEquiv_val G C L hG,
      coreArc_coreBits G C L hG source j hs j.isLt]
    simp
  rw [hCount]
  apply (outdegree_eq_directCount_of_captured G _ _ ?_).symm
  by_cases hsA : source < 8
  · have heq : labelledVertex G L source = (L.a ⟨source, hsA⟩).1 := by
      simp [labelledVertex, hsA]
    rw [heq]
    exact A_outgoingCaptured_retained G C hG hPB _ (L.a _).2
  · have heq : labelledVertex G L source =
        (L.p ⟨source - 8, by omega⟩).1 := by
      simp [labelledVertex, hsA, hs]
    rw [heq]
    exact P_outgoingCaptured_retained G C hG hPB _ (L.p _).2

theorem strictSecondLocal_true_mem (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented)
    (source target : Nat) (hs : source < 15) (ht : target < 19)
    (hSecond : strictSecondLocal
      (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  let bits := XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_coreBits G C L hG source middle hs (by omega)] at hFirst
  rw [coreArc_coreBits G C L hG middle target hm ht] at hLast
  rw [coreArc_coreBits G C L hG source target hs ht] at hNotArc
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 19) = ⟨source, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa [retainedLabelEquiv_val G C L hG] using heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

theorem localSecondCount_le_graph (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (source : Nat) (hs : source < 15) :
    (localSecondCount (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1)
      (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  let bits := XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hFiltered := count_le_filterCard (V := V) (retainedVertexSet G C)
    (retainedLabelEquiv G C L hG) (strictSecondLocal bits source)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    (by omega) (by
      intro j hj
      rw [retainedLabelEquiv_val G C L hG]
      exact strictSecondLocal_true_mem G C L hG source j hs j.isLt hj)
  unfold localSecondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

theorem nonSeymour_coreBits_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 15) :
    (localSecondCount (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1)
      (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)) source).ult
      (XFourNoRoot.BroadFourCore.directCount (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1)
        (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)) source) = true := by
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [directCount_coreBits_toNat G C L hG hPB source hs]
  exact (localSecondCount_le_graph G C L hG source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨labelledVertex G L source, h⟩))

theorem aOut_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (source : Nat) (hs : source < 8) :
    (aOut (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) source).toNat =
      Shared.directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  rw [XFourNoRoot.BroadFourBridge.aArc_coreBits G.Adj _ _ _ source j hs j.isLt]
  simp

theorem aPOut_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (_hG : G.IsOriented) (source : Nat) (hs : source < 8) :
    (aPOut (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) source).toNat =
      Shared.directCount G C.P (L.a ⟨source, hs⟩).1 := by
  rw [aPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  have hA0P : ∀ i : Fin 7, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  unfold aToP
  by_cases hs0 : source = 0
  · subst source
    simp [hA0P]
  by_cases hs7 : source < 7
  · have hsh : source - 1 < 6 := by omega
    rw [if_neg hs0, if_pos hs7,
      XFourNoRoot.BroadFourBridge.hToP_coreBits G.Adj _ _ _ (source - 1) j hsh j.isLt]
    have hfin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
        ⟨source, hs⟩ := Fin.ext (by simp; omega)
    simp [hfin]
  · have hsEq : source = 7 := by omega
    subst source
    rw [if_neg (by omega : ¬7 = 0), if_neg (by omega : ¬7 < 7),
      XFourNoRoot.BroadFourBridge.rToP_coreBits G.Adj _ _ _ j j.isLt]
    simp

theorem pBlockCounts (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hHCard : C.H.card = 6)
    (p : Nat) (hp : p < 7) :
    (pOut (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) p).toNat =
        Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ∧
    (pHOut (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) p).toNat =
        Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ∧
    (pZOut (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) p).toNat =
        Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
  let bits := XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hP : (pOut bits p).toNat =
      Shared.directCount G C.P (L.p ⟨p, hp⟩).1 := by
    rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P L.p _
    intro j
    rw [XFourNoRoot.BroadFourBridge.pArc_coreBits G.Adj _ _ _ p j hp j.isLt]
    by_cases hpj : p = j
    · simp only [hpj, ne_eq, not_true_eq_false, false_and, decide_false,
        Bool.false_eq_true, false_iff]
      intro hadj
      apply hG.1 (L.p ⟨p, hp⟩).1
      have hfin : (⟨j.val, j.isLt⟩ : Fin 7) = ⟨p, hp⟩ := Fin.ext hpj.symm
      have hfin' : j = ⟨p, hp⟩ := Fin.ext hpj.symm
      simpa [hfin, hfin'] using hadj
    · simp [hpj]
  have hH : (pHOut bits p).toNat =
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 := by
    rw [pHOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H (hLabelEquiv G C L hHCard) _
    intro j
    rw [XFourNoRoot.BroadFourBridge.pToH_coreBits G.Adj _ _ _ p j hp j.isLt]
    simp
  have hZ : (pZOut bits p).toNat =
      Shared.directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
    rw [pZOut, toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G (externalTargets G C) L.z _
    intro j
    rw [XFourNoRoot.BroadFourBridge.pToZ_coreBits G.Adj _ _ _ p j hp j.isLt]
    simp
  exact ⟨hP, hH, hZ⟩

theorem hPOut_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (_hHCard : C.H.card = 6) (h : Nat) (hh : h < 6) :
    (hPOut (XFourNoRoot.BroadFourBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
      (fun i ↦ (L.z i).1)) h).toNat =
      Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1 := by
  rw [hPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  rw [XFourNoRoot.BroadFourBridge.hToP_coreBits G.Adj _ _ _ h j hh j.isLt]
  simp

end SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge
