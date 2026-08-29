import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.MTwoProjectedBridge
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExact00
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExact10
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExact10HP19
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExact01
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactCOneMOne
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactConsequences

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.LowExactBridge

open CertificateBridge Shared Labels
open MTwoCore Shared.FiniteCore
open MTwoProjectedBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem pReachesLocal_true_path (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q)
    (p target : Nat) (hp : p < 6) (ht : target < 18)
    (hReach : pReachesLocal (graphBits G C q L) p target = true) :
    ∃ middle, G.Adj (L.low.p ⟨p, hp⟩).1 middle ∧
      G.Adj middle (localVertex G C q L target) := by
  simp only [pReachesLocal, Bool.or_eq_true] at hReach
  rcases hReach with (hP | hH) | hE
  · obtain ⟨i, hi, hBoth⟩ := (Bridge.any_eq_true_iff 6 _).mp hP
    rw [Bool.and_eq_true] at hBoth
    refine ⟨(L.low.p ⟨i, hi⟩).1, ?_, ?_⟩
    · rw [pArc_graphBits G C q L hG p i hp hi] at hBoth
      exact of_decide_eq_true hBoth.1
    · rw [pLocalArc_graphBits G C q L hG hRoot target i ht hi] at hBoth
      exact of_decide_eq_true hBoth.2
  · obtain ⟨i, hi, hBoth⟩ := (Bridge.any_eq_true_iff 6 _).mp hH
    rw [Bool.and_eq_true] at hBoth
    refine ⟨(L.low.h ⟨i, hi⟩).1, ?_, ?_⟩
    · rw [pToH_graphBits G C q L p i hp hi] at hBoth
      exact of_decide_eq_true hBoth.1
    · rw [hLocalArc_graphBits G C q L hG heZero i target hi ht] at hBoth
      exact of_decide_eq_true hBoth.2
  · obtain ⟨i, hi, hBoth⟩ := (Bridge.any_eq_true_iff 3 _).mp hE
    rw [Bool.and_eq_true] at hBoth
    refine ⟨(L.low.e ⟨i, hi⟩).1, ?_, ?_⟩
    · rw [pToE_graphBits G C q L p i hp hi] at hBoth
      exact of_decide_eq_true hBoth.1
    · rw [eLocalArc_graphBits G C q L hG i target hi ht] at hBoth
      exact of_decide_eq_true hBoth.2

private theorem pStrictSecondLocal_true_mem (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented) (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q)
    (p target : Nat) (hp : p < 6) (ht : target < 18)
    (hSecond : pStrictSecondLocal (graphBits G C q L) p target = true) :
    localVertex G C q L target ∈
      G.secondOutNeighborFinset (L.low.p ⟨p, hp⟩).1 := by
  simp only [pStrictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hFirst, hLast⟩ := pReachesLocal_true_path G C q L hG
    hRoot heZero p target hp ht hReach
  have hVertexNe : localVertex G C q L target ≠ (L.low.p ⟨p, hp⟩).1 := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 18) = ⟨8 + p, by omega⟩ := by
      apply (retainedLabelEquiv G C q L hqQ hG).injective
      apply Subtype.ext
      rw [retainedLabelEquiv_val, retainedLabelEquiv_val,
        localVertex_p G C q L ⟨p, hp⟩]
      exact heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨middle, hFirst, hLast⟩, ?_, hVertexNe⟩
  rw [pLocalArc_graphBits G C q L hG hRoot target p ht hp] at hNotArc
  simpa using hNotArc

omit [Fintype V] [DecidableEq V] in
private theorem padded_count_le_filter (W : Finset V) (hW : W.card ≤ 7)
    (Q : V → Prop) [DecidablePred Q] (b : Nat → Bool)
    (hGood : ∀ i : Fin 7, b i = true →
      match paddedOutsideLabels W i with
      | some v => Q v
      | none => False) :
    (count 7 b).toNat ≤ (W.filter Q).card := by
  classical
  rw [← paddedOutsideLabels_count W hW Q,
    Bridge.toNat_count_eq_fin_sum 7 _ (by omega),
    Bridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  apply Finset.sum_le_sum
  intro i _
  by_cases hb : b i = true
  · have hg := hGood i hb
    cases hwi : paddedOutsideLabels W i with
    | none => simp [hwi] at hg
    | some v =>
      have hv : Q v := by simpa [hwi] using hg
      simp [hwi, hb, hv]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

private theorem lowPNoDeletion_true
    (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) :
    lowPNoDeletion (graphBits G C q L) = true := by
  rw [lowPNoDeletion, Bridge.all_eq_true_iff]
  intro p hp
  let source := (L.low.p ⟨p, hp⟩).1
  have hOut : (pOut (graphBits G C q L) p).toNat = G.outdegree source := by
    rw [pLocalCount_toNat G C q L hqQ hG hRoot p hp]
    symm
    apply outdegree_eq_directCount_of_captured G _ source
    intro v hv
    have hc := hCaptured source (L.low.p ⟨p, hp⟩).2 hv
    rcases Finset.mem_union.mp hc with hPH | hE
    · rcases Finset.mem_union.mp hPH with hP | hH
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hP))
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hH)))
    · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hE)
  have hLocal : (pLocalSecondCount (graphBits G C q L) p).toNat ≤
      ((retainedVertexSet G C q).filter
        (fun v => v ∈ G.secondOutNeighborFinset source)).card := by
    unfold pLocalSecondCount
    exact Bridge.count_le_filterCard (retainedVertexSet G C q)
      (retainedLabelEquiv G C q L hqQ hG) _ _ (by omega)
      (fun j hj => by
        have hm := pStrictSecondLocal_true_mem G C q L hqQ hG hRoot heZero
          p j hp j.isLt hj
        simpa [source, retainedLabelEquiv_val] using hm)
  have hOutside : (pOutsideSecondSeven (graphBits G C q L) p).toNat ≤
      (W.filter (fun v => v ∈ G.secondOutNeighborFinset source)).card := by
    unfold pOutsideSecondSeven
    apply padded_count_le_filter W hWCard _ _
    intro i hi
    rw [Bridge.any_eq_true_iff] at hi
    obtain ⟨e, he, hBoth⟩ := hi
    rw [Bool.and_eq_true, pToE_graphBits G C q L p e hp he,
      outsideAdjSeven_graphBits G C q L i e i.isLt he, hw] at hBoth
    simp only [decide_eq_true_eq] at hBoth
    cases hwi : paddedOutsideLabels W i with
    | none => simp [hwi] at hBoth
    | some v =>
      have hvW := paddedOutsideLabels_some_mem W hWCard i v hwi
      simp only [hwi] at hBoth
      have hvOutside : v ∉ retainedVertexSet G C q := by
        have : v ∈ outsideSet G C q := hW.symm ▸ hvW
        exact (Finset.mem_sdiff.mp this).2
      have hNotDirect : ¬G.Adj source v := by
        intro hsv
        have hc := hCaptured source (L.low.p ⟨p, hp⟩).2
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv)
        apply hvOutside
        rcases Finset.mem_union.mp hc with hPH | hE
        · rcases Finset.mem_union.mp hPH with hP | hH
          · exact Finset.mem_union_left {C.s}
              (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hP))
          · exact Finset.mem_union_left {C.s}
              (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P
                (Digraph.LocalConfiguration.H_subset_A (G := G) C hH)))
        · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hE)
      have hvNe : v ≠ source := by
        intro hvs
        apply hvOutside
        exact hvs ▸ Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z)
            (Finset.mem_union_right C.A (L.low.p ⟨p, hp⟩).2))
      have hvSecond : v ∈ G.secondOutNeighborFinset source := by
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨(L.low.e ⟨e, he⟩).1, hBoth.1,
          of_decide_eq_true hBoth.2⟩, hNotDirect, hvNe⟩
      simpa [hwi] using hvSecond
  have hDisjoint : Disjoint (retainedVertexSet G C q) W := by
    rw [hW, Finset.disjoint_left]
    intro v hvR hvW'
    exact (Finset.mem_sdiff.mp hvW').2 hvR
  have hUnionCard :
      ((retainedVertexSet G C q).filter
          (fun v => v ∈ G.secondOutNeighborFinset source)).card +
        (W.filter (fun v => v ∈ G.secondOutNeighborFinset source)).card ≤
        G.secondOutdegree source := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hDisjoint)]
    apply Finset.card_le_card
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp hv).2
    · exact (Finset.mem_filter.mp hv).2
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨source, hs⟩)
  have hSum : (pLocalSecondCount (graphBits G C q L) p).toNat +
      (pOutsideSecondSeven (graphBits G C q L) p).toNat <
      (pOut (graphBits G C q L) p).toNat := by
    rw [hOut]
    omega
  have hLocalLe : (pLocalSecondCount (graphBits G C q L) p).toNat < 256 :=
    (pLocalSecondCount (graphBits G C q L) p).toFin.isLt
  have hOutsideLe : (pOutsideSecondSeven (graphBits G C q L) p).toNat < 256 :=
    (pOutsideSecondSeven (graphBits G C q L) p).toFin.isLt
  simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq,
    BitVec.ult_eq_decide, BitVec.toNat_add]
  constructor
  · rw [hOut]
    exact hMin source
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact hSum

private theorem lowTotals_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (alpha beta : Nat)
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 17)
    (hPP : edgeCount G C.P C.P = 15 - beta)
    (hPH : edgeCount G C.P C.H = 17 - alpha)
    (hHP : 19 ≤ edgeCount G C.H C.P)
    (ha : alpha ≤ 1) (hb : beta ≤ 1) :
    lowTotals alpha beta (graphBits G C q L) = true := by
  unfold lowTotals
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPE_toNat G C q L, hPE]
    decide
  · rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPP_toNat G C q L hG, hPP]
    interval_cases beta <;> decide
  · rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPH_toNat G C q L, hPH]
    interval_cases alpha <;> decide
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [totalHP_toNat G C q L]
    exact hHP

private theorem pPOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (p : Nat) (hp : p < 6) :
    (pPOut (graphBits G C q L) p).toNat =
      directCount G C.P (L.low.p ⟨p, hp⟩).1 := by
  unfold pPOut
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega),
    directCount_eq_sum_fin G C.P L.low.p]
  apply Finset.sum_congr rfl
  intro j _
  rw [pArc_graphBits G C q L hG p j hp j.isLt]

private theorem pHOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (p : Nat) (hp : p < 6) :
    (pHOut (graphBits G C q L) p).toNat =
      directCount G C.H (L.low.p ⟨p, hp⟩).1 := by
  unfold pHOut
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega),
    directCount_eq_sum_fin G C.H L.low.h]
  apply Finset.sum_congr rfl
  intro j _
  rw [pToH_graphBits G C q L p j hp j.isLt]

private theorem pEOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (p : Nat) (hp : p < 6) :
    (pEOut (graphBits G C q L) p).toNat =
      directCount G ({q} ∪ C.Z) (L.low.p ⟨p, hp⟩).1 := by
  unfold pEOut
  rw [Bridge.toNat_count_eq_fin_sum 3 _ (by omega),
    directCount_eq_sum_fin G ({q} ∪ C.Z) L.low.e]
  apply Finset.sum_congr rfl
  intro j _
  rw [pToE_graphBits G C q L p j hp j.isLt]

theorem orderedP_true_of_exact_degrees (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (hOrder : ∀ i : Fin 5,
      Labels.pKey G C ({q} ∪ C.Z) (L.low.p ⟨i.val + 1, by omega⟩).1 ≤
        Labels.pKey G C ({q} ∪ C.Z) (L.low.p ⟨i.val, by omega⟩).1)
    (hDegrees : ∀ p ∈ C.P, G.outdegree p = 8) :
    orderedP (graphBits G C q L) = true := by
  rw [orderedP, Bridge.all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  unfold pRowKey
  unfold Labels.pKey at hOrder
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  rw [pEOut_toNat G C q L (p + 1) (by omega),
    pHOut_toNat G C q L (p + 1) (by omega),
    pPOut_toNat G C q L hG (p + 1) (by omega),
    pEOut_toNat G C q L p (by omega), pHOut_toNat G C q L p (by omega),
    pPOut_toNat G C q L hG p (by omega)]
  have hKey := hOrder ⟨p, hp⟩
  rw [hDegrees _ (L.low.p ⟨p + 1, by omega⟩).2,
    hDegrees _ (L.low.p ⟨p, by omega⟩).2] at hKey
  have hpPLe : directCount G C.P (L.low.p ⟨p, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.p).symm)
  have hpHLe : directCount G C.H (L.low.p ⟨p, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.h).symm)
  have hpELe : directCount G ({q} ∪ C.Z) (L.low.p ⟨p, by omega⟩).1 ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      rw [← Fintype.card_coe]
      exact (Fintype.card_congr L.low.e).symm)
  have hpPLe' : directCount G C.P (L.low.p ⟨p + 1, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.p).symm)
  have hpHLe' : directCount G C.H (L.low.p ⟨p + 1, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.h).symm)
  have hpELe' : directCount G ({q} ∪ C.Z) (L.low.p ⟨p + 1, by omega⟩).1 ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      rw [← Fintype.card_coe]
      exact (Fintype.card_congr L.low.e).symm)
  have h256 : (256 : BitVec 16).toNat = 256 := by decide
  have h16 : (16 : BitVec 16).toNat = 16 := by decide
  rw [h256, h16, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change 4096 * 8 +
      256 * directCount G ({q} ∪ C.Z) (L.low.p ⟨p + 1, by omega⟩).1 +
      16 * directCount G C.H (L.low.p ⟨p + 1, by omega⟩).1 +
      directCount G C.P (L.low.p ⟨p + 1, by omega⟩).1 ≤
    4096 * 8 +
      256 * directCount G ({q} ∪ C.Z) (L.low.p ⟨p, by omega⟩).1 +
      16 * directCount G C.H (L.low.p ⟨p, by omega⟩).1 +
      directCount G C.P (L.low.p ⟨p, by omega⟩).1 at hKey
  omega

theorem orderedETail_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q)
    (hOrder : Labels.eIncoming G (fun i => (L.low.p i).1) (L.low.e 2).1 ≤
      Labels.eIncoming G (fun i => (L.low.p i).1) (L.low.e 1).1) :
    orderedETail (graphBits G C q L) = true := by
  unfold orderedETail
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  have hIncoming (e : Nat) (he : e < 3) :
      (count 6 fun p => pToE (graphBits G C q L) p e).toNat =
        Labels.eIncoming G (fun i => (L.low.p i).1) (L.low.e ⟨e, he⟩).1 := by
    rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
    unfold Labels.eIncoming
    apply Finset.sum_congr rfl
    intro p _
    rw [pToE_graphBits G C q L p e p.isLt he]
    by_cases ha : G.Adj (L.low.p p).1 (L.low.e ⟨e, he⟩).1 <;> simp
  rw [hIncoming 2 (by omega), hIncoming 1 (by omega)]
  exact hOrder

private theorem hPOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (h : Nat) (hh : h < 6) :
    (hPOut (graphBits G C q L) h).toNat =
      directCount G C.P (L.low.h ⟨h, hh⟩).1 := by
  unfold hPOut
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega),
    directCount_eq_sum_fin G C.P L.low.p]
  apply Finset.sum_congr rfl
  intro p _
  rw [hToP_graphBits G C q L h p hh p.isLt]

theorem orderedXOnly_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q)
    (hOrder : ∀ i : Fin 3,
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.low.h ⟨i.val + 3, by omega⟩).1 ≤
        RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.low.h ⟨i.val + 2, by omega⟩).1) :
    orderedXOnly (graphBits G C q L) = true := by
  rw [orderedXOnly, Bridge.all_eq_true_iff]
  intro i hi
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  rw [hPOut_toNat G C q L (3 + i) (by omega),
    hPOut_toNat G C q L (2 + i) (by omega)]
  have hIncoming (h : Nat) (hh : h < 6) :
      (count 6 fun p => pToH (graphBits G C q L) p h).toNat =
        ∑ p : Fin 6, if G.Adj (L.low.p p).1 (L.low.h ⟨h, hh⟩).1 then 1 else 0 := by
    rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
    apply Finset.sum_congr rfl
    intro p _
    rw [pToH_graphBits G C q L p h p.isLt hh]
    by_cases ha : G.Adj (L.low.p p).1 (L.low.h ⟨h, hh⟩).1 <;> simp [ha]
  rw [hIncoming (3 + i) (by omega), hIncoming (2 + i) (by omega)]
  have hKey := hOrder ⟨i, hi⟩
  unfold RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey at hKey
  rw [sum_finset_eq_sum_fin C.P L.low.p,
    sum_finset_eq_sum_fin C.P L.low.p] at hKey
  have hOut0 : directCount G C.P (L.low.h ⟨2 + i, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.p).symm)
  have hOut1 : directCount G C.P (L.low.h ⟨3 + i, by omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.p).symm)
  have hIn0 : (∑ p : Fin 6,
      if G.Adj (L.low.p p).1 (L.low.h ⟨2 + i, by omega⟩).1 then 1 else 0) ≤ 6 := by
    calc
      _ ≤ ∑ _p : Fin 6, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        split <;> omega
      _ = 6 := by simp
  have hIn1 : (∑ p : Fin 6,
      if G.Adj (L.low.p p).1 (L.low.h ⟨3 + i, by omega⟩).1 then 1 else 0) ≤ 6 := by
    calc
      _ ≤ ∑ _p : Fin 6, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        split <;> omega
      _ = 6 := by simp
  have h16 : (16 : BitVec 8).toNat = 16 := by decide
  rw [h16]
  have hMul0 : 16 * directCount G C.P (L.low.h ⟨3 + i, by omega⟩).1 < 256 := by omega
  have hMul1 : 16 * directCount G C.P (L.low.h ⟨2 + i, by omega⟩).1 < 256 := by omega
  rw [Nat.mod_eq_of_lt hMul0, Nat.mod_eq_of_lt hMul1,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simpa [Nat.add_comm] using hKey

theorem lowEffectivePConditions_true
    (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (_hNoRoot : epsilonS G C = 0)
    (hRoot : edgeCount G C.P {C.s} = 0) (heZero : (L.low.e 0).1 = q)
    (hE : ({q} ∪ C.Z) = auxiliarySet G C)
    (hPE : 17 ≤ edgeCount G C.P ({q} ∪ C.Z))
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z)) :
    lowEffectivePConditions (graphBits G C q L) = true := by
  rw [lowEffectivePConditions, Bridge.all_eq_true_iff]
  intro p hp
  let source := (L.low.p ⟨p, hp⟩).1
  let E := {q} ∪ C.Z
  let S := directAuxNeighbors G E source
  let U := directAuxEffectiveUnion G C E source
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.low.p).symm
  have hECard : E.card = 3 := by
    rw [← Fintype.card_coe]
    simpa [E] using (Fintype.card_congr L.low.e).symm
  have hEP : Disjoint E C.P := by
    rw [Finset.disjoint_left]
    intro v hvE hvP
    change v ∈ ({q} ∪ C.Z) at hvE
    rcases Finset.mem_union.mp hvE with hvQ | hvZ
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
          (Finset.mem_singleton.mp hvQ ▸ hqQ)
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
  have hEffective := effective_seven_or_eight G C hG hMin E hEP hPCard
    hECard (by simpa [E] using hPE) source (L.low.p ⟨p, hp⟩).2
  have hSecond : (pSecondPCount (graphBits G C q L) p).toNat ≤
      (C.P.filter fun v => v ∈ G.secondOutNeighborFinset source).card := by
    unfold pSecondPCount
    exact Bridge.count_le_filterCard C.P L.low.p _ _ (by omega)
      (fun i hi => by
        have hm := pStrictSecondLocal_true_mem G C q L hqQ hG hRoot heZero
          p (8 + i) hp (by omega) hi
        simpa [source, localVertex_p] using hm)
  have hUnion := PSecond_add_directAuxEffective_card_le_second_add_H G C hG
    E (by simpa [E] using hE) source (L.low.p ⟨p, hp⟩).2
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨source, hs⟩)
  have hPH : Disjoint C.P C.H :=
    Digraph.LocalConfiguration.disjoint_H_P (G := G) C |>.symm
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [Finset.disjoint_left]
    intro v hvPH hvE
    rcases Finset.mem_union.mp hvPH with hvP | hvH
    · exact (Finset.disjoint_left.mp hEP) hvE hvP
    · have hvAux : v ∈ auxiliarySet G C := by
        rw [← hE]
        simpa [E] using hvE
      rcases Finset.mem_union.mp hvAux with hvQ | hvZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C
            (Finset.mem_inter.mp hvQ).1)
      · exact (Finset.disjoint_left.mp
          (BSixKThree.disjoint_H_externalTargets G C hG)) hvH hvZ
  have hDegree : G.outdegree source = directCount G C.P source +
      directCount G C.H source + directCount G E source := by
    have h := outdegree_eq_directCount_of_captured G (C.P ∪ C.H ∪ E)
      source (by simpa [E] using hCaptured source (L.low.p ⟨p, hp⟩).2)
    rw [directCount_union_of_disjoint G (C.P ∪ C.H) E source hPHE,
      directCount_union_of_disjoint G C.P C.H source hPH] at h
    exact h
  have hBlocks :
      (pPOut (graphBits G C q L) p).toNat = directCount G C.P source ∧
      (pHOut (graphBits G C q L) p).toNat = directCount G C.H source ∧
      (pEOut (graphBits G C q L) p).toNat = directCount G E source := by
    exact ⟨by simpa [source] using pPOut_toNat G C q L hG p hp,
      by simpa [source] using pHOut_toNat G C q L p hp,
      by simpa [source, E] using pEOut_toNat G C q L p hp⟩
  have hSCard : S.card = directCount G E source := rfl
  have hPLe : (pPOut (graphBits G C q L) p).toNat ≤ 6 := by
    rw [hBlocks.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe : (pHOut (graphBits G C q L) p).toNat ≤ 6 := by
    rw [hBlocks.2.1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.low.h).symm)
  have hELe : (pEOut (graphBits G C q L) p).toNat ≤ 3 := by
    rw [hBlocks.2.2]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hSecondLe : (pSecondPCount (graphBits G C q L) p).toNat ≤ 6 :=
    hSecond.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hIneq : (pSecondPCount (graphBits G C q L) p).toNat +
      (if pEOut (graphBits G C q L) p == 2 then 9 else 8) ≤
      (pPOut (graphBits G C q L) p).toNat +
        2 * (pHOut (graphBits G C q L) p).toNat +
          (pEOut (graphBits G C q L) p).toNat := by
    have hBase : (pSecondPCount (graphBits G C q L) p).toNat + U.card + 1 ≤
        G.outdegree source + directCount G C.H source := by
      dsimp [U]
      omega
    by_cases hTwo : pEOut (graphBits G C q L) p = (2 : BitVec 8)
    · have hsTwo : S.card = 2 := by
        rw [hSCard, ← hBlocks.2.2]
        exact congrArg BitVec.toNat hTwo
      have hEight := hEffective.2 hsTwo
      change 8 ≤ U.card at hEight
      simp only [beq_iff_eq, if_pos hTwo]
      rw [hBlocks.1, hBlocks.2.1]
      have hEExact : directCount G E source = 2 := by
        rw [← hBlocks.2.2]
        exact congrArg BitVec.toNat hTwo
      omega
    · have hSeven := hEffective.1
      change 7 ≤ U.card at hSeven
      simp only [beq_iff_eq, if_neg hTwo]
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      omega
  simp only [beq_iff_eq] at hIneq
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_mul]
  have hTwoNat : (2 : BitVec 8).toNat = 2 := by decide
  have hEightNat : (8 : BitVec 8).toNat = 8 := by decide
  have hNineNat : (9 : BitVec 8).toNat = 9 := by decide
  split
  · rw [hTwoNat, hNineNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rename_i hCond
    have hEq : pEOut (graphBits G C q L) p = (2 : BitVec 8) := by
      simpa [beq_iff_eq] using hCond
    rw [if_pos hEq] at hIneq
    exact hIneq
  · rw [hTwoNat, hEightNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rename_i hCond
    have hNe : pEOut (graphBits G C q L) p ≠ (2 : BitVec 8) := by
      simpa [beq_iff_eq] using hCond
    rw [if_neg hNe] at hIneq
    exact hIneq

private theorem allPDegreesEight_true
    (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented) (hRoot : edgeCount G C.P {C.s} = 0)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hDegrees : ∀ p ∈ C.P, G.outdegree p = 8) :
    (all 6 fun p => pOut (graphBits G C q L) p == 8) = true := by
  rw [Bridge.all_eq_true_iff]
  intro p hp
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [pLocalCount_toNat G C q L hqQ hG hRoot p hp]
  have hCaptured' : G.outNeighborFinset (L.low.p ⟨p, hp⟩).1 ⊆
      retainedVertexSet G C q := by
    intro v hv
    have hc := hCaptured _ (L.low.p ⟨p, hp⟩).2 hv
    rcases Finset.mem_union.mp hc with hPH | hE
    · rcases Finset.mem_union.mp hPH with hP | hH
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hP))
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hH)))
    · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hE)
  rw [← outdegree_eq_directCount_of_captured G _ _ hCaptured',
    hDegrees _ (L.low.p ⟨p, hp⟩).2]
  decide

theorem pDegrees_eight_of_totals
    (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hSum : edgeCount G C.P ({q} ∪ C.Z) +
      edgeCount G C.P C.P + edgeCount G C.P C.H = 48) :
    ∀ p ∈ C.P, G.outdegree p = 8 := by
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 48 := by
    calc
      _ = ∑ p ∈ C.P, (directCount G C.P p + directCount G C.H p +
          directCount G ({q} ∪ C.Z) p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact P_outdegree_eq_blocks G C q L hqQ hCaptured p hp
      _ = edgeCount G C.P C.P + edgeCount G C.P C.H +
          edgeCount G C.P ({q} ∪ C.Z) := by
        unfold edgeCount
        simp only [Finset.sum_add_distrib]
      _ = 48 := by omega
  apply pointwise_eq_of_sum_eq_card_mul C.P G.outdegree 8
    (fun p hp => hMin p)
  have hpCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.low.p).symm
  simpa [hpCard] using hDegreeSum

private theorem saturatedPP_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (hPP : edgeCount G C.P C.P = 15) :
    saturatedPP (graphBits G C q L) = true := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.low.p).symm
  have hMax : edgeCount G C.P C.P = C.P.card.choose 2 := by
    rw [hPP, hPCard]
    decide
  rw [saturatedPP, Bridge.all_eq_true_iff]
  intro p hp
  rw [Bridge.all_eq_true_iff]
  intro p' hp'
  by_cases heq : p = p'
  · simp [heq]
  · rw [decide_eq_false heq]
    simp only [Bool.false_or, Bool.or_eq_true]
    rcases RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
        G C.P hG hMax (L.low.p ⟨p, hp⟩).2 (L.low.p ⟨p', hp'⟩).2
        (by intro hv
            exact heq (Fin.ext_iff.mp (L.low.p.injective (Subtype.ext hv)))) with h | h
    · left
      rw [pArc_graphBits G C q L hG p p' hp hp']
      exact decide_eq_true h
    · right
      rw [pArc_graphBits G C q L hG p' p hp' hp]
      exact decide_eq_true h

private theorem completePH_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (hMax : edgeCount G C.P C.H + edgeCount G C.H C.P = 36) :
    completePH (graphBits G C q L) = true := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.low.p).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr L.low.h).symm
  have hCrossMax : edgeCount G C.P C.H + edgeCount G C.H C.P =
      C.P.card * C.H.card := by simpa [hPCard, hHCard] using hMax
  rw [completePH, Bridge.all_eq_true_iff]
  intro p hp
  rw [Bridge.all_eq_true_iff]
  intro h hh
  rw [Bool.or_eq_true]
  rcases complete_of_cross_edgeCount_max G C.P C.H hG hCrossMax
      (L.low.p ⟨p, hp⟩).2 (L.low.h ⟨h, hh⟩).2 with hph | hhp
  · left
    rw [pToH_graphBits G C q L p h hp hh]
    exact decide_eq_true hph
  · right
    rw [hToP_graphBits G C q L h p hh hp]
    exact decide_eq_true hhp

private theorem tightHStructure_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hG : G.IsOriented)
    (hXCard : C.X.card = 4) (hRCard : C.R.card = 1)
    (hRSingleton : C.R = {(L.a 7).1})
    (hQ : C.Q = {q}) (hAOneQ : edgeCount G C.A1 {q} = 1)
    (hHA : edgeCount G C.H C.A = 23)
    (hHQ : edgeCount G C.H C.Q = 5) :
    tightHStructure (graphBits G C q L) = true := by
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr L.low.h).symm
  have hHHLe := internal_edgeCount_le_choose_two G C.H hG
  rw [hHCard] at hHHLe
  norm_num [Nat.choose] at hHHLe
  have hHa1Le := Shared.H_to_a1_le_x G C hG
  have hx : C.x = 4 := by
    change C.X.card = 4
    exact hXCard
  rw [hx] at hHa1Le
  have hHRLe := Shared.H_to_R_le_x_mul_card_R G C
  rw [hx, hRCard] at hHRLe
  have hHa1Disjoint : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hv
    have hvEq := Finset.mem_singleton.mp hv
    subst v
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  have hPartsR := Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hHASplit : edgeCount G C.H C.A = edgeCount G C.H C.H +
      edgeCount G C.H {C.a1} + edgeCount G C.H C.R := by
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C,
      edgeCount_union_of_disjoint G C.H (C.A1 ∪ C.X ∪ {C.a1}) C.R hPartsR,
      edgeCount_union_of_disjoint G C.H (C.A1 ∪ C.X) {C.a1} hHa1Disjoint]
    rfl
  have hHH : edgeCount G C.H C.H = 15 := by omega
  have hHa1 : edgeCount G C.H {C.a1} = 4 := by omega
  have hHR : edgeCount G C.H C.R = 4 := by omega
  have hTournament : ∀ u ∈ C.H, ∀ v ∈ C.H, u ≠ v →
      G.Adj u v ∨ G.Adj v u := by
    intro u hu v hv hne
    exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
      G C.H hG (by simpa [hHCard, Nat.choose] using hHH) hu hv hne
  have hDomPivot : ∀ u ∈ C.X, G.Adj u C.a1 := by
    let incoming := C.H.filter (fun u => G.Adj u C.a1)
    have hSubset : incoming ⊆ C.X := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huH, hua1⟩
      rcases Finset.mem_union.mp huH with huA1 | huX
      · exact (hG.2 (Finset.mem_filter.mp huA1).2 hua1).elim
      · exact huX
    have hIncomingCard : incoming.card = 4 := by
      rw [edgeCount_eq_sum_incoming G C.H {C.a1}] at hHa1
      simpa [incoming, internalInDegree] using hHa1
    have hEq : incoming = C.X :=
      Finset.eq_of_subset_of_card_le hSubset (by omega)
    intro u hu
    have huIncoming : u ∈ incoming := by rw [hEq]; exact hu
    exact (Finset.mem_filter.mp huIncoming).2
  have hDomR : ∀ u ∈ C.X, G.Adj u (L.a 7).1 := by
    intro u hu
    have hHRSingle : edgeCount G C.H {(L.a 7).1} = 4 := by
      have h := hHR
      rw [hRSingleton] at h
      exact h
    let incoming := C.H.filter (fun v => G.Adj v (L.a 7).1)
    have hSubset : incoming ⊆ C.X := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvH, hvr⟩
      rcases Finset.mem_union.mp hvH with hvA1 | hvX
      · exact (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
          G C v (L.a 7).1 hvA1 L.a_r hvr).elim
      · exact hvX
    have hIncomingCard : incoming.card = 4 := by
      rw [edgeCount_eq_sum_incoming G C.H {(L.a 7).1}] at hHRSingle
      simpa [incoming, internalInDegree] using hHRSingle
    have hEq : incoming = C.X :=
      Finset.eq_of_subset_of_card_le hSubset (by omega)
    have huIncoming : u ∈ incoming := by rw [hEq]; exact hu
    exact (Finset.mem_filter.mp huIncoming).2
  have hHXSplit := BSixKThree.edgeCount_source_union G C.A1 C.X C.Q
    (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hXQ : edgeCount G C.X {q} = 4 := by
    have hSplit : edgeCount G C.H {q} =
        edgeCount G C.A1 {q} + edgeCount G C.X {q} := by
      simpa [Digraph.LocalConfiguration.H, hQ] using hHXSplit
    have hHQ' : edgeCount G C.H {q} = 5 := by simpa [hQ] using hHQ
    omega
  have hDomQ : ∀ u ∈ C.X, G.Adj u q := by
    let incoming := C.X.filter (fun u => G.Adj u q)
    have hIncomingCard : incoming.card = 4 := by
      rw [edgeCount_eq_sum_incoming G C.X {q}] at hXQ
      simpa [incoming, internalInDegree] using hXQ
    have hEq : incoming = C.X :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    intro u hu
    have huIncoming : u ∈ incoming := by rw [hEq]; exact hu
    exact (Finset.mem_filter.mp huIncoming).2
  rw [tightHStructure, Bool.and_eq_true]
  constructor
  · rw [Bridge.all_eq_true_iff]
    intro x hx
    simp only [Bool.and_eq_true]
    have hxMem : (L.low.h ⟨2 + x, by omega⟩).1 ∈ C.X := by
      simpa [Nat.add_comm] using L.low.h_x ⟨x, by omega⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hToQ_graphBits G C q L (2 + x) (by omega)]
      exact decide_eq_true (hDomQ _ hxMem)
    · rw [hToAOne_graphBits G C q L (2 + x) (by omega)]
      exact decide_eq_true (hDomPivot _ hxMem)
    · rw [hToR_graphBits G C q L (2 + x) (by omega)]
      exact decide_eq_true (hDomR _ hxMem)
  · rw [Bridge.all_eq_true_iff]
    intro i hi
    rw [Bridge.all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · rw [decide_eq_false hij]
      simp only [Bool.false_or, Bool.or_eq_true]
      rcases hTournament _ (L.low.h ⟨i, hi⟩).2 _ (L.low.h ⟨j, hj⟩).2
          (by intro hv; exact hij (Fin.ext_iff.mp (L.low.h.injective (Subtype.ext hv)))) with h | h
      · left
        rw [hArc_graphBits G C q L hG i j hi hj]
        exact decide_eq_true h
      · right
        rw [hArc_graphBits G C q L hG j i hj hi]
        exact decide_eq_true h

private theorem totalHP_eq_true (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (n : Nat) (hn : n < 256)
    (hHP : edgeCount G C.H C.P = n) :
    (count 36 (fun k => hToP (graphBits G C q L) (k / 6) (k % 6)) == n) = true := by
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [totalHP_toNat G C q L, hHP]
  change n = (BitVec.ofNat 8 n).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem commonFacts
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPivot : IsMinimalPivot G C) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0) (heZero : (L.low.e 0).1 = q)
    (hB : C.B = C.P ∪ {q}) (hRSingleton : C.R = {(L.a 7).1})
    (hk : C.k = 2) (hr : C.r = 6)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) :
    oriented (graphBits G C q L) = true ∧
    everyXReached (graphBits G C q L) = true ∧
    hConditions (graphBits G C q L) = true ∧
    rConditions (graphBits G C q L) = true ∧
    xConditionsSeven (graphBits G C q L) = true ∧
    eConditionsSeven (graphBits G C q L) = true ∧
    lowPNoDeletion (graphBits G C q L) = true := by
  exact ⟨oriented_true G C q L hG heZero,
    everyXReached_true G C q L hG hk,
    hConditions_true G C q L hG hMin hPivot hqQ hB hRSingleton hk hr,
    rConditions_true G C q L hG hMin hPivot hqQ hB hRSingleton hk hr,
    xConditionsSeven_true G C q L hqQ hG hRoot heZero hB hNoSeymour
      W hW hWCard hw,
    eConditionsSeven_true G C q L hqQ hG hMin W hW hWCard hw,
    lowPNoDeletion_true G C q L hqQ hG hMin hNoSeymour hRoot heZero
      hCaptured W hW hWCard hw⟩

theorem cTwoMOne_false
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPivot : IsMinimalPivot G C) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0) (heZero : (L.low.e 0).1 = q)
    (hB : C.B = C.P ∪ {q}) (hRSingleton : C.R = {(L.a 7).1})
    (hk : C.k = 2) (hr : C.r = 6)
    (hq0 : G.Adj (L.low.h 0).1 q) (hq1 : G.Adj (L.low.h 1).1 q)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (alpha beta : Nat) (hab : alpha + beta ≤ 1)
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 17)
    (hPP : edgeCount G C.P C.P = 15 - beta)
    (hPH : edgeCount G C.P C.H = 17 - alpha)
    (hHP : 19 ≤ edgeCount G C.H C.P)
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) : False := by
  let bits := graphBits G C q L
  rcases commonFacts G hBound C q L hqQ hG hMin hPivot hNoSeymour hRoot
    heZero hB hRSingleton hk hr hCaptured W hW hWCard hw with
    ⟨hOr, hReached, hHC, hRC, hXC, hEC, hLowP⟩
  have hq0b : hToQ bits 0 = true := by
    rw [hToQ_graphBits G C q L 0 (by omega)]
    exact decide_eq_true hq0
  have hq1b : hToQ bits 1 = true := by
    rw [hToQ_graphBits G C q L 1 (by omega)]
    exact decide_eq_true hq1
  have hTotals := lowTotals_true G C q L hG alpha beta hPE hPP hPH hHP
    (by omega) (by omega)
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.low.p).symm
  have hHCard : C.H.card = 6 := by simpa using (Fintype.card_congr L.low.h).symm
  rw [hPCard, hHCard] at hCross
  have hCases : (alpha = 0 ∧ beta = 0) ∨
      (alpha = 1 ∧ beta = 0) ∨ (alpha = 0 ∧ beta = 1) := by omega
  rcases hCases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hSat := saturatedPairRectangles_true G C q L hG hPP hPH hHP
    have hCore : lowExactCore00 bits = true := by
      simp only [lowExactCore00, Bool.and_eq_true]
      aesop
    rw [lowExact00_unsat bits] at hCore
    contradiction
  · have hDegrees := pDegrees_eight_of_totals G C q L hqQ hMin hCaptured
      (by omega)
    have hAllDegrees := allPDegreesEight_true G C q L hqQ hG hRoot
      hCaptured hDegrees
    have hDeletion := auxiliaryDeletionPConditionsSeven_true G hBound C q L
      hqQ hG hNoSeymour hRoot heZero hB hCaptured hDegrees W hW hWCard hw
    have hSatPP := saturatedPP_true G C q L hG hPP
    have hHPle : edgeCount G C.H C.P ≤ 20 := by omega
    by_cases hHP19 : edgeCount G C.H C.P = 19
    · have hHPBool := totalHP_eq_true G C q L 19 (by omega) hHP19
      have hCore : lowExactCore10All 19 bits = true := by
        simp only [lowExactCore10All, lowExactCore10HP, lowExactCore10,
          lowExactCore, Bool.and_eq_true, if_neg (by omega : (19 : Nat) ≠ 20)]
        aesop
      rw [lowExact10HP19_unsat bits] at hCore
      contradiction
    · have hHP20 : edgeCount G C.H C.P = 20 := by omega
      have hHPBool := totalHP_eq_true G C q L 20 (by omega) hHP20
      have hComplete := completePH_true G C q L hG (by omega)
      have hCore : lowExactCore10All 20 bits = true := by
        simp only [lowExactCore10All, lowExactCore10HP, lowExactCore10,
          lowExactCore, Bool.and_eq_true]
        aesop
      rw [lowExact10_unsat bits] at hCore
      contradiction
  · have hHPExact : edgeCount G C.H C.P = 19 := by omega
    have hDegrees := pDegrees_eight_of_totals G C q L hqQ hMin hCaptured
      (by omega)
    have hAllDegrees := allPDegreesEight_true G C q L hqQ hG hRoot
      hCaptured hDegrees
    have hDeletion := auxiliaryDeletionPConditionsSeven_true G hBound C q L
      hqQ hG hNoSeymour hRoot heZero hB hCaptured hDegrees W hW hWCard hw
    have hComplete := completePH_true G C q L hG (by omega)
    have hHPBool := totalHP_eq_true G C q L 19 (by omega) hHPExact
    have hSatPH : saturatedPH bits = true := by
      unfold saturatedPH
      rw [Bool.and_eq_true]
      exact ⟨hComplete, hHPBool⟩
    have hCore : lowExactCore01All bits = true := by
      simp only [lowExactCore01All, lowExactCore01, lowExactCore,
        Bool.and_eq_true]
      aesop
    rw [lowExact01_unsat bits] at hCore
    contradiction

set_option maxHeartbeats 2000000 in
-- The canonical exact-one bridge unfolds the finite encoding definitions.
theorem cOneMOne_false
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration) (q : V)
    (L : MTwoProjectedBridge.Labels G C q) (hqQ : q ∈ C.Q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPivot : IsMinimalPivot G C) (hNoSeymour : ¬G.HasSeymourVertex)
    (hNoRoot : epsilonS G C = 0)
    (hRoot : edgeCount G C.P {C.s} = 0) (heZero : (L.low.e 0).1 = q)
    (hB : C.B = C.P ∪ {q}) (hRSingleton : C.R = {(L.a 7).1})
    (hk : C.k = 2) (hr : C.r = 6)
    (hXCard : C.X.card = 4) (hQ : C.Q = {q})
    (hAOneQ : edgeCount G C.A1 {q} = 1)
    (hAux : ({q} ∪ C.Z) = auxiliarySet G C)
    (hq0 : G.Adj (L.low.h 0).1 q) (hq1 : ¬G.Adj (L.low.h 1).1 q)
    (hOrderedP : orderedP (graphBits G C q L) = true)
    (hOrderedX : orderedXOnly (graphBits G C q L) = true)
    (hOrderedE : orderedETail (graphBits G C q L) = true)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 17)
    (hPP : edgeCount G C.P C.P = 15)
    (hPH : edgeCount G C.P C.H = 16)
    (hHP : 20 ≤ edgeCount G C.H C.P)
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) : False := by
  let bits := graphBits G C q L
  rcases commonFacts G hBound C q L hqQ hG hMin hPivot hNoSeymour hRoot
    heZero hB hRSingleton hk hr hCaptured W hW hWCard hw with
    ⟨hOr, hReached, hHC, hRC, hXC, hEC, hLowP⟩
  have hq0b : hToQ bits 0 = true := by
    rw [hToQ_graphBits G C q L 0 (by omega)]
    exact decide_eq_true hq0
  have hq1b : (!hToQ bits 1) = true := by
    rw [hToQ_graphBits G C q L 1 (by omega)]
    simpa using hq1
  have hPEb : (count 18 (fun n => pToE bits (n / 3) (n % 3)) == 17) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPE_toNat G C q L, hPE]
    decide
  have hPPb : (count 30 (fun n =>
      let p := n / 5
      let j := n % 5
      pArc bits p (if j < p then j else j + 1)) == 15) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPP_toNat G C q L hG, hPP]
    decide
  have hPHb : (count 36 (fun n => pToH bits (n / 6) (n % 6)) == 16) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPH_toNat G C q L, hPH]
    decide
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.low.p).symm
  have hHCard : C.H.card = 6 := by simpa using (Fintype.card_congr L.low.h).symm
  rw [hPCard, hHCard] at hCross
  have hHPExact : edgeCount G C.H C.P = 20 := by omega
  have hHPb : (20 : BitVec 8).ule
      (count 36 fun n => hToP bits (n / 6) (n % 6)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [totalHP_toNat G C q L, hHPExact]
    decide
  have hDegrees := pDegrees_eight_of_totals G C q L hqQ hMin hCaptured
    (by omega)
  have hAllDegrees := allPDegreesEight_true G C q L hqQ hG hRoot
    hCaptured hDegrees
  have hDeletion := auxiliaryDeletionPConditionsSeven_true G hBound C q L
    hqQ hG hNoSeymour hRoot heZero hB hCaptured hDegrees W hW hWCard hw
  have hSatPP := saturatedPP_true G C q L hG hPP
  have hComplete := completePH_true G C q L hG (by omega)
  have hEffective := lowEffectivePConditions_true G C q L hqQ hG hMin
    hNoSeymour hNoRoot hRoot heZero hAux (by omega) hCaptured
  have hRCard : C.R.card = 1 := by simp [hRSingleton]
  have hHQUpper : edgeCount G C.H C.Q ≤ 5 := by
    have hSplit := BSixKThree.edgeCount_source_union G C.A1 C.X C.Q
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
    have hXQ := edgeCount_le_card_mul_card G C.X {q}
    rw [hXCard] at hXQ
    have hSplit' : edgeCount G C.H {q} =
        edgeCount G C.A1 {q} + edgeCount G C.X {q} := by
      simpa [Digraph.LocalConfiguration.H, hQ] using hSplit
    rw [hAOneQ] at hSplit'
    norm_num at hXQ
    rw [hQ]
    omega
  have hHDegreeLower : 48 ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      48 = ∑ _u ∈ C.H, 8 := by simp [hHCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hHDegreeSplit := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
  have hHAUpper := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  have hx : C.x = 4 := by
    change C.X.card = 4
    exact hXCard
  rw [hHCard, hx, hRCard] at hHAUpper
  norm_num [Nat.choose] at hHAUpper
  have hHA : edgeCount G C.H C.A = 23 := by omega
  have hHQ : edgeCount G C.H C.Q = 5 := by omega
  have hTight := tightHStructure_true G C q L hG hXCard hRCard
    hRSingleton hQ hAOneQ hHA hHQ
  have hCanonical := canonicalPEOneMissing_of_ordered bits hOrderedP hOrderedE
    hPEb hAllDegrees
  have hCore : lowExactCOneMOne bits = true := by
    simp only [lowExactCOneMOne, Bool.and_eq_true]
    aesop
  rw [lowExactCOneMOne_unsat bits] at hCore
  contradiction

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.LowExactBridge
