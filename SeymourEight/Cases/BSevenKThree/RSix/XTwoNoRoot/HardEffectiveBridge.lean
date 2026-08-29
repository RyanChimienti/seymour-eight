import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.HardAuxBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardEffectiveBridge

open Shared Shared.FiniteCore CertificateBridge Labels Encoding EasyBridge HardAuxBridge
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
open SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev auxiliarySet (C : G.LocalConfiguration) : Finset V :=
  C.Q ∪ externalTargets G C

abbrev directAuxNeighbors (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxNeighbors G E p

abbrev directAuxEffectiveUnion (C : G.LocalConfiguration)
    (E : Finset V) (p : V) : Finset V :=
  SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffectiveUnion G C E p

theorem auxiliarySet_card (C : G.LocalConfiguration) (L : Labels G 5 C) :
    (auxiliarySet G C).card = 6 := by
  have hDis : Disjoint C.Q (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [Finset.card_union_of_disjoint hDis]
  have hQ : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hZ : (externalTargets G C).card = 5 := by
    simpa using (Fintype.card_congr L.z).symm
  omega

theorem auxiliarySet_disjoint_P (C : G.LocalConfiguration) :
    Disjoint (auxiliarySet G C) C.P := by
  rw [Finset.disjoint_left]
  intro v hvE hvP
  rcases Finset.mem_union.mp hvE with hvQ | hvExt
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hvQ
  · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExt

noncomputable def hEquiv (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hHCard : C.H.card = 5) :
    Fin 5 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 5 → {v : V // v ∈ C.H} := fun i ↦
    ⟨(L.a ⟨i.val + 1, by omega⟩).1, by
      by_cases hi : i.val < 3
      · exact Finset.mem_union_left C.X (by
          have heq : (⟨i.val + 1, by omega⟩ : Fin 8) =
              ⟨i.val + 1, by omega⟩ := rfl
          rw [heq]
          exact L.a_aOne ⟨i, hi⟩)
      · apply Finset.mem_union_right C.A1
        have heq : (⟨i.val + 1, by omega⟩ : Fin 8) =
            ⟨(i.val - 3) + 4, by omega⟩ := Fin.ext (by simp; omega)
        rw [heq]
        exact L.a_x ⟨i.val - 3, by omega⟩⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply Fin.ext
    have ha : (⟨i.val + 1, by omega⟩ : Fin 8) =
        ⟨j.val + 1, by omega⟩ := by
      apply L.a.injective
      exact Subtype.ext (by simpa [f] using congrArg Subtype.val hij)
    have hv : i.val + 1 = j.val + 1 := by
      simpa using congrArg Fin.val ha
    omega
  · simpa using hHCard.symm

@[simp] theorem hEquiv_val (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hHCard : C.H.card = 5) (i : Fin 5) :
    (hEquiv G C L hHCard i).1 = (L.a ⟨i.val + 1, by omega⟩).1 := rfl

theorem pHOut_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hHCard : C.H.card = 5) (p : Nat) (hp : p < 6) :
    (HardCore.pHOut (graphArc G L) p).toNat =
      directCount G C.H (L.p ⟨p, hp⟩).1 := by
  rw [HardCore.pHOut, toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H (hEquiv G C L hHCard) _
  intro i
  rw [hEquiv_val]
  change graphArc G L (8 + p) (1 + i) = true ↔ _
  rw [graphArc_PA G L p (1 + i) hp (by omega)]
  simp [Nat.add_comm]

theorem pAuxOut_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (p : Nat) (hp : p < 6) :
    (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p).toNat =
      directCount G (auxiliarySet G C) (L.p ⟨p, hp⟩).1 := by
  have hQ : C.Q = {(L.q 0).1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(L.q 0).2, ?_⟩
    intro v hv
    obtain ⟨i, hi⟩ := L.q.surjective ⟨v, hv⟩
    simpa [Subsingleton.elim i 0] using congrArg Subtype.val hi.symm
  have hDis : Disjoint C.Q (externalTargets G C) := by
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  have hZ : (pZOut 5 (graphPToZ G L) p).toNat =
      directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 := by
    rw [pZOut, toNat_count_eq_fin_sum 5 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G (externalTargets G C) L.z _
    intro z
    rw [graphPToZ_eq G L p z hp z.isLt]
    simp only [decide_eq_true_eq]
  have hQCount : (bitCount (pToQ (graphArc G L) p)).toNat =
      directCount G C.Q (L.p ⟨p, hp⟩).1 := by
    rw [hQ, directCount_singleton, epsilonAt, bitCount, pToQ,
      graphArc_PQ G L p hp]
    by_cases h : G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1 <;> simp [h]
  simp only [pAuxOut, show (1 = 0) = False by decide, if_false]
  rw [BitVec.toNat_add, hQCount, hZ,
    Nat.mod_eq_of_lt (by
      have hqLe : directCount G C.Q (L.p ⟨p, hp⟩).1 ≤ 1 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by rw [hQ]; simp)
      have hzLe : directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ 5 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr L.z).symm)
      omega), Nat.add_comm,
    ← directCount_union_of_disjoint G C.Q (externalTargets G C) _ hDis]

theorem toNat_sumCount (n : Nat) (f : Nat → BitVec 8) :
    (sumCount n f).toNat =
      (∑ i ∈ Finset.range n, (f i).toNat) % 256 := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      rw [sumCount, BitVec.toNat_add, ih, Finset.sum_range_succ]
      omega

theorem totalPToAux_toNat (C : G.LocalConfiguration) (L : Labels G 5 C) :
    (totalPToAux 1 5 (graphArc G L) (graphPToZ G L)).toNat =
      edgeCount G C.P (auxiliarySet G C) := by
  have hRewrite : totalPToAux 1 5 (graphArc G L) (graphPToZ G L) =
      sumCount 6 fun p ↦
        pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p := by
    simp only [totalPToAux, totalPToZ, totalPToQ, pAuxOut,
      pZOut, pToQ, show (1 = 0) = False by decide, if_false,
      sumCount, count, bitCount]
    bv_decide
  rw [hRewrite, toNat_sumCount]
  have hEach : ∀ i : Fin 6,
      (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) i).toNat =
        directCount G (auxiliarySet G C) (L.p i).1 := by
    intro i
    exact pAuxOut_toNat G C L i i.isLt
  have hSum : (∑ i ∈ Finset.range 6,
      (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) i).toNat) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [edgeCount_eq_sum_fin G C.P (auxiliarySet G C) L.p,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ ↦ hEach i)
  rw [hSum]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hP : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hP, auxiliarySet_card G C L] at hCap
  exact Nat.mod_eq_of_lt (by omega)

theorem externalMissing_toNat (C : G.LocalConfiguration) (L : Labels G 5 C) :
    (HardCore.externalMissing (graphArc G L) (graphPToZ G L)).toNat =
      36 - edgeCount G C.P (auxiliarySet G C) := by
  rw [HardCore.externalMissing, BitVec.toNat_sub, totalPToAux_toNat G C L]
  have hCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hP : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  rw [hP, auxiliarySet_card G C L] at hCap
  change ((256 - edgeCount G C.P (auxiliarySet G C) + 36) % 256) =
    36 - edgeCount G C.P (auxiliarySet G C)
  omega

set_option maxHeartbeats 5000000 in
theorem effectiveTable_graph (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hmBound :
      (HardCore.externalMissing (graphArc G L) (graphPToZ G L)).toNat ≤ 11)
    (p : Nat) (hp : p < 6) :
    (effectiveTable (HardCore.externalMissing (graphArc G L) (graphPToZ G L))
      (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p)).toNat ≤
      (directAuxEffectiveUnion G C (auxiliarySet G C)
        (L.p ⟨p, hp⟩).1).card := by
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  let S := directAuxNeighbors G E v
  let U := directAuxEffectiveUnion G C E v
  let m := 36 - edgeCount G C.P E
  let s := S.card
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = 6 := by simpa [E] using auxiliarySet_card G C L
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hs : s ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hRow : 6 - s ≤ m := by
    have hOther : ∑ q ∈ C.P.erase v, directCount G E q ≤ 30 := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase v, 6 := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 30 := by simp [Finset.card_erase_of_mem hvP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (directCount G E) hvP
    have hEdge : edgeCount G C.P E =
        (∑ q ∈ C.P.erase v, directCount G E q) + directCount G E v := by
      unfold edgeCount
      omega
    have hSCard : s = directCount G E v := rfl
    dsimp [m]
    omega
  have hLower :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.directAuxEffective_capacity_lower
      G C hMin E (auxiliarySet_disjoint_P G C) v
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP :=
    SeymourEight.BSevenKThree.RSix.XFourNoRoot.EffectiveBridge.directAux_to_P_capacity
      G C hG E hPCard 6 hECard v hvP
  have hMN :
      (HardCore.externalMissing (graphArc G L) (graphPToZ G L)).toNat = m := by
    simpa [m, E] using externalMissing_toNat G C L
  have hSN :
      (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p).toNat = s := by
    rw [pAuxOut_toNat G C L p hp]
    rfl
  have hMBV : HardCore.externalMissing (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [hMN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hSBV : pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p =
      BitVec.ofNat 8 s := by
    apply BitVec.eq_of_toNat_eq
    rw [hSN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : m ≤ 11 := by simpa [hMN] using hmBound
  change s * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hInternal
  change edgeCount G S C.P ≤ m - (6 - s) at hToP
  change (effectiveTable (HardCore.externalMissing (graphArc G L) (graphPToZ G L))
    (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p)).toNat ≤ U.card
  simp only [effectiveTable]
  rw [hMBV, hSBV]
  interval_cases m <;> interval_cases s <;>
    simp [effectiveAt, Nat.choose, BitVec.toNat_ofNat]
      at hm hs hRow hInternal hToP hLower ⊢ <;>
    omega

theorem pStrictSecond_true_mem (C : G.LocalConfiguration) (L : Labels G 5 C)
    (p r : Nat) (hp : p < 6) (hr : r < 6)
    (hSecond : strictSecondLocal (graphArc G L) (8 + p) (8 + r) = true) :
    (L.p ⟨r, hr⟩).1 ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1 := by
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 14 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  have hFirst' : G.Adj (localVertex G L (8 + p))
      (localVertex G L middle) := by
    rw [graphArc_eq_adj G C L (8 + p) middle (by omega) (by omega)] at hFirst
    exact of_decide_eq_true hFirst
  have hLast' : G.Adj (localVertex G L middle)
      (localVertex G L (8 + r)) := by
    rw [graphArc_eq_adj G C L middle (8 + r) hm (by omega)] at hLast
    exact of_decide_eq_true hLast
  have hNot' : ¬G.Adj (localVertex G L (8 + p))
      (localVertex G L (8 + r)) := by
    rw [graphArc_eq_adj G C L (8 + p) (8 + r) (by omega) (by omega)] at hNot
    have hNotBool : decide (G.Adj (localVertex G L (8 + p))
        (localVertex G L (8 + r))) = false := by simpa using hNot
    exact decide_eq_false_iff_not.mp hNotBool
  have hneV : (L.p ⟨r, hr⟩).1 ≠ (L.p ⟨p, hp⟩).1 := by
    intro heq
    apply hne
    have hi : (⟨r, hr⟩ : Fin 6) = ⟨p, hp⟩ := by
      apply L.p.injective
      exact Subtype.ext heq
    exact congrArg (fun n : Nat ↦ 8 + n) (Fin.ext_iff.mp hi)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨localVertex G L middle, ?_, ?_⟩, ?_, hneV⟩
  · simpa [localVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega] using hFirst'
  · simpa [localVertex, show ¬8 + r < 8 by omega,
      show 8 + r < 14 by omega] using hLast'
  · simpa [localVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega, show ¬8 + r < 8 by omega,
      show 8 + r < 14 by omega] using hNot'

theorem pSecondPCount_le_graph (C : G.LocalConfiguration) (L : Labels G 5 C)
    (p : Nat) (hp : p < 6) :
    (pSecondPCount (graphArc G L) p).toNat ≤
      (C.P.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  apply SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.count_le_filterCard
    C.P L.p
    (fun r ↦ strictSecondLocal (graphArc G L) (8 + p) (8 + r))
    (fun v ↦ v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1)
    (by omega)
  intro r hr'
  exact pStrictSecond_true_mem G C L p r hp r.isLt hr'

theorem auxiliarySet_eq_reached (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hy : BSevenKThree.y G C = 1) :
    auxiliarySet G C =
      SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet G C := by
  have hSub : reachedQ G C ⊆ C.Q := Finset.inter_subset_left
  have hReachedCard : (reachedQ G C).card = 1 := hy
  have hQCard : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
  have hReached : reachedQ G C = C.Q :=
    Finset.eq_of_subset_of_card_le hSub (by omega)
  have hCross : BSevenKTwo.reachedQ G C = reachedQ G C := by rfl
  rw [SeymourEight.BSevenKTwo.RSix.XFourNoRoot.auxiliarySet,
    hCross, hReached]

theorem effectiveTable_toNat_le (m s : BitVec 8) :
    (effectiveTable m s).toNat ≤ 13 := by
  have h : (effectiveTable m s).ule (13 : BitVec 8) = true := by
    unfold effectiveTable effectiveAt
    bv_decide
  simpa [BitVec.ule_eq_decide] using h

set_option maxHeartbeats 5000000 in
theorem pEffective_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 5)
    (hy : BSevenKThree.y G C = 1)
    (hmBound :
      (HardCore.externalMissing (graphArc G L) (graphPToZ G L)).toNat ≤ 11) :
    (all 6 fun p ↦ pEffective (graphArc G L) (graphPToZ G L) p) = true := by
  rw [all_eq_true_iff]
  intro p hp
  let E := auxiliarySet G C
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hH := pHOut_toNat G C L hHCard p hp
  have hTable := effectiveTable_graph G C L hG hMin hmBound p hp
  have hPS := pSecondPCount_le_graph G C L p hp
  have hEeq := auxiliarySet_eq_reached G C L hy
  have hUnion :=
    SeymourEight.BSevenKTwo.RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG E hEeq v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨v, hs⟩)
  have hDegree := HardAuxBridge.pDegree_toNat G C L hG p hp
  have hNatural :
      (pSecondPCount (graphArc G L) p).toNat +
          (effectiveTable (HardCore.externalMissing (graphArc G L) (graphPToZ G L))
            (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p)).toNat + 1 ≤
        (HardCore.pDegree (graphArc G L) (graphPToZ G L) p).toNat +
          (HardCore.pHOut (graphArc G L) p).toNat := by
    have hUnion' := hUnion
    change (C.P.filter fun w ↦ w ∈ G.secondOutNeighborFinset v).card +
        (directAuxEffectiveUnion G C E v).card ≤
          G.secondOutdegree v + directCount G C.H v at hUnion'
    dsimp [v, E] at hPS hTable hNS hDegree hH hUnion'
    omega
  have hRhs :
      pOut (graphArc G L) p + 2 * HardCore.pHOut (graphArc G L) p +
          pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p =
        HardCore.pDegree (graphArc G L) (graphPToZ G L) p +
          HardCore.pHOut (graphArc G L) p := by
    unfold HardCore.pDegree
    bv_decide
  simp only [pEffective]
  rw [hRhs]
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  have hPSLe : (pSecondPCount (graphArc G L) p).toNat ≤ 6 :=
    hPS.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard)
  have hTableLe := effectiveTable_toNat_le
    (HardCore.externalMissing (graphArc G L) (graphPToZ G L))
    (pAuxOut 1 5 (graphArc G L) (graphPToZ G L) p)
  have hDegreeLe :
      (HardCore.pDegree (graphArc G L) (graphPToZ G L) p).toNat ≤ 20 := by
    rw [hDegree]
    have hCaptured : G.outNeighborFinset v ⊆
        localSet G C ∪ externalTargets G C := by
      intro w hw
      have hw' := BSixKThree.P_outgoingCaptured_general G C hG v hvP hw
      rcases Finset.mem_union.mp hw' with hwLocal | hwExt
      · apply Finset.mem_union_left
        rcases Finset.mem_union.mp hwLocal with hwHP | hwQ
        · rcases Finset.mem_union.mp hwHP with hwH | hwP
          · exact Finset.mem_union_left C.B
              (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
          · exact Finset.mem_union_right C.A
              (Digraph.LocalConfiguration.P_subset_B (G := G) C hwP)
        · exact Finset.mem_union_right C.A
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hwQ)
      · exact Finset.mem_union_right _ hwExt
    have hCard : (localSet G C ∪ externalTargets G C).card = 20 := by
      have hDis : Disjoint (localSet G C) (externalTargets G C) := by
        simpa [localSet] using
          (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG)
      rw [Finset.card_union_of_disjoint hDis]
      have hLocal : (localSet G C).card = 15 := by
        simpa using (Fintype.card_congr (localEquiv G C L)).symm
      have hExt : (externalTargets G C).card = 5 := by
        simpa using (Fintype.card_congr L.z).symm
      omega
    have hEq := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
      G v (localSet G C ∪ externalTargets G C) hCaptured
    rw [hEq]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hCard
  have hHLe : (HardCore.pHOut (graphArc G L) p).toNat ≤ 5 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hOne : (1 : BitVec 8).toNat = 1 := by decide
  rw [hOne]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  exact hNatural

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardEffectiveBridge
