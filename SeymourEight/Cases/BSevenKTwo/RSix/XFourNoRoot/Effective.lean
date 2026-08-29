import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Labels
import SeymourEight.Cases.BSevenKTwo.Counting

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot

open CertificateBridge Shared Core Bridge Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def auxiliarySet (C : G.LocalConfiguration) : Finset V :=
  reachedQ G C ∪ externalTargets G C

def directAuxNeighbors (E : Finset V) (p : V) : Finset V :=
  E.filter (G.Adj p)

def directAuxEffectiveUnion (C : G.LocalConfiguration)
    (E : Finset V) (p : V) : Finset V :=
  G.outNeighborFinsetOf (directAuxNeighbors G E p) \
    (C.P ∪ directAuxNeighbors G E p)

omit [Fintype V] [DecidableEq V] in
theorem directAuxNeighbors_subset (E : Finset V) (p : V) :
    directAuxNeighbors G E p ⊆ E := Finset.filter_subset _ _

/-- Degree capacity for the effective union.  This deliberately uses only
the chosen auxiliary set, so it applies equally to `Z` and to `Q ∪ Z`. -/
theorem directAuxEffective_capacity_lower (C : G.LocalConfiguration)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (E : Finset V)
    (hEP : Disjoint E C.P) (p : V) :
    (directAuxNeighbors G E p).card *
        (8 - (directAuxEffectiveUnion G C E p).card) ≤
      edgeCount G (directAuxNeighbors G E p) (directAuxNeighbors G E p) +
        edgeCount G (directAuxNeighbors G E p) C.P := by
  let S := directAuxNeighbors G E p
  let U := directAuxEffectiveUnion G C E p
  have hPointwise : ∀ e ∈ S,
      8 ≤ directCount G S e + directCount G C.P e + U.card := by
    intro e heS
    have hPartition : G.outNeighborFinset e ⊆ S ∪ C.P ∪ U := by
      intro v hv
      have hev : G.Adj e v := (Digraph.mem_outNeighborFinset (G := G)).mp hv
      by_cases hvS : v ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvS)
      by_cases hvP : v ∈ C.P
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvP)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr ⟨e, heS, hev⟩,
            by simpa [hvS, hvP]⟩)
    have hSP : Disjoint S C.P :=
      Finset.disjoint_of_subset_left (directAuxNeighbors_subset G E p) hEP
    have hSPU : Disjoint (S ∪ C.P) U := by
      rw [Finset.disjoint_left]
      intro v hvSP hvU
      exact (Finset.mem_sdiff.mp hvU).2 (by
        simpa [Finset.union_comm] using hvSP)
    have hExact : G.outdegree e =
        directCount G S e + directCount G C.P e + directCount G U e := by
      have h := outdegree_eq_directCount_of_captured G (S ∪ C.P ∪ U) e hPartition
      rw [directCount_union_of_disjoint G (S ∪ C.P) U e hSPU,
        directCount_union_of_disjoint G S C.P e hSP] at h
      exact h
    have hULe : directCount G U e ≤ U.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hMinE := hMin e
    rw [hExact] at hMinE
    exact hMinE.trans (Nat.add_le_add_left hULe _)
  have hSum : S.card * 8 ≤
      edgeCount G S S + edgeCount G S C.P + S.card * U.card := by
    calc
      S.card * 8 = ∑ _e ∈ S, 8 := by simp
      _ ≤ ∑ e ∈ S, (directCount G S e + directCount G C.P e + U.card) := by
        apply Finset.sum_le_sum
        intro e he
        exact hPointwise e he
      _ = edgeCount G S S + edgeCount G S C.P + S.card * U.card := by
        unfold edgeCount
        simp only [Finset.sum_add_distrib]
        simp [Nat.add_assoc]
  have hResult : S.card * (8 - U.card) ≤
      edgeCount G S S + edgeCount G S C.P := by
    calc
      S.card * (8 - U.card) = S.card * 8 - S.card * U.card :=
        Nat.mul_sub_left_distrib S.card 8 U.card
      _ ≤ (edgeCount G S S + edgeCount G S C.P + S.card * U.card) -
          S.card * U.card := Nat.sub_le_sub_right hSum _
      _ = edgeCount G S S + edgeCount G S C.P := by omega
  simpa [S, U] using hResult

theorem directAux_to_P_capacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (E : Finset V)
    (hPCard : C.P.card = 6) (hECard : E.card = 3)
    (p : V) (hpP : p ∈ C.P) :
    edgeCount G (directAuxNeighbors G E p) C.P ≤
      (18 - edgeCount G C.P E) -
        (3 - (directAuxNeighbors G E p).card) := by
  let S := directAuxNeighbors G E p
  let T := E \ S
  have hS : S ⊆ E := directAuxNeighbors_subset G E p
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = E := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 3 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hECard]
  have hpT : directCount G T p = 0 := by
    unfold directCount internalFirstNeighbors
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e heT hpe
    exact (Finset.mem_sdiff.mp heT).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp heT).1, hpe⟩)
  have hPT : edgeCount G C.P T ≤ 5 * T.card := by
    calc
      edgeCount G C.P T ≤ ∑ q ∈ C.P, if q = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqp : q = p
        · subst q
          simp [hpT]
        · simp only [hqp, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 * T.card := by
        rw [← Finset.sum_erase_add C.P
          (fun q => if q = p then 0 else T.card) hpP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ q ∈ C.P.erase p, if q = p then 0 else T.card) =
              ∑ _q ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [if_neg (Finset.mem_erase.mp hq).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 5 * T.card := by
            rw [Finset.card_erase_of_mem hpP, hPCard]
  have hPESplit : edgeCount G C.P E =
      edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = 3 := by
    rw [hTCard]
    have hSLe : S.card ≤ 3 := (Finset.card_le_card hS).trans_eq hECard
    omega
  have hPEUpper := edgeCount_le_card_mul_card G C.P E
  rw [hPCard, hECard] at hPEUpper
  change edgeCount G S C.P ≤
    (18 - edgeCount G C.P E) - (3 - S.card)
  omega

theorem effective_seven_or_eight (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (E : Finset V) (hEP : Disjoint E C.P)
    (hPCard : C.P.card = 6) (hECard : E.card = 3)
    (hPE : 17 ≤ edgeCount G C.P E) (p : V) (hpP : p ∈ C.P) :
    7 ≤ (directAuxEffectiveUnion G C E p).card ∧
      ((directAuxNeighbors G E p).card = 2 →
        8 ≤ (directAuxEffectiveUnion G C E p).card) := by
  let S := directAuxNeighbors G E p
  let U := directAuxEffectiveUnion G C E p
  have hsLe : S.card ≤ 3 :=
    (Finset.card_le_card (directAuxNeighbors_subset G E p)).trans_eq hECard
  have hPELe : edgeCount G C.P E ≤ 18 := by
    exact (edgeCount_le_card_mul_card G C.P E).trans_eq (by rw [hPCard, hECard])
  have hMissing : 18 - edgeCount G C.P E ≤ 1 := by omega
  have hRowMissing : 3 - S.card ≤ 18 - edgeCount G C.P E := by
    have hOther : ∑ q ∈ C.P.erase p, directCount G E q ≤ 15 := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase p, 3 := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 15 := by simp [Finset.card_erase_of_mem hpP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (directCount G E) hpP
    have hSCard : S.card = directCount G E p := rfl
    unfold edgeCount at hPE hPELe ⊢
    omega
  have hsLower : 2 ≤ S.card := by omega
  have hCapacity := directAuxEffective_capacity_lower G C hMin E hEP p
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hReverse := directAux_to_P_capacity G C hG E hPCard hECard p hpP
  change S.card * (8 - U.card) ≤ edgeCount G S S + edgeCount G S C.P
    at hCapacity
  change edgeCount G S S ≤ S.card.choose 2 at hInternal
  change edgeCount G S C.P ≤
    (18 - edgeCount G C.P E) - (3 - S.card) at hReverse
  have hSeven : 7 ≤ U.card := by
    interval_cases hS : S.card <;> simp_all [Nat.choose] <;> omega
  refine ⟨by simpa [U] using hSeven, ?_⟩
  intro hsTwo
  change S.card = 2 at hsTwo
  change 8 ≤ U.card
  simp [hsTwo] at hCapacity hReverse hInternal
  omega

theorem directAuxEffectiveStrict_subset_second (C : G.LocalConfiguration)
    (E : Finset V) (p : V) (hpP : p ∈ C.P) :
    directAuxEffectiveUnion G C E p \ G.outNeighborFinset p ⊆
      G.secondOutNeighborFinset p := by
  intro v hv
  rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvNotDirect⟩
  rcases Finset.mem_sdiff.mp hvU with ⟨hvReached, hvOutside⟩
  obtain ⟨e, heS, hev⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached
  have hpe : G.Adj p e := (Finset.mem_filter.mp heS).2
  have hpv : ¬G.Adj p v := by
    simpa only [Digraph.mem_outNeighborFinset] using hvNotDirect
  have hvp : v ≠ p := by
    intro hvp
    subst v
    exact hvOutside (Finset.mem_union_left _ hpP)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨e, hpe, hev⟩, hpv, hvp⟩

theorem directAuxEffective_direct_subset_H (C : G.LocalConfiguration)
    (hG : G.IsOriented)
    (E : Finset V) (hE : E = auxiliarySet G C)
    (p : V) (hpP : p ∈ C.P) :
    directAuxEffectiveUnion G C E p ∩ G.outNeighborFinset p ⊆
      C.H.filter (G.Adj p) := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvU, hvDirect⟩
  have hpv : G.Adj p v := by
    simpa only [Digraph.mem_outNeighborFinset] using hvDirect
  have hvCaptured := BSixKThree.P_outgoingCaptured_general G C hG p hpP hvDirect
  have hvOutside := (Finset.mem_sdiff.mp hvU).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, hpv⟩
  rcases Finset.mem_union.mp hvCaptured with hvLocal | hvExternal
  · rcases Finset.mem_union.mp hvLocal with hvHP | hvQ
    · rcases Finset.mem_union.mp hvHP with hvH | hvP
      · exact hvH
      · exact (hvOutside (Finset.mem_union_left _ hvP)).elim
    · have hvReached : v ∈ reachedQ G C := by
        exact Finset.mem_inter.mpr ⟨hvQ,
          (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
            ⟨p, Finset.mem_union_right C.A1 hpP, hpv⟩⟩
      have hvE : v ∈ E := hE.symm ▸
        Finset.mem_union_left (externalTargets G C) hvReached
      have hvS : v ∈ directAuxNeighbors G E p :=
        Finset.mem_filter.mpr ⟨hvE, hpv⟩
      exact (hvOutside (Finset.mem_union_right _ hvS)).elim
  · have hvE : v ∈ E := hE.symm ▸
        Finset.mem_union_right (reachedQ G C) hvExternal
    have hvS : v ∈ directAuxNeighbors G E p :=
      Finset.mem_filter.mpr ⟨hvE, hpv⟩
    exact (hvOutside (Finset.mem_union_right _ hvS)).elim

theorem PSecond_add_directAuxEffective_card_le_second_add_H
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (E : Finset V)
    (hE : E = auxiliarySet G C) (p : V) (hpP : p ∈ C.P) :
    (C.P.filter fun v => v ∈ G.secondOutNeighborFinset p).card +
        (directAuxEffectiveUnion G C E p).card ≤
      G.secondOutdegree p + directCount G C.H p := by
  let U := directAuxEffectiveUnion G C E p
  let N := G.outNeighborFinset p
  let PS := C.P.filter fun v => v ∈ G.secondOutNeighborFinset p
  let Strict := U \ N
  let Direct := U ∩ N
  have hStrict : Strict ⊆ G.secondOutNeighborFinset p := by
    simpa [Strict, U, N] using
      directAuxEffectiveStrict_subset_second G C E p hpP
  have hPS : PS ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hDisjoint : Disjoint PS Strict := by
    rw [Finset.disjoint_left]
    intro v hvPS hvStrict
    have hvP := (Finset.mem_filter.mp hvPS).1
    have hvU := (Finset.mem_sdiff.mp hvStrict).1
    exact (Finset.mem_sdiff.mp hvU).2 (Finset.mem_union_left _ hvP)
  have hSecondUnion : PS ∪ Strict ⊆ G.secondOutNeighborFinset p :=
    Finset.union_subset hPS hStrict
  have hSecondCard : PS.card + Strict.card ≤ G.secondOutdegree p := by
    change PS.card + Strict.card ≤ (G.secondOutNeighborFinset p).card
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hSecondUnion
  have hDirect : Direct ⊆ C.H.filter (G.Adj p) := by
    simpa [Direct, U, N] using
      directAuxEffective_direct_subset_H G C hG E hE p hpP
  have hDirectCard : Direct.card ≤ directCount G C.H p := by
    unfold directCount internalFirstNeighbors
    exact Finset.card_le_card hDirect
  have hSplit := Finset.card_sdiff_add_card_inter U N
  change Strict.card + Direct.card = U.card at hSplit
  change PS.card + U.card ≤ G.secondOutdegree p + directCount G C.H p
  omega

private abbrev graphBits (L : LowLabels G C E) : Encoding :=
  coreBits G.Adj (fun i => (L.p i).1) (fun i => (L.h i).1)
    (fun i => (L.e i).1)

theorem pConditions_true_of_effective_eight (C : G.LocalConfiguration)
    (E : Finset V) (L : LowLabels G C E)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hE : E = auxiliarySet G C)
    (hPEGraph : 17 ≤ edgeCount G C.P E)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ E)
    (hEight : ∀ p ∈ C.P, 8 ≤ (directAuxEffectiveUnion G C E p).card) :
    pConditions (graphBits G L) = true := by
  rw [pConditions, Bridge.all_eq_true_iff]
  intro i hi
  let v := (L.p ⟨i, hi⟩).1
  have hBlocks :
      (pOut (graphBits G L) i).toNat = directCount G C.P v ∧
      (pHOut (graphBits G L) i).toNat = directCount G C.H v ∧
      (pEOut (graphBits G L) i).toNat = directCount G E v := by
    simpa [graphBits, v] using
      (Bridge.pBlockCounts G C.P C.H E L.p L.h L.e hG i hi)
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr L.h).symm
  have hECard : E.card = 3 := by
    simpa using (Fintype.card_congr L.e).symm
  have hPH : Disjoint C.P C.H := by
    rw [Finset.disjoint_left]
    intro w hwP hwH
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
      (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
      (Digraph.LocalConfiguration.P_subset_B (G := G) C hwP)
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [Finset.disjoint_left]
    intro w hwPH hwE
    rcases Finset.mem_union.mp hwPH with hwP | hwH
    · have hwAux := hE ▸ hwE
      rcases Finset.mem_union.mp hwAux with hwQ | hwZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP
          (Finset.mem_inter.mp hwQ).1
      · rcases Finset.mem_union.mp hwZ with hwZ | hwRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hws : w = C.s := by
              simpa [rootSecondFinset, hReach] using hwRoot
            subst w
            exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hwP
          · simp [rootSecondFinset, hReach] at hwRoot
    · have hwAux := hE ▸ hwE
      rcases Finset.mem_union.mp hwAux with hwQ | hwZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C
              (Finset.mem_inter.mp hwQ).1)
      · rcases Finset.mem_union.mp hwZ with hwZ | hwRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hwZ hwH
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hws : w = C.s := by
              simpa [rootSecondFinset, hReach] using hwRoot
            subst w
            exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
              (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
          · simp [rootSecondFinset, hReach] at hwRoot
  have hDegreeBlocks : G.outdegree v =
      directCount G C.P v + directCount G C.H v + directCount G E v := by
    have hu := hCaptured v (L.p ⟨i, hi⟩).2
    have h := outdegree_eq_directCount_of_captured G (C.P ∪ C.H ∪ E) v hu
    rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
      directCount_union_of_disjoint G C.P C.H v hPH] at h
    exact h
  have hpLe : directCount G C.P v ≤ 6 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hhLe : directCount G C.H v ≤ 6 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have heLe : directCount G E v ≤ 3 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hMinimum : (8 : BitVec 8).ule
      (pOut (graphBits G L) i + pHOut (graphBits G L) i +
        pEOut (graphBits G L) i) = true := by
    simp only [v] at hBlocks hDegreeBlocks hpLe hhLe heLe ⊢
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega :
      (pOut (graphBits G L) i).toNat + (pHOut (graphBits G L) i).toNat < 256),
      Nat.mod_eq_of_lt (by omega :
      (pOut (graphBits G L) i).toNat + (pHOut (graphBits G L) i).toNat +
        (pEOut (graphBits G L) i).toNat < 256)]
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2, ← hDegreeBlocks]
    exact hMin v
  have hSecond : (pSecondCount (graphBits G L) i).toNat ≤
      (C.P.filter fun w => w ∈ G.secondOutNeighborFinset v).card := by
    simpa [graphBits, v] using
      (Bridge.pSecondCount_le_graph G C.P C.H E L.p L.h L.e i hi)
  have hUnion := PSecond_add_directAuxEffective_card_le_second_add_H
    G C hG E hE v (L.p ⟨i, hi⟩).2
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨v, hs⟩)
  have hIneq : (pSecondCount (graphBits G L) i).toNat + 8 + 1 ≤
      (pOut (graphBits G L) i).toNat +
        2 * (pHOut (graphBits G L) i).toNat +
          (pEOut (graphBits G L) i).toNat := by
    have h8 := hEight v (L.p ⟨i, hi⟩).2
    simp only [v] at hBlocks hDegreeBlocks hSecond hUnion hNS h8 ⊢
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
    omega
  have hBool :
      (pSecondCount (graphBits G L) i + auxiliaryContribution (graphBits G L) + 1).ule
        (pOut (graphBits G L) i + 2 * pHOut (graphBits G L) i +
          pEOut (graphBits G L) i) = true := by
    have hPE : (17 : BitVec 8).ule (totalPE (graphBits G L)) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [Bridge.totalPE_toNat G C.P C.H E L.p L.h L.e hG]
      exact hPEGraph
    simp only [auxiliaryContribution, hPE, if_pos, BitVec.ule_eq_decide,
      decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_mul]
    have h8Nat : (8 : BitVec 8).toNat = 8 := by decide
    have h1Nat : (1 : BitVec 8).toNat = 1 := by decide
    have h2Nat : (2 : BitVec 8).toNat = 2 := by decide
    rw [h8Nat, h1Nat, h2Nat]
    have hsLe : (pSecondCount (graphBits G L) i).toNat ≤ 6 := by
      have hf : (C.P.filter fun w => w ∈ G.secondOutNeighborFinset v).card ≤ 6 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
      omega
    have hpBitsLe : (pOut (graphBits G L) i).toNat ≤ 6 := by
      rw [hBlocks.1]
      simpa [v] using hpLe
    have hhBitsLe : (pHOut (graphBits G L) i).toNat ≤ 6 := by
      rw [hBlocks.2.1]
      simpa [v] using hhLe
    have heBitsLe : (pEOut (graphBits G L) i).toNat ≤ 3 := by
      rw [hBlocks.2.2]
      simpa [v] using heLe
    rw [Nat.mod_eq_of_lt (by omega :
        (pSecondCount (graphBits G L) i).toNat + 8 < 256),
      Nat.mod_eq_of_lt (by omega :
        (pSecondCount (graphBits G L) i).toNat + 8 + 1 < 256),
      Nat.mod_eq_of_lt (by omega :
        2 * (pHOut (graphBits G L) i).toNat < 256),
      Nat.mod_eq_of_lt (by omega :
        (pOut (graphBits G L) i).toNat +
          2 * (pHOut (graphBits G L) i).toNat < 256),
      Nat.mod_eq_of_lt (by omega :
        (pOut (graphBits G L) i).toNat +
          2 * (pHOut (graphBits G L) i).toNat +
            (pEOut (graphBits G L) i).toNat < 256)]
    exact hIneq
  rw [Bool.and_eq_true]
  exact ⟨hMinimum, hBool⟩

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot
