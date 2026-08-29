import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.GraphBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.Assembly

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge

open Shared Shared.FiniteCore
open RSix.XTwoNoRoot
open RSix.XTwoNoRoot.Labels RSix.XTwoNoRoot.Encoding
open RSix.XTwoNoRoot.Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) : Core.Encoding :=
  Encoding.coreBits G.Adj L

theorem q_disjoint_externalTargets (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) : Disjoint ({q} : Finset V) (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvq hvE
  have hv : v = q := Finset.mem_singleton.mp hvq
  subst v
  exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
    (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ) hvE

theorem PH_disjoint_auxiliary (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hG : G.IsOriented) :
    Disjoint (C.P ∪ C.H) ({q} ∪ externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvPH hvE
  rcases Finset.mem_union.mp hvPH with hvP | hvH
  · rcases Finset.mem_union.mp hvE with hvq | hvExt
    · have hv : v = q := Finset.mem_singleton.mp hvq
      subst v
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hqQ
    · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExt
  · rcases Finset.mem_union.mp hvE with hvq | hvExt
    · have hv : v = q := Finset.mem_singleton.mp hvq
      subst v
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
        (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
    · exact (Finset.disjoint_left.mp
        (BSixKThree.disjoint_H_externalTargets G C hG)) hvH hvExt

theorem P_outdegree_eq_blocks (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (hG : G.IsOriented)
    (p : V) (hpP : p ∈ C.P) :
    G.outdegree p = Shared.directCount G C.P p + Shared.directCount G C.H p +
      Shared.directCount G ({q} ∪ externalTargets G C) p := by
  have hCaptured : G.outNeighborFinset p ⊆
      C.P ∪ C.H ∪ ({q} ∪ externalTargets G C) := by
    intro w hw
    have hc := BSixKThree.P_outgoingCaptured_general G C hG p hpP hw
    simp only [Finset.mem_union] at hc ⊢
    rcases hc with (((hwH | hwP) | hwQ) | hwExt)
    · exact Or.inl (Or.inr hwH)
    · exact Or.inl (Or.inl hwP)
    · exact Or.inr (Or.inl (by simpa [hQ] using hwQ))
    · exact Or.inr (Or.inr hwExt)
  have hPH : Disjoint C.P C.H :=
    (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
  have hPHE := PH_disjoint_auxiliary G C q hqQ hG
  have hDegree := outdegree_eq_directCount_of_captured G
    (C.P ∪ C.H ∪ ({q} ∪ externalTargets G C)) p hCaptured
  rw [directCount_union_of_disjoint G (C.P ∪ C.H)
      ({q} ∪ externalTargets G C) p hPHE,
    directCount_union_of_disjoint G C.P C.H p hPH] at hDegree
  exact hDegree

theorem pMinimumDegreeReached_true {eCount : Nat}
    (C : G.LocalConfiguration) (q : V) (hqQ : q ∈ C.Q)
    (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin eCount ≃ {v : V // v ∈ E}) (heBound : eCount ≤ 5)
    (hELab : ∀ i : Fin eCount,
      L.e ⟨i.val, lt_of_lt_of_le i.isLt heBound⟩ = (eEq i).1) :
    all 6 (fun p => (8 : BitVec 8).ule
      (pOut (graphBits G L) p + pHOut (graphBits G L) p +
        pEOut eCount (graphBits G L) p)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  have hBlocks := XTwoNoRoot.GraphBridge.pBlockCounts G C q L hG hHCard E eEq
    heBound hELab p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hECard : E.card = eCount := by simpa using (Fintype.card_congr eEq).symm
  have hSmall : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G E (L.p ⟨p, hp⟩).1 < 256 := by
    have h1 := Finset.card_le_card (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.P)
    have h2 := Finset.card_le_card (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.H)
    have h3 := Finset.card_le_card (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) E)
    change Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at h1
    change Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at h2
    change Shared.directCount G E (L.p ⟨p, hp⟩).1 ≤ E.card at h3
    rw [hpCard] at h1
    rw [hHCard] at h2
    rw [hECard] at h3
    omega
  have hSmallPH : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 < 256 := by omega
  rw [Nat.mod_eq_of_lt hSmallPH, Nat.mod_eq_of_lt hSmall]
  rw [hE, ← P_outdegree_eq_blocks G C q hqQ hQ hG _ (L.p _).2]
  exact hMin _

theorem labelledExternalReached_true {zCount offset : Nat}
    (C : G.LocalConfiguration) (q : V) (L : ReachedLabels G C q)
    (eZ : Fin zCount ≃ {v : V // v ∈ externalTargets G C})
    (hBound : offset + zCount ≤ 5)
    (hLabel : ∀ z : Fin zCount,
      L.e ⟨offset + z.val, by omega⟩ = (eZ z).1) :
    all zCount (fun z => any 6 fun p =>
      pToE (graphBits G L) p (offset + z)) = true := by
  rw [all_eq_true_iff]
  intro z hz
  rw [any_eq_true_iff]
  have hzMem := (eZ ⟨z, hz⟩).2
  rcases Finset.mem_union.mp hzMem with hzMem | hRootMem
  · rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
    obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
    refine ⟨i.val, i.isLt, ?_⟩
    rw [pToE_coreBits G.Adj L i (offset + z) i.isLt (by omega)]
    simpa [congrArg Subtype.val hi, hLabel ⟨z, hz⟩] using hpz
  · by_cases hRootReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hRootReach' := hRootReach
      obtain ⟨p, hp, hps⟩ := hRootReach
      have hRootLabel : (eZ ⟨z, hz⟩).1 = C.s := by
        simpa [rootSecondFinset, hRootReach'] using hRootMem
      obtain ⟨i, hi⟩ := L.p.surjective ⟨p, hp⟩
      refine ⟨i.val, i.isLt, ?_⟩
      rw [pToE_coreBits G.Adj L i (offset + z) i.isLt (by omega)]
      simpa [hRootLabel, congrArg Subtype.val hi, hLabel ⟨z, hz⟩] using hps
    · simp [rootSecondFinset, hRootReach] at hRootMem

theorem H_to_P_add_missing_le (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 6)
    (hHCard : C.H.card = 4) (hECard : (externalTargets G C).card = 4) :
    edgeCount G C.H C.P +
      (30 - edgeCount G C.P ({q} ∪ externalTargets G C)) ≤ 21 := by
  have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hDis := q_disjoint_externalTargets G C q hqQ
  have hPE : edgeCount G C.P ({q} ∪ externalTargets G C) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} (externalTargets G C) hDis, ← hQ]
  rw [hHCard, ← hPE] at hCap
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ externalTargets G C)
  have hpCard : C.P.card = 6 := hr
  have hUnionCard : ({q} ∪ externalTargets G C).card = 5 := by
    rw [Finset.card_union_of_disjoint hDis]
    simp [hECard]
  rw [hpCard, hUnionCard] at hPECap
  omega

theorem H_to_P_add_missing_four_le (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hr : C.r = 6)
    (hHCard : C.H.card = 4) (hECard : (externalTargets G C).card = 3) :
    edgeCount G C.H C.P +
      (24 - edgeCount G C.P ({q} ∪ externalTargets G C)) ≤ 15 := by
  have hCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hDis := q_disjoint_externalTargets G C q hqQ
  have hPE : edgeCount G C.P ({q} ∪ externalTargets G C) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} (externalTargets G C) hDis, ← hQ]
  rw [hHCard, ← hPE] at hCap
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ externalTargets G C)
  have hpCard : C.P.card = 6 := hr
  have hUnionCard : ({q} ∪ externalTargets G C).card = 4 := by
    rw [Finset.card_union_of_disjoint hDis]
    simp [hECard]
  rw [hpCard, hUnionCard] at hPECap
  omega

theorem externalMissing_add_three_le_ph (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hr : C.r = 6) (hECard : (externalTargets G C).card = 4) :
    30 - edgeCount G C.P ({q} ∪ externalTargets G C) + 3 ≤
      edgeCount G C.P C.H := by
  have hPCard : C.P.card = 6 := hr
  have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hInternal := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hInternal
  norm_num [Nat.choose] at hInternal
  have hDis := q_disjoint_externalTargets G C q hqQ
  have hPE : edgeCount G C.P ({q} ∪ externalTargets G C) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} (externalTargets G C) hDis, ← hQ]
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hUnionCard : ({q} ∪ externalTargets G C).card = 5 := by
    rw [Finset.card_union_of_disjoint hDis]
    simp [hECard]
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ externalTargets G C)
  rw [hPCard, hUnionCard] at hPECap
  omega

theorem pEffectiveConditionFive_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4) (hy : BSevenKTwo.y G C = 1)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (hmBound : 30 - edgeCount G C.P E ≤ 7) :
    all 6 (pEffectiveCondition 5 true (graphBits G L)) = true := by
  let bits := graphBits G L
  have hAux : E = RSix.XFourNoRoot.auxiliarySet G C := by
    rw [hE]
    exact (RSix.XThreeRoot.Assembly.auxiliarySet_eq_E G C q hQ hy).symm
  have hEP : Disjoint E C.P := by
    rw [hE, Finset.disjoint_left]
    intro w hwE hwP
    rcases Finset.mem_union.mp hwE with hwq | hwExt
    · have hwEq : w = q := Finset.mem_singleton.mp hwq
      subst w
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
    · exact (Finset.disjoint_left.mp
        (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hwP) hwExt
  rw [all_eq_true_iff]
  intro p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hBlocks := XTwoNoRoot.GraphBridge.pBlockCounts G C q L hG hHCard
    E eEq (by omega) hELab p hp
  have hTable := XTwoNoRoot.GraphBridge.individualEffectiveLowerFive_graph
    G C q L hG hMin hHCard E hEP eEq hELab hmBound p hp
  have hPS := XTwoNoRoot.GraphBridge.pSecondPCount_le_graph G C q L hG p hp
  have hTable' : (individualEffectiveLowerFive (graphBits G L) p).toNat ≤
      (RSix.XFourNoRoot.directAuxEffectiveUnion G C E
        (L.p ⟨p, hp⟩).1).card := by
    exact hTable
  have hPS' : (pSecondPCount (graphBits G L) p).toNat ≤
      (C.P.filter fun w =>
        w ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
    exact hPS
  have hUnion :=
    RSix.XFourNoRoot.PSecond_add_directAuxEffective_card_le_second_add_H
      G C hG E hAux v hvP
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨v, hs⟩)
  have hDegree : G.outdegree v = Shared.directCount G C.P v +
      Shared.directCount G C.H v + Shared.directCount G E v := by
    rw [hE]
    exact P_outdegree_eq_blocks G C q hqQ hQ hG v hvP
  have hNatural : (pSecondPCount bits p).toNat +
      (individualEffectiveLowerFive bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pEOut 5 bits p).toNat := by
    dsimp [v, bits] at hPS' hTable' hUnion hNS hDegree hBlocks ⊢
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

end SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge
