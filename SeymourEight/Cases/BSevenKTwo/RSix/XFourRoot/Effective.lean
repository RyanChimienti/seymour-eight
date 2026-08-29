import SeymourEight.Cases.BSevenKTwo.RSix.XFourRoot.Labels
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourRoot.CoreDefs

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourRoot

open CertificateBridge Shared
open RSix.XFourNoRoot RSix.XFourNoRoot.Core RSix.XFourNoRoot.Bridge
open RSix.XFourNoRoot.Labels
open Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (E : Finset V) (L : LowLabels G C E) : Encoding :=
  coreBits G.Adj (fun i => (L.p i).1) (fun i => (L.h i).1)
    (fun i => (L.e i).1)

theorem effective_eight_of_root_arc (C : G.LocalConfiguration)
    (E : Finset V) (hE : E = auxiliarySet G C)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (p : V) (hpP : p ∈ C.P) (hps : G.Adj p C.s) :
    8 ≤ (directAuxEffectiveUnion G C E p).card := by
  let S := directAuxNeighbors G E p
  let U := directAuxEffectiveUnion G C E p
  have hRootE : C.s ∈ E := by
    rw [hE]
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    simp [rootSecondFinset, show ∃ q ∈ C.P, G.Adj q C.s from ⟨p, hpP, hps⟩]
  have hRootS : C.s ∈ S := Finset.mem_filter.mpr ⟨hRootE, hps⟩
  have hASubset : C.A ⊆ U := by
    intro v hvA
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨C.s, hRootS,
        (Digraph.mem_outNeighborFinset (G := G)).mp hvA⟩
    · intro hvLocal
      rcases Finset.mem_union.mp hvLocal with hvP | hvS
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
      · have hvE : v ∈ E := directAuxNeighbors_subset G E p (by
          simpa [S] using hvS)
        have hvAux : v ∈ auxiliarySet G C := hE.symm ▸ hvE
        rcases Finset.mem_union.mp hvAux with hvQ | hvExternal
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C
              (Finset.mem_inter.mp hvQ).1)
        · rcases Finset.mem_union.mp hvExternal with hvZ | hvRoot
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
          · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
            · have hvs : v = C.s := by
                simpa [rootSecondFinset, hReach] using hvRoot
              subst v
              exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
            · simp [rootSecondFinset, hReach] at hvRoot
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  exact hACard ▸ Finset.card_le_card hASubset

theorem effective_eight_of_one_defect (C : G.LocalConfiguration)
    (E : Finset V) (hE : E = auxiliarySet G C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hRoot : epsilonS G C = 1)
    (hPCard : C.P.card = 6) (hECard : E.card = 3)
    (hEP : Disjoint E C.P) (hPE : 17 ≤ edgeCount G C.P E)
    (p : V) (hpP : p ∈ C.P) :
    8 ≤ (directAuxEffectiveUnion G C E p).card := by
  by_cases hps : G.Adj p C.s
  · exact effective_eight_of_root_arc G C E hE hG hRootDegree p hpP hps
  · have hRootE : C.s ∈ E := by
      rw [hE]
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      have hReach : ∃ q ∈ C.P, G.Adj q C.s := by
        by_contra hn
        simp [epsilonS, rootSecondFinset, hn] at hRoot
      simp [rootSecondFinset, hReach]
    let S := directAuxNeighbors G E p
    have hRootNotS : C.s ∉ S := by simp [S, directAuxNeighbors, hps]
    have hSlt : S.card < 3 := by
      have hProper : S ⊂ E := Finset.ssubset_iff_subset_ne.mpr
        ⟨directAuxNeighbors_subset G E p, fun heq => hRootNotS (heq.symm ▸ hRootE)⟩
      simpa [hECard] using Finset.card_lt_card hProper
    have hOther : ∑ q ∈ C.P.erase p, directCount G E q ≤ 15 := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase p, 3 := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 15 := by simp [Finset.card_erase_of_mem hpP, hPCard]
    have hSplit := Finset.sum_erase_add C.P (directCount G E) hpP
    have hSCard : S.card = directCount G E p := rfl
    have hSLower : 2 ≤ S.card := by
      change 17 ≤ ∑ q ∈ C.P, directCount G E q at hPE
      omega
    have hSTwo : S.card = 2 := by omega
    exact (effective_seven_or_eight G C hG hMin E hEP hPCard hECard
      hPE p hpP).2 hSTwo

theorem pSecond_card_add_direct_le_five (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 6)
    (p : V) (hpP : p ∈ C.P) :
    (C.P.filter fun v => v ∈ G.secondOutNeighborFinset p).card +
        directCount G C.P p ≤ 5 := by
  let T := C.P.filter fun v => v ∈ G.secondOutNeighborFinset p
  let D := C.P.filter (G.Adj p)
  have hTD : Disjoint T D := by
    rw [Finset.disjoint_left]
    intro v hvT hvD
    have hvSecond := (Finset.mem_filter.mp hvT).2
    have hvNot := (Digraph.mem_secondOutNeighborSet (G := G)).mp
      ((Digraph.mem_secondOutNeighborFinset (G := G)).mp hvSecond)
    exact hvNot.2.1 (Finset.mem_filter.mp hvD).2
  have hpNotT : p ∉ T := by
    intro hp
    have hSecond := (Digraph.mem_secondOutNeighborSet (G := G)).mp
      ((Digraph.mem_secondOutNeighborFinset (G := G)).mp
        (Finset.mem_filter.mp hp).2)
    exact hSecond.2.2 rfl
  have hpNotD : p ∉ D := by
    intro hp
    exact hG.1 p (Finset.mem_filter.mp hp).2
  have hUnion : (T ∪ D) ∪ {p} ⊆ C.P := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvTD | hvp
    · rcases Finset.mem_union.mp hvTD with hvT | hvD
      · exact (Finset.mem_filter.mp hvT).1
      · exact (Finset.mem_filter.mp hvD).1
    · simpa using (Finset.mem_singleton.mp hvp ▸ hpP)
  have hDisjointP : Disjoint (T ∪ D) {p} := by
    rw [Finset.disjoint_left]
    intro v hvTD hvp
    have hvpEq : v = p := Finset.mem_singleton.mp hvp
    subst v
    rcases Finset.mem_union.mp hvTD with hpT | hpD
    · exact hpNotT hpT
    · exact hpNotD hpD
  have hCard := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hDisjointP,
    Finset.card_union_of_disjoint hTD, hPCard] at hCard
  simp only [Finset.card_singleton] at hCard
  simpa [T, D, directCount, internalFirstNeighbors] using hCard

theorem pConditions_true (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hRoot : epsilonS G C = 1)
    (hE : E = auxiliarySet G C)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ E) :
    rootPConditions (graphBits G E L) = true := by
  rw [rootPConditions, all_eq_true_iff]
  intro i hi
  let v := (L.p ⟨i, hi⟩).1
  have hvP : v ∈ C.P := (L.p ⟨i, hi⟩).2
  have hBlocks := Bridge.pBlockCounts G C.P C.H E L.p L.h L.e hG i hi
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr L.h).symm
  have hECard : E.card = 3 := by
    simpa using (Fintype.card_congr L.e).symm
  have hPH : Disjoint C.P C.H :=
    Digraph.LocalConfiguration.disjoint_H_P (G := G) C |>.symm
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [Finset.disjoint_left]
    intro w hwPH hwE
    have hwAux : w ∈ auxiliarySet G C := hE.symm ▸ hwE
    rcases Finset.mem_union.mp hwPH with hwP | hwH
    · rcases Finset.mem_union.mp hwAux with hwQ | hwExternal
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP
          (Finset.mem_inter.mp hwQ).1
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hwP) hwExternal
    · rcases Finset.mem_union.mp hwAux with hwQ | hwExternal
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C
            (Finset.mem_inter.mp hwQ).1)
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_H_externalTargets G C hG))
          hwH hwExternal
  have hDegree : G.outdegree v = directCount G C.P v +
      directCount G C.H v + directCount G E v := by
    have h := outdegree_eq_directCount_of_captured G (C.P ∪ C.H ∪ E)
      v (hCaptured v hvP)
    rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
      directCount_union_of_disjoint G C.P C.H v hPH] at h
    exact h
  have hpLe : directCount G C.P v ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hhLe : directCount G C.H v ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have heLe : directCount G E v ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
  have hMinimum : (8 : BitVec 8).ule
      (pOut (graphBits G E L) i + pHOut (graphBits G E L) i +
        pEOut (graphBits G E L) i) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    have hpBitsLe : (pOut (graphBits G E L) i).toNat ≤ 6 := by
      rw [hBlocks.1]
      exact hpLe
    have hhBitsLe : (pHOut (graphBits G E L) i).toNat ≤ 6 := by
      rw [hBlocks.2.1]
      exact hhLe
    have heBitsLe : (pEOut (graphBits G E L) i).toNat ≤ 3 := by
      rw [hBlocks.2.2]
      exact heLe
    rw [Nat.mod_eq_of_lt (by omega :
      (pOut (graphBits G E L) i).toNat +
        (pHOut (graphBits G E L) i).toNat < 256),
      Nat.mod_eq_of_lt (by omega :
        (pOut (graphBits G E L) i).toNat +
          (pHOut (graphBits G E L) i).toNat +
            (pEOut (graphBits G E L) i).toNat < 256)]
    rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2, ← hDegree]
    exact hMin v
  have hSecond : (pSecondCount (graphBits G E L) i).toNat ≤
      (C.P.filter fun w => w ∈ G.secondOutNeighborFinset v).card := by
    simpa [graphBits, v] using
      (Bridge.pSecondCount_le_graph G C.P C.H E L.p L.h L.e i hi)
  have hIneq : (pSecondCount (graphBits G E L) i).toNat + 8 + 1 ≤
      (pOut (graphBits G E L) i).toNat +
        2 * (pHOut (graphBits G E L) i).toNat +
          (pEOut (graphBits G E L) i).toNat := by
    by_cases hvs : G.Adj v C.s
    · have hEight := effective_eight_of_root_arc G C E hE hG hRootDegree
          v hvP hvs
      have hUnion := PSecond_add_directAuxEffective_card_le_second_add_H
        G C hG E hE v hvP
      have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun hs => hNoSeymour ⟨v, hs⟩)
      dsimp [v] at hBlocks hSecond hEight hUnion hNS hDegree ⊢
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      omega
    · have hRootE : C.s ∈ E := by
        rw [hE]
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        have hReach : ∃ q ∈ C.P, G.Adj q C.s := by
          have hCard : (rootSecondFinset G C).card = 1 := by
            simpa [epsilonS] using hRoot
          by_contra hn
          simp [rootSecondFinset, hn] at hCard
        simp [rootSecondFinset, hReach]
      have heTwo : directCount G E v ≤ 2 := by
        have hRootNot : C.s ∉ E.filter (G.Adj v) := by simp [hvs]
        have hProper : E.filter (G.Adj v) ⊂ E :=
          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun heq =>
            hRootNot (heq.symm ▸ hRootE)⟩
        have := Finset.card_lt_card hProper
        change (E.filter (G.Adj v)).card ≤ 2
        omega
      have hPSecond := pSecond_card_add_direct_le_five G C hG hPCard v hvP
      dsimp [v] at hBlocks hSecond hPSecond hDegree heTwo ⊢
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      have hMinV := hMin v
      dsimp [v] at hMinV
      omega
  have hBool :
      (pSecondCount (graphBits G E L) i + 8 + 1).ule
        (pOut (graphBits G E L) i + 2 * pHOut (graphBits G E L) i +
          pEOut (graphBits G E L) i) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_mul]
    have hsLe : (pSecondCount (graphBits G E L) i).toNat ≤ 6 := by
      have hCardLe :
          (C.P.filter fun w => w ∈ G.secondOutNeighborFinset v).card ≤ 6 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
      exact hSecond.trans hCardLe
    have hpBitsLe : (pOut (graphBits G E L) i).toNat ≤ 6 := by
      rw [hBlocks.1]
      exact hpLe
    have hhBitsLe : (pHOut (graphBits G E L) i).toNat ≤ 6 := by
      rw [hBlocks.2.1]
      exact hhLe
    have heBitsLe : (pEOut (graphBits G E L) i).toNat ≤ 3 := by
      rw [hBlocks.2.2]
      exact heLe
    have h1Nat : (1 : BitVec 8).toNat = 1 := by decide
    have h2Nat : (2 : BitVec 8).toNat = 2 := by decide
    have h8Nat : (8 : BitVec 8).toNat = 8 := by decide
    rw [h1Nat, h2Nat, h8Nat]
    rw [Nat.mod_eq_of_lt (by omega :
        (pSecondCount (graphBits G E L) i).toNat + 8 < 256),
      Nat.mod_eq_of_lt (by omega :
        (pSecondCount (graphBits G E L) i).toNat + 8 + 1 < 256),
      Nat.mod_eq_of_lt (by omega :
        2 * (pHOut (graphBits G E L) i).toNat < 256),
      Nat.mod_eq_of_lt (by omega :
        (pOut (graphBits G E L) i).toNat +
          2 * (pHOut (graphBits G E L) i).toNat < 256),
      Nat.mod_eq_of_lt (by omega :
        (pOut (graphBits G E L) i).toNat +
          2 * (pHOut (graphBits G E L) i).toNat +
            (pEOut (graphBits G E L) i).toNat < 256)]
    omega
  rw [Bool.and_eq_true]
  exact ⟨hMinimum, hBool⟩

end SeymourEight.BSevenKTwo.RSix.XFourRoot
