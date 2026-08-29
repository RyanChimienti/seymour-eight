import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.ActualTailBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionDefs

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletionBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  CommonBridge ActualTailBridge HDeletion

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 3000000 in
theorem aDegree_toNat_eq_outdegree (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (source : Nat)
    (hs : source < 8) :
    (aDegree (graphArc G L) source).toNat =
      G.outdegree (L.a ⟨source, hs⟩).1 := by
  have hAO := aOut_toNat G C L source hs
  have hBO := aBOut_toNat G C L source hs
  have hDegree := A_outdegree_eq_blocks G C L hG source hs
  rw [aDegree, BitVec.toNat_add, hAO, hBO,
    Nat.mod_eq_of_lt (by
      have hA := Finset.card_le_card
        (Finset.filter_subset (G.Adj (L.a ⟨source, hs⟩).1) C.A)
      have hB := Finset.card_le_card
        (Finset.filter_subset (G.Adj (L.a ⟨source, hs⟩).1) C.B)
      have hACard : C.A.card = 8 := by
        simpa using (Fintype.card_congr L.a).symm
      have hPCard : C.P.card = 6 := by
        simpa using (Fintype.card_congr L.p).symm
      have hQCard : C.Q.card = 1 := by
        simpa using (Fintype.card_congr L.q).symm
      have hBCard : C.B.card = 7 := by
        rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
        have hr : C.r = 6 := by
          simpa [Digraph.LocalConfiguration.r] using hPCard
        omega
      change directCount G C.A (L.a ⟨source, hs⟩).1 ≤ C.A.card at hA
      change directCount G C.B (L.a ⟨source, hs⟩).1 ≤ C.B.card at hB
      omega)]
  exact hDegree.symm

set_option maxHeartbeats 3000000 in
theorem hQDeletionCondition_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (h : Nat) (hh : h < 7) :
    (!(aDegree (graphArc G L) (1 + h) == 8 &&
        aToQ (graphArc G L) (1 + h)) ||
      (7 : BitVec 8).ule
        (hDeleteQCount (graphArc G L) (graphPToZ G L) h)) = true := by
  let sourceIndex := 1 + h
  let source := (L.a ⟨sourceIndex, by omega⟩).1
  let q := (L.q 0).1
  by_cases hEligible :
      (aDegree (graphArc G L) sourceIndex == 8 &&
        aToQ (graphArc G L) sourceIndex) = true
  · have hEligibleOrig :
        (aDegree (graphArc G L) (1 + h) == 8 &&
          aToQ (graphArc G L) (1 + h)) = true := by
      simpa [sourceIndex] using hEligible
    have hEligible' := hEligible
    simp only [Bool.and_eq_true] at hEligible'
    have hDegreeBits : aDegree (graphArc G L) sourceIndex = 8 := by
      simpa using hEligible'.1
    have hDegree : G.outdegree source = 8 := by
      have hNat := congrArg BitVec.toNat hDegreeBits
      rw [aDegree_toNat_eq_outdegree G C L hG sourceIndex (by omega)] at hNat
      simpa [source] using hNat
    have hGraphArc : G.Adj source q := by
      rw [aToQ_graph G L sourceIndex (by omega)] at hEligible'
      simpa [source, q] using of_decide_eq_true hEligible'.2
    let S := (G.outNeighborFinset source).erase q
    let E := G.outNeighborFinsetOf S \ (S ∪ {source})
    have hExpansion : 7 ≤ E.card := by
      simpa [source, q, S, E] using
        Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour hDegree hGraphArc
    have hSourceA : source ∈ C.A := (L.a ⟨sourceIndex, by omega⟩).2
    have hQSingleton : C.Q = {q} := by
      simpa [q] using qSingleton G C L
    have hESubset : E ⊆ retainedVertexSet G C := by
      intro v hvE
      rcases Finset.mem_sdiff.mp hvE with ⟨hvReach, _⟩
      obtain ⟨middle, hmS, hmv⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
      have hmOut : middle ∈ G.outNeighborFinset source :=
        Finset.mem_of_mem_erase hmS
      rcases Finset.mem_union.mp
          (SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
            G C hG source hSourceA hmOut) with hmA | hmB
      · rcases Finset.mem_union.mp
            (SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
              G C hG middle hmA
                ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)) with hvA | hvB
        · exact Finset.mem_union_left (externalTargets G C)
            (Finset.mem_union_left C.Q (Finset.mem_union_left C.P hvA))
        · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hvB
          rcases Finset.mem_union.mp hvB with hvP | hvQ
          · exact Finset.mem_union_left (externalTargets G C)
              (Finset.mem_union_left C.Q (Finset.mem_union_right C.A hvP))
          · exact Finset.mem_union_left (externalTargets G C)
              (Finset.mem_union_right (C.A ∪ C.P) hvQ)
      · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hmB
        rcases Finset.mem_union.mp hmB with hmP | hmQ
        · simpa [AuxiliaryBridge.namedVertexSet] using
            p_outgoing_mem_named G C L hG hmP hmv
        · have hmEqQ : middle = q := by simpa [hQSingleton] using hmQ
          exact ((Finset.mem_erase.mp hmS).1 hmEqQ).elim
    have hCount : E.card ≤
        (hDeleteQCount (graphArc G L) (graphPToZ G L) h).toNat := by
      have hFilter := filterCard_le_count (V := V) (retainedVertexSet G C)
        (retainedLabelEquiv G C L hG)
        (hDeleteQSecond (graphArc G L) (graphPToZ G L) h)
        (fun v ↦ v ∈ E) (by omega) (by
          intro target htE
          rw [retainedLabelEquiv_val] at htE
          rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
          obtain ⟨middle, hmS, hmt⟩ :=
            (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
          have hmOut : middle ∈ G.outNeighborFinset source :=
            Finset.mem_of_mem_erase hmS
          have hmAdj : G.Adj source middle :=
            (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
          have hmIndex : ∃ i : Fin 14, labelledVertex G L i = middle := by
            rcases Finset.mem_union.mp
                (SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
                  G C hG source hSourceA hmOut) with hmA | hmB
            · obtain ⟨i, hi⟩ := L.a.surjective ⟨middle, hmA⟩
              refine ⟨⟨i.val, by omega⟩, ?_⟩
              simp [labelledVertex, i.isLt, congrArg Subtype.val hi]
            · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hmB
              rcases Finset.mem_union.mp hmB with hmP | hmQ
              · obtain ⟨i, hi⟩ := L.p.surjective ⟨middle, hmP⟩
                refine ⟨⟨8 + i.val, by omega⟩, ?_⟩
                simp [labelledVertex, show ¬8 + i.val < 8 by omega,
                  show 8 + i.val < 14 by omega, congrArg Subtype.val hi]
              · have hmEqQ : middle = q := by simpa [hQSingleton] using hmQ
                exact ((Finset.mem_erase.mp hmS).1 hmEqQ).elim
          obtain ⟨middleIndex, hmLabel⟩ := hmIndex
          have htNeSource : target.val ≠ sourceIndex := by
            intro heq
            apply htOutside
            apply Finset.mem_union_right S
            apply Finset.mem_singleton.mpr
            simp [source, sourceIndex, heq, labelledVertex,
              show 1 + h < 8 by omega]
          have hmNeSource : middleIndex.val ≠ sourceIndex := by
            intro heq
            have hmEqSource : middle = source := by
              rw [← hmLabel]
              simp [heq, source, sourceIndex, labelledVertex,
                show 1 + h < 8 by omega]
            exact hG.1 source (hmEqSource ▸ hmAdj)
          have hmNeTarget : middleIndex.val ≠ target.val := by
            intro heq
            have hmEqTarget : middle = labelledVertex G L target := by
              rw [← hmLabel, heq]
            exact hG.1 middle (hmEqTarget ▸ hmt)
          have hFirst : coreArc 3 (graphArc G L) (graphPToZ G L)
              sourceIndex middleIndex = true := by
            rw [coreArc_graph G C L hG sourceIndex middleIndex
              (by omega) (by omega), hmLabel]
            simpa [source, sourceIndex, labelledVertex,
              show 1 + h < 8 by omega] using decide_eq_true hmAdj
          have hLast : coreArc 3 (graphArc G L) (graphPToZ G L)
              middleIndex target = true := by
            rw [coreArc_graph G C L hG middleIndex target
              (by omega) target.isLt, hmLabel]
            exact decide_eq_true hmt
          have hNotDirect :
              !(decide (target.val ≠ 14) &&
                coreArc 3 (graphArc G L) (graphPToZ G L)
                  sourceIndex target) = true := by
            by_cases htQ : target.val = 14
            · simp [htQ]
            · have hCoreFalse : coreArc 3 (graphArc G L) (graphPToZ G L)
                  sourceIndex target = false := by
                rw [coreArc_graph G C L hG sourceIndex target
                  (by omega) target.isLt]
                apply decide_eq_false_iff_not.mpr
                intro hDirect
                apply htOutside
                apply Finset.mem_union_left {source}
                apply Finset.mem_erase.mpr
                refine ⟨?_, (Digraph.mem_outNeighborFinset (G := G)).mpr ?_⟩
                · intro htEqQ
                  have hTarget14 : labelledVertex G L 14 = q := by
                    simp [labelledVertex, q, show ¬14 < 8 by omega]
                  have hVals :
                      (retainedLabelEquiv G C L hG target).1 =
                        (retainedLabelEquiv G C L hG
                          (⟨14, by omega⟩ : Fin 18)).1 := by
                    rw [retainedLabelEquiv_val, retainedLabelEquiv_val,
                      hTarget14]
                    exact htEqQ
                  have hFin : target = (⟨14, by omega⟩ : Fin 18) :=
                    (retainedLabelEquiv G C L hG).injective
                      (Subtype.ext hVals)
                  exact htQ (Fin.ext_iff.mp hFin)
                · simpa [source, sourceIndex, labelledVertex,
                    show 1 + h < 8 by omega] using hDirect
              simp [htQ, hCoreFalse]
          unfold hDeleteQSecond
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · rw [Bool.and_eq_true]
            exact ⟨decide_eq_true htNeSource,
              by simpa [sourceIndex] using hNotDirect⟩
          · rw [any_eq_true_iff]
            refine ⟨middleIndex.val, middleIndex.isLt, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨⟨hmNeSource, hmNeTarget⟩, hFirst⟩, hLast⟩)
      change ((retainedVertexSet G C).filter (fun v ↦ v ∈ E)).card ≤ _ at hFilter
      have hFilterEq :
          (retainedVertexSet G C).filter (fun v ↦ v ∈ E) = E :=
        by
          ext v
          simp only [Finset.mem_filter]
          constructor
          · exact fun hv ↦ hv.2
          · exact fun hv ↦ ⟨hESubset hv, hv⟩
      rw [hFilterEq] at hFilter
      simpa [hDeleteQCount] using hFilter
    have hSeven := hExpansion.trans hCount
    simp [BitVec.ule_eq_decide, hSeven]
  · have hEligibleFalse := Bool.eq_false_of_not_eq_true hEligible
    have hEligibleOrig :
        (aDegree (graphArc G L) (1 + h) == 8 &&
          aToQ (graphArc G L) (1 + h)) = false := by
      simpa [sourceIndex] using hEligibleFalse
    simp only [hEligibleOrig, Bool.not_false, Bool.true_or]

set_option maxHeartbeats 3000000 in
theorem hQDeletionConditions_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    hQDeletionConditions (graphArc G L) (graphPToZ G L) = true := by
  rw [hQDeletionConditions, all_eq_true_iff]
  intro h hh
  exact hQDeletionCondition_true G hBound C L hG hNoSeymour h hh

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletionBridge
