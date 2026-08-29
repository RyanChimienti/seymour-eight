import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.CoreAssembly

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# The targeted `X -> a1` deletion

The finite core retains one reduction consequence for an `X` vertex that has
degree eight and dominates both `a1` and `R`.  This file transports the
ordinary one-arc deletion expansion into the compact nineteen-vertex model.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared RepeatedSharedOmissionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem filterCard_le_coreCount {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, Q (e j).1 → b j = true) :
    (S.filter Q).card ≤ (ThetaFourCore.count n b).toNat := by
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hQ : Q (e j).1
  · simp [hQ, hGood j hQ]
  · simp [hQ]

theorem xEligible_graph_facts (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hRoot : edgeCount G C.P {C.s} = 0)
    (x : Nat) (hx : x < 4)
    (hEligible : ThetaFourCore.xEligible
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) x = true) :
    G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8 ∧
      G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1 ∧
      G.Adj (L.a ⟨3 + x, by omega⟩).1 (L.a 7).1 := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  simp only [ThetaFourCore.xEligible, Bool.and_eq_true, beq_iff_eq] at hEligible
  rcases hEligible with ⟨⟨hDegreeBits, ha1Bits⟩, hrBits⟩
  have hSource : labelledVertex G L (3 + x) = (L.a ⟨3 + x, by omega⟩).1 := by
    simp [labelledVertex, show 3 + x < 8 by omega]
  have hDegreeNat := congrArg BitVec.toNat hDegreeBits
  rw [directCount_coreBits_toNat G C L T hG hRoot (3 + x) (by omega),
    hSource] at hDegreeNat
  have ha1 : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1 := by
    rw [aArc_coreBits G.Adj _ _ _ (3 + x) 0 (by omega) (by omega)] at ha1Bits
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by
      have hfin : (⟨0, by omega⟩ : Fin 8) = 0 := by rfl
      rw [hfin]
      exact L.a_zero
    rw [ha0] at ha1Bits
    exact of_decide_eq_true ha1Bits
  have hr : G.Adj (L.a ⟨3 + x, by omega⟩).1 (L.a 7).1 := by
    rw [aArc_coreBits G.Adj _ _ _ (3 + x) 7 (by omega) (by omega)] at hrBits
    exact of_decide_eq_true hrBits
  exact ⟨hDegreeNat, ha1, hr⟩

theorem deletionReached_good (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (x : Nat) (hx : x < 4) (source : V)
    (hSourceLabel : labelledVertex G L (3 + x) = source)
    (S : Finset V) (hS : S = (G.outNeighborFinset source).erase C.a1)
    (bits : Encoding)
    (hbits : bits = coreBits G.Adj (fun i ↦ (L.p i).1)
      (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)) (target : Fin 19)
    (htNotS : labelledVertex G L target ∉ S)
    (htNeSource : labelledVertex G L target ≠ source)
    (middle : V) (middleIndex : Nat) (hmIndex : middleIndex < 15)
    (hmLabel : labelledVertex G L middleIndex = middle)
    (_hmS : middle ∈ S) (hmt : G.Adj middle (labelledVertex G L target))
    (hRetMiddle : ThetaFourCore.retainedAfterAOneDeletion bits x middleIndex = true) :
    (decide (target.1 ≠ 3 + x) &&
      !ThetaFourCore.retainedAfterAOneDeletion bits x target.1 &&
      ThetaFourCore.any 15 (fun middle =>
        ThetaFourCore.retainedAfterAOneDeletion bits x middle &&
          ThetaFourCore.coreArc bits middle target)) = true := by
  have htIndexNe : target.1 ≠ 3 + x := by
    intro heq
    apply htNeSource
    simpa [heq] using hSourceLabel
  have htNotRet : ThetaFourCore.retainedAfterAOneDeletion bits x target = false := by
    apply Bool.eq_false_of_not_eq_true
    intro htRet
    simp only [ThetaFourCore.retainedAfterAOneDeletion, Bool.and_eq_true,
      decide_eq_true_eq] at htRet
    rcases htRet with ⟨htNeZero, htArc⟩
    rw [hbits, coreArc_coreBits G C L hG T.p_complete T.ph_complete
      (3 + x) target (by omega) target.isLt] at htArc
    have hGraphArc : G.Adj source (labelledVertex G L target) := by
      rw [← hSourceLabel]
      exact of_decide_eq_true htArc
    have htNeA1 : labelledVertex G L target ≠ C.a1 := by
      intro heq
      have hzero : labelledVertex G L 0 = C.a1 := by
        simpa [labelledVertex] using L.a_zero
      have hFin : target = (0 : Fin 19) := by
        apply (retainedLabelEquiv G C L).injective
        apply Subtype.ext
        simpa [retainedLabelEquiv_val, hzero] using heq
      exact htNeZero (Fin.ext_iff.mp hFin)
    apply htNotS
    rw [hS]
    apply Finset.mem_erase.mpr
    exact ⟨htNeA1, (Digraph.mem_outNeighborFinset (G := G)).mpr hGraphArc⟩
  have hArc : ThetaFourCore.coreArc bits middleIndex target = true := by
    rw [hbits, coreArc_coreBits G C L hG T.p_complete T.ph_complete
      middleIndex target hmIndex target.isLt]
    rw [hmLabel]
    exact decide_eq_true hmt
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    exact ⟨decide_eq_true htIndexNe, by simp [htNotRet]⟩
  · rw [any_eq_true_iff]
    exact ⟨middleIndex, hmIndex, by simp [hRetMiddle, hArc]⟩

theorem xDeletionExpands_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (x : Nat) (hx : x < 4)
    (hEligible : ThetaFourCore.xEligible
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) x = true) :
    ThetaFourCore.xDeletionExpands
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) x = true := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  let source := (L.a ⟨3 + x, by omega⟩).1
  let S := (G.outNeighborFinset source).erase C.a1
  let E := G.outNeighborFinsetOf S \ (S ∪ {source})
  have hFacts := xEligible_graph_facts G C L T hG hRoot x hx hEligible
  have hExpansion : 7 ≤ E.card := by
    simpa [source, S, E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hFacts.1 hFacts.2.1
  have hSourceA : source ∈ C.A := by
    exact (L.a ⟨3 + x, by omega⟩).2
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro v hvE
    rcases Finset.mem_sdiff.mp hvE with ⟨hvReach, _⟩
    obtain ⟨middle, hmS, hmv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hmOut : middle ∈ G.outNeighborFinset source := Finset.mem_of_mem_erase hmS
    rcases Finset.mem_union.mp (A_outgoingCaptured G C hG source hSourceA hmOut) with
      hmA | hmB
    · exact A_outgoingCaptured_retained G C hG T.p_eq_B middle hmA
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
    · have hmP : middle ∈ C.P := by simpa [T.p_eq_B] using hmB
      exact P_outgoingCaptured_retained G C hG T.p_eq_B hRoot middle hmP
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
  have hCount : E.card ≤ (ThetaFourCore.count 19 (fun target =>
      decide (target ≠ 3 + x) &&
        !ThetaFourCore.retainedAfterAOneDeletion bits x target &&
        ThetaFourCore.any 15 (fun middle =>
          ThetaFourCore.retainedAfterAOneDeletion bits x middle &&
            ThetaFourCore.coreArc bits middle target))).toNat := by
    have hFilter := filterCard_le_coreCount (V := V) (retainedVertexSet G C)
      (retainedLabelEquiv G C L)
      (fun target => decide (target ≠ 3 + x) &&
        !ThetaFourCore.retainedAfterAOneDeletion bits x target &&
        ThetaFourCore.any 15 (fun middle =>
          ThetaFourCore.retainedAfterAOneDeletion bits x middle &&
            ThetaFourCore.coreArc bits middle target))
      (fun v => v ∈ E) (by omega) (by
        intro target htE
        rw [retainedLabelEquiv_val] at htE
        rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
        obtain ⟨middle, hmS, hmt⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
        have hmOut : middle ∈ G.outNeighborFinset source :=
          Finset.mem_of_mem_erase hmS
        rcases Finset.mem_union.mp (A_outgoingCaptured G C hG source hSourceA hmOut) with
          hmA | hmB
        · obtain ⟨i, hi⟩ := L.a.surjective ⟨middle, hmA⟩
          let middleIndex := i.1
          have hmIndex : middleIndex < 15 := by
            dsimp [middleIndex]
            omega
          have hmLabel : labelledVertex G L middleIndex = middle := by
            simp [middleIndex, labelledVertex, i.isLt, congrArg Subtype.val hi]
          have hmNeA1 : middle ≠ C.a1 := (Finset.mem_erase.mp hmS).1
          have hmNeZero : middleIndex ≠ 0 := by
            intro hz
            have : middle = C.a1 := by
              rw [← hmLabel, hz]
              simpa [labelledVertex] using L.a_zero
            exact hmNeA1 this
          have hRetMiddle : ThetaFourCore.retainedAfterAOneDeletion bits x
              middleIndex = true := by
            unfold ThetaFourCore.retainedAfterAOneDeletion
            rw [coreArc_coreBits G C L hG T.p_complete T.ph_complete
              (3 + x) middleIndex (by omega) (by omega)]
            rw [hmLabel]
            have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
            simpa [hmNeZero, source, labelledVertex,
              show 3 + x < 8 by omega] using hadj
          have htNotS : labelledVertex G L target ∉ S := by
            intro ht
            exact htOutside (Finset.mem_union_left {source} ht)
          have htNeSource : labelledVertex G L target ≠ source := by
            intro ht
            exact htOutside (Finset.mem_union_right S (Finset.mem_singleton.mpr ht))
          refine deletionReached_good G C L T hG x hx source ?_ S rfl bits rfl target
            htNotS htNeSource middle middleIndex hmIndex hmLabel hmS hmt
            hRetMiddle
          simp [source, labelledVertex, show 3 + x < 8 by omega]
        · have hmP : middle ∈ C.P := by simpa [T.p_eq_B] using hmB
          obtain ⟨i, hi⟩ := L.p.surjective ⟨middle, hmP⟩
          let middleIndex := 8 + i.1
          have hmIndex : middleIndex < 15 := by
            dsimp [middleIndex]
            omega
          have hmLabel : labelledVertex G L middleIndex = middle := by
            simp [middleIndex, labelledVertex, show ¬8 + i.1 < 8 by omega,
              show 8 + i.1 < 15 by omega, congrArg Subtype.val hi]
          have hRetMiddle : ThetaFourCore.retainedAfterAOneDeletion bits x
              middleIndex = true := by
            unfold ThetaFourCore.retainedAfterAOneDeletion
            rw [coreArc_coreBits G C L hG T.p_complete T.ph_complete
              (3 + x) middleIndex (by omega) (by omega)]
            rw [hmLabel]
            have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
            simpa [middleIndex, source, labelledVertex,
              show 3 + x < 8 by omega] using hadj
          have htNotS : labelledVertex G L target ∉ S := by
            intro ht
            exact htOutside (Finset.mem_union_left {source} ht)
          have htNeSource : labelledVertex G L target ≠ source := by
            intro ht
            exact htOutside (Finset.mem_union_right S (Finset.mem_singleton.mpr ht))
          refine deletionReached_good G C L T hG x hx source ?_ S rfl bits rfl target
            htNotS htNeSource middle middleIndex hmIndex hmLabel hmS hmt
            hRetMiddle
          simp [source, labelledVertex, show 3 + x < 8 by omega])
    have hFilterEq : ((retainedVertexSet G C).filter fun v => v ∈ E).card =
        E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv => hv.2, fun hv => ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    exact hFilter
  unfold ThetaFourCore.xDeletionExpands
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  exact hExpansion.trans hCount

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
