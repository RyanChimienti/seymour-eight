import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.AuxiliaryBridge

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ActualTailBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  EffectiveBridge CommonBridge DefectBridge AuxiliaryBridge
open AuxiliaryCore ActualTail

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 3000000 in
def graphRealAuxArc (C : G.LocalConfiguration) (L : Labels G 3 C)
    (i target : Nat) : Bool :=
  if hi : i < 4 then
    if _ht : target < 18 then
      decide (G.Adj (auxiliaryVertex G C L ⟨i, hi⟩)
        (namedVertex G C L target))
    else false
  else false

@[simp] theorem graphRealAuxArc_eq (C : G.LocalConfiguration) (L : Labels G 3 C)
    (i target : Nat) (hi : i < 4) :
    target < 18 →
    graphRealAuxArc G C L i target =
      decide (G.Adj (auxiliaryVertex G C L ⟨i, hi⟩)
        (namedVertex G C L target)) := by
  intro ht
  simp [graphRealAuxArc, hi, ht]

@[simp] theorem graphRealAuxArc_eighteen (C : G.LocalConfiguration)
    (L : Labels G 3 C) (i : Nat) : graphRealAuxArc G C L i 18 = false := by
  simp [graphRealAuxArc]

set_option maxHeartbeats 3000000 in
theorem combinedAuxArc_eq_real (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i target : Nat) (hi : i < 4) :
    combinedAuxArc (graphAuxArc G C L hMin) (graphRealAuxArc G C L)
      i target = graphRealAuxArc G C L i target := by
  unfold combinedAuxArc
  by_cases hTrim : graphAuxArc G C L hMin i target = true
  · have hAdj := graphAuxArc_true_adj G C L hMin i target hi hTrim
    rw [auxiliaryVertex_eq_named G C L ⟨i, hi⟩] at hAdj
    have ht : target < 18 := by
      by_contra hn
      simp [graphAuxArc, hi, show ¬target < 18 by omega] at hTrim
    rw [graphRealAuxArc_eq G C L i target hi ht]
    simp [hTrim, hAdj]
  · have hTrimFalse := Bool.eq_false_of_not_eq_true hTrim
    simp [hTrimFalse]

set_option maxHeartbeats 3000000 in
theorem actualAuxiliaryOriented_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) :
    actualAuxiliaryOriented (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) = true := by
  simp only [actualAuxiliaryOriented, Bool.and_eq_true, all_eq_true_iff]
  constructor
  · intro i hi source hs
    rw [Bool.not_eq_true']
    by_contra hFalse
    have hBoth : (incomingToAux (graphArc G L) (graphPToZ G L) source i &&
        graphRealAuxArc G C L i source) = true :=
      Bool.eq_true_of_not_eq_false hFalse
    rw [Bool.and_eq_true] at hBoth
    rw [incomingToAux_eq_adj G C L hG source i hs hi] at hBoth
    rw [graphRealAuxArc_eq G C L i source hi (by omega)] at hBoth
    exact hG.2 (of_decide_eq_true hBoth.1) (of_decide_eq_true hBoth.2)
  · intro i hi j hj
    rw [Bool.not_eq_true']
    by_contra hFalse
    have hBoth : (graphRealAuxArc G C L i (14 + j) &&
        graphRealAuxArc G C L j (14 + i)) = true :=
      Bool.eq_true_of_not_eq_false hFalse
    rw [Bool.and_eq_true, graphRealAuxArc_eq G C L i (14 + j) hi (by omega),
      graphRealAuxArc_eq G C L j (14 + i) hj (by omega)] at hBoth
    have hij := of_decide_eq_true hBoth.1
    have hji := of_decide_eq_true hBoth.2
    rw [← auxiliaryVertex_eq_named G C L ⟨j, hj⟩] at hij
    rw [← auxiliaryVertex_eq_named G C L ⟨i, hi⟩] at hji
    exact hG.2 hij hji

set_option maxHeartbeats 3000000 in
def outsideSecondSet (C : G.LocalConfiguration) (L : Labels G 3 C)
    (p : Fin 6) : Finset V :=
  G.secondOutNeighborFinset (L.p p).1 \ namedVertexSet G C

set_option maxHeartbeats 3000000 in
noncomputable def paddedOutsideLabels (W : Finset V) : Fin 7 → Option V := fun i ↦
  if hi : i.val < W.card then
    some ((finsetEquivFin W rfl) ⟨i.val, hi⟩).1
  else none

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_some_mem (W : Finset V) (_hW : W.card ≤ 7)
    (i : Fin 7) (v : V) (hi : paddedOutsideLabels W i = some v) : v ∈ W := by
  classical
  unfold paddedOutsideLabels at hi
  split at hi
  · simp only [Option.some.injEq] at hi
    rw [← hi]
    exact ((finsetEquivFin W rfl) _).2
  · contradiction

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_surjective (W : Finset V) (hW : W.card ≤ 7)
    {v : V} (hv : v ∈ W) :
    ∃ i : Fin 7, paddedOutsideLabels W i = some v := by
  classical
  let j : Fin W.card := (finsetEquivFin W rfl).symm ⟨v, hv⟩
  let i : Fin 7 := ⟨j.val, by omega⟩
  refine ⟨i, ?_⟩
  simp [paddedOutsideLabels, i, j]

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_some_injective (W : Finset V) (_hW : W.card ≤ 7)
    {i j : Fin 7} {v : V}
    (hi : paddedOutsideLabels W i = some v)
    (hj : paddedOutsideLabels W j = some v) : i = j := by
  classical
  unfold paddedOutsideLabels at hi hj
  split at hi
  · split at hj
    · simp only [Option.some.injEq] at hi hj
      apply Fin.ext
      have heq : (⟨i.val, by assumption⟩ : Fin W.card) =
          ⟨j.val, by assumption⟩ := by
        apply (finsetEquivFin W rfl).injective
        apply Subtype.ext
        exact hi.trans hj.symm
      exact congrArg (fun x : Fin W.card ↦ x.val) heq
    · cases hj
  · cases hi

set_option maxHeartbeats 3000000 in
noncomputable def graphOutsideArc (C : G.LocalConfiguration) (L : Labels G 3 C)
    (W : Finset V) (i slot : Nat) : Bool :=
  if hi : i < 4 then
    if hs : slot < 7 then
      match paddedOutsideLabels W ⟨slot, hs⟩ with
      | some v => decide (G.Adj (auxiliaryVertex G C L ⟨i, hi⟩) v)
      | none => false
    else false
  else false

set_option maxHeartbeats 3000000 in
theorem graphOutsideArc_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (W : Finset V) (hW : W.card ≤ 7)
    (i slot : Nat) (hi : i < 4) (hs : slot < 7)
    (hArc : graphOutsideArc G C L W i slot = true) :
    ∃ v ∈ W, paddedOutsideLabels W ⟨slot, hs⟩ = some v ∧
      G.Adj (auxiliaryVertex G C L ⟨i, hi⟩) v := by
  simp only [graphOutsideArc, hi, hs, dite_true] at hArc
  split at hArc
  · rename_i v hv
    exact ⟨v, paddedOutsideLabels_some_mem W hW _ _ hv,
      hv, of_decide_eq_true hArc⟩
  · contradiction

set_option maxHeartbeats 3000000 in
theorem pDirect_eq_adj (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (p target : Nat) (hp : p < 6) (ht : target < 18) :
    pDirect (graphArc G L) (graphPToZ G L) p target =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (namedVertex G C L target)) := by
  simp only [pDirect, ht, if_true]
  have hCore := coreArc_graph G C L hG (8 + p) target (by omega) ht
  simpa [namedVertex, labelledVertex, show ¬8 + p < 8 by omega,
    show 8 + p < 14 by omega] using hCore

set_option maxHeartbeats 3000000 in
theorem actualNamedArc_eq_adj (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (middle target : Nat) (hm : middle < 18)
    (ht : target < 18) :
    actualNamedArc (graphArc G L) (graphPToZ G L) (graphRealAuxArc G C L)
      middle target =
        decide (G.Adj (namedVertex G C L middle) (namedVertex G C L target)) := by
  by_cases hm14 : middle < 14
  · simp only [actualNamedArc, hm14, ht, if_true]
    exact coreArc_graph G C L hG middle target hm14 ht
  · have hi : middle - 14 < 4 := by omega
    simp only [actualNamedArc, hm14, hm, if_false, if_true]
    rw [graphRealAuxArc_eq G C L (middle - 14) target hi ht]
    rw [auxiliaryVertex_eq_named G C L ⟨middle - 14, hi⟩]
    simp [show 14 + (middle - 14) = middle by omega]

set_option maxHeartbeats 3000000 in
theorem actualSecondNamed_true_mem (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (p target : Nat) (hp : p < 6) (ht : target < 19)
    (hSecond : actualSecondNamed (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) p target = true) :
    namedVertex G C L target ∈
      G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1 := by
  simp only [actualSecondNamed, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 18 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  have ht18 : target < 18 := by
    by_contra hn
    have htEq : target = 18 := by omega
    subst target
    simp [actualNamedArc, graphRealAuxArc] at hLast
  rw [pDirect_eq_adj G C L hG p target hp ht18] at hNot
  rw [pDirect_eq_adj G C L hG p middle hp (by omega)] at hFirst
  rw [actualNamedArc_eq_adj G C L hG middle target hm ht18] at hLast
  have hSource : namedVertex G C L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [namedVertex, labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega]
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨namedVertex G C L middle, of_decide_eq_true hFirst,
    of_decide_eq_true hLast⟩, by simpa using hNot, ?_⟩
  intro heq
  apply hne
  have hFin : (⟨target, ht18⟩ : Fin 18) = ⟨8 + p, by omega⟩ := by
    apply (namedLabelEquiv G C L hG).injective
    apply Subtype.ext
    simpa [hSource] using heq
  exact Fin.ext_iff.mp hFin

set_option maxHeartbeats 3000000 in
theorem actualSecondNamed_count_le (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (p : Nat) (hp : p < 6) :
    (count 19 (actualSecondNamed (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) p)).toNat ≤
      ((namedVertexSet G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.p ⟨p, hp⟩).1).card := by
  rw [count_nineteen_eq_eighteen]
  · apply count_le_filterCard (namedVertexSet G C)
      (namedLabelEquiv G C L hG) _ _ (by omega)
    intro target hTarget
    rw [namedLabelEquiv_val G C L hG]
    exact actualSecondNamed_true_mem G C L hG p target hp (by omega) hTarget
  · apply Bool.eq_false_of_not_eq_true
    intro hSecond
    simp only [actualSecondNamed, Bool.and_eq_true] at hSecond
    obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 18 _).mp hSecond.2
    simp only [Bool.and_eq_true] at hPath
    have hLast := hPath.2
    simp [actualNamedArc, graphRealAuxArc] at hLast

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_count (W : Finset V) (hW : W.card ≤ 7)
    (Q : V → Prop) [DecidablePred Q] :
    (count 7 fun i ↦
      if hi : i < 7 then
        match paddedOutsideLabels W ⟨i, hi⟩ with
        | some v => decide (Q v)
        | none => false
      else false).toNat = (W.filter Q).card := by
  classical
  let b : Nat → Bool := fun i ↦
    if hi : i < 7 then
      match paddedOutsideLabels W ⟨i, hi⟩ with
      | some v => decide (Q v)
      | none => false
    else false
  change (count 7 b).toNat = (W.filter Q).card
  rw [toNat_count 7 b (by omega),
    filterCard_eq_sum_fin W (finsetEquivFin W rfl) Q]
  rw [show 7 = W.card + (7 - W.card) by omega, Finset.sum_range_add]
  have hFirst :
      (∑ i ∈ Finset.range W.card, (bitCount (b i)).toNat) =
        ∑ i : Fin W.card, if Q ((finsetEquivFin W rfl) i).1 then 1 else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [b, paddedOutsideLabels, show i.val < 7 by omega]
    split <;> simp_all [bitCount]
  rw [hFirst]
  simp only [add_eq_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hiRange := Finset.mem_range.mp hi
  simp [b, paddedOutsideLabels, bitCount]

set_option maxHeartbeats 3000000 in
theorem p_outgoing_mem_named (C : G.LocalConfiguration) (_L : Labels G 3 C)
    (hG : G.IsOriented)
    {p v : V} (hp : p ∈ C.P) (hpv : G.Adj p v) :
    v ∈ namedVertexSet G C := by
  have hCaptured := BSixKThree.P_outgoingCaptured_general G C hG p hp
    ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
  simp only [Finset.mem_union] at hCaptured
  rcases hCaptured with ((hvH | hvP) | hvQ) | hvExt
  · simp [namedVertexSet, retainedVertexSet,
      Digraph.LocalConfiguration.H_subset_A (G := G) C hvH]
  · simp [namedVertexSet, retainedVertexSet, hvP]
  · simp [namedVertexSet, retainedVertexSet, hvQ]
  · simp [namedVertexSet, retainedVertexSet, hvExt]

set_option maxHeartbeats 3000000 in
theorem outside_path_middle_auxiliary (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) {p middle target : V}
    (hp : p ∈ C.P) (hFirst : G.Adj p middle) (hLast : G.Adj middle target)
    (hOutside : target ∉ namedVertexSet G C) :
    ∃ i : Fin 4, middle = auxiliaryVertex G C L i := by
  have hmRet : middle ∈ retainedVertexSet G C := by
    simpa [namedVertexSet] using p_outgoing_mem_named G C L hG hp hFirst
  simp only [retainedVertexSet, Finset.mem_union] at hmRet
  rcases hmRet with ((hmA | hmP) | hmQ) | hmZ
  · have htCap :=
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG middle hmA
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hLast)
    apply (hOutside ?_).elim
    rcases Finset.mem_union.mp htCap with htA | htB
    · simp [namedVertexSet, retainedVertexSet, htA]
    · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at htB
      rcases Finset.mem_union.mp htB with htP | htQ
      · simp [namedVertexSet, retainedVertexSet, htP]
      · simp [namedVertexSet, retainedVertexSet, htQ]
  · exact (hOutside (p_outgoing_mem_named G C L hG hmP hLast)).elim
  · obtain ⟨j, hj⟩ := L.q.surjective ⟨middle, hmQ⟩
    have hj0 : j = 0 := Subsingleton.elim _ _
    refine ⟨⟨0, by omega⟩, ?_⟩
    simpa [auxiliaryVertex, hj0] using congrArg Subtype.val hj.symm
  · obtain ⟨j, hj⟩ := L.z.surjective ⟨middle, hmZ⟩
    refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
    simpa [auxiliaryVertex, show j.val + 1 ≠ 0 by omega] using
      congrArg Subtype.val hj.symm

set_option maxHeartbeats 3000000 in
def auxPath (C : G.LocalConfiguration) (L : Labels G 3 C)
    (source target : V) : Prop :=
  ∃ i : Fin 4, G.Adj source (auxiliaryVertex G C L i) ∧
    G.Adj (auxiliaryVertex G C L i) target

set_option maxHeartbeats 3000000 in
theorem outside_second_has_auxPath (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (p : Fin 6) {v : V}
    (hv : v ∈ outsideSecondSet G C L p) :
    auxPath G C L (L.p p).1 v := by
  rcases Finset.mem_sdiff.mp hv with ⟨hvSecond, hvOutside⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet] at hvSecond
  rcases hvSecond.1 with ⟨middle, hFirst, hLast⟩
  obtain ⟨i, hi⟩ := outside_path_middle_auxiliary G C L hG
    (L.p p).2 hFirst hLast hvOutside
  subst middle
  exact ⟨i, hFirst, hLast⟩

set_option maxHeartbeats 3000000 in
theorem actualSlotReached_for_some_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (p : Fin 6)
    (W : Finset V) (hW : W = outsideSecondSet G C L p)
    (hWCard : W.card ≤ 7) (slot : Fin 7) {v : V}
    (hSlot : paddedOutsideLabels W slot = some v) :
    actualSlotReached (graphArc G L) (graphPToZ G L)
      (graphOutsideArc G C L W) p.val slot.val = true := by
  have hvW := paddedOutsideLabels_some_mem W hWCard slot v hSlot
  have hvOutside : v ∈ outsideSecondSet G C L p := by simpa [hW] using hvW
  obtain ⟨i, hpi, hiv⟩ := outside_second_has_auxPath G C L hG p hvOutside
  rw [actualSlotReached, any_eq_true_iff]
  refine ⟨i.val, i.isLt, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · rw [pDirect_eq_adj G C L hG p.val (14 + i.val)
      p.isLt (by omega), ← auxiliaryVertex_eq_named G C L i]
    exact decide_eq_true hpi
  · simp only [graphOutsideArc, i.isLt, slot.isLt, dite_true, hSlot]
    exact decide_eq_true hiv

set_option maxHeartbeats 3000000 in
theorem actualSlotReached_true_has_some (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (p : Fin 6)
    (W : Finset V) (hWCard : W.card ≤ 7) (slot : Fin 7)
    (hReached : actualSlotReached (graphArc G L) (graphPToZ G L)
      (graphOutsideArc G C L W) p.val slot.val = true) :
    ∃ v ∈ W, paddedOutsideLabels W slot = some v ∧
      auxPath G C L (L.p p).1 v := by
  rw [actualSlotReached, any_eq_true_iff] at hReached
  obtain ⟨i, hi, hBoth⟩ := hReached
  rw [Bool.and_eq_true] at hBoth
  obtain ⟨v, hvW, hSlot, hiv⟩ :=
    graphOutsideArc_true G C L W hWCard i slot.val hi slot.isLt hBoth.2
  refine ⟨v, hvW, hSlot, ⟨⟨i, hi⟩, ?_, hiv⟩⟩
  rw [pDirect_eq_adj G C L hG p.val (14 + i)
      p.isLt (by omega), ← auxiliaryVertex_eq_named G C L ⟨i, hi⟩] at hBoth
  exact of_decide_eq_true hBoth.1

set_option maxHeartbeats 3000000 in
theorem reachedSlotPrefix_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (p : Fin 6)
    (W : Finset V) (hW : W = outsideSecondSet G C L p)
    (hWCard : W.card ≤ 7) :
    reachedSlotPrefix (graphArc G L) (graphPToZ G L)
      (graphOutsideArc G C L W) p.val = true := by
  rw [reachedSlotPrefix, all_eq_true_iff]
  intro slot hs
  by_cases hNext : actualSlotReached (graphArc G L) (graphPToZ G L)
      (graphOutsideArc G C L W) p.val (slot + 1) = true
  · simp only [hNext, Bool.not_true, Bool.false_or]
    obtain ⟨v, _, hSome, _⟩ := actualSlotReached_true_has_some G C L hG
      p W hWCard ⟨slot + 1, by omega⟩ hNext
    unfold paddedOutsideLabels at hSome
    split at hSome
    · rename_i hNextCard
      change slot + 1 < W.card at hNextCard
      let current : Fin 7 := ⟨slot, by omega⟩
      have hCurrentCard : current.val < W.card := by
        dsimp [current]
        omega
      let w := ((finsetEquivFin W rfl) ⟨current.val, hCurrentCard⟩).1
      have hCurrentSome : paddedOutsideLabels W current = some w := by
        simp [paddedOutsideLabels, current, w, hCurrentCard]
      exact actualSlotReached_for_some_true G C L hG p W hW hWCard
        current hCurrentSome
    · contradiction
  · have hNextFalse := Bool.eq_false_of_not_eq_true hNext
    simp [hNextFalse]

set_option maxHeartbeats 3000000 in
theorem actualSlot_count_le_card (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (p : Fin 6)
    (W : Finset V) (hWCard : W.card ≤ 7) :
    (count 7 (actualSlotReached (graphArc G L) (graphPToZ G L)
      (graphOutsideArc G C L W) p.val)).toNat ≤ W.card := by
  have hPad := paddedOutsideLabels_count W hWCard (fun _ : V ↦ True)
  simp only [Finset.filter_true] at hPad
  rw [← hPad, toNat_count_eq_fin_sum 7 _ (by omega),
    toNat_count_eq_fin_sum 7 _ (by omega)]
  apply Finset.sum_le_sum
  intro slot _
  by_cases hReached : actualSlotReached (graphArc G L) (graphPToZ G L)
      (graphOutsideArc G C L W) p.val slot.val = true
  · obtain ⟨v, _, hSome, _⟩ := actualSlotReached_true_has_some G C L hG
      p W hWCard slot hReached
    simp [hReached, hSome]
  · have hFalse := Bool.eq_false_of_not_eq_true hReached
    simp [hFalse]

set_option maxHeartbeats 3000000 in
theorem actualSecondCount_le_seven_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 6)
    (hDegree : G.outdegree (L.p p).1 = 8)
    (W : Finset V) (hW : W = outsideSecondSet G C L p)
    (hWCard : W.card ≤ 7) :
    (actualSecondCount (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) (graphOutsideArc G C L W) p.val).ule 7 = true := by
  let T := G.secondOutNeighborFinset (L.p p).1
  let localSecond := (namedVertexSet G C).filter fun v ↦ v ∈ T
  have hNamed := actualSecondNamed_count_le G C L hG p.val p.isLt
  have hSlot := actualSlot_count_le_card G C L hG p W hWCard
  have hPartition : localSecond.card + W.card = T.card := by
    have hUnion : localSecond ∪ W = T := by
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, localSecond, T]
      rw [hW]
      simp only [outsideSecondSet, Finset.mem_sdiff]
      tauto
    have hDisjoint : Disjoint localSecond W := by
      rw [Finset.disjoint_left]
      intro v hvLocal hvW'
      have hvNamed := (Finset.mem_filter.mp hvLocal).1
      rw [hW, outsideSecondSet] at hvW'
      exact (Finset.mem_sdiff.mp hvW').2 hvNamed
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion]
  have hSecondLt := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨(L.p p).1, hs⟩)
  change T.card < G.outdegree (L.p p).1 at hSecondLt
  have hNamed' :
      (count 19 (actualSecondNamed (graphArc G L) (graphPToZ G L)
        (graphRealAuxArc G C L) p.val)).toNat ≤ localSecond.card := by
    simpa [localSecond, T] using hNamed
  have hTotalLe :
      (count 19 (actualSecondNamed (graphArc G L) (graphPToZ G L)
        (graphRealAuxArc G C L) p.val)).toNat +
      (count 7 (actualSlotReached (graphArc G L) (graphPToZ G L)
        (graphOutsideArc G C L W) p.val)).toNat ≤ 7 := by
    rw [hDegree] at hSecondLt
    omega
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  unfold actualSecondCount
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (hTotalLe.trans_lt (by norm_num))]
  exact hTotalLe

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem filterCard_le_count {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, Q (e j).1 → b j = true) :
    (S.filter Q).card ≤ (count n b).toNat := by
  classical
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j _
  by_cases hQ : Q (e j).1
  · simp [hQ, hGood j hQ]
  · simp [hQ]

set_option maxHeartbeats 3000000 in
theorem count_toNat_le (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat ≤ n := by
  rw [toNat_count n f hn]
  calc
    _ ≤ ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases f i <;> decide
    _ = n := by simp

set_option maxHeartbeats 3000000 in
omit [Fintype V] [DecidableEq V] in
theorem padded_filterCard_le_count (W : Finset V) (hW : W.card ≤ 7)
    (Q : V → Prop) [DecidablePred Q] (b : Nat → Bool)
    (hGood : ∀ i : Fin 7,
      (match paddedOutsideLabels W i with
        | some v => decide (Q v)
        | none => false) = true → b i = true) :
    (W.filter Q).card ≤ (count 7 b).toNat := by
  classical
  rw [← paddedOutsideLabels_count W hW Q,
    toNat_count_eq_fin_sum 7 _ (by omega),
    toNat_count_eq_fin_sum 7 _ (by omega)]
  apply Finset.sum_le_sum
  intro i _
  let a := match paddedOutsideLabels W i with
    | some v => decide (Q v)
    | none => false
  by_cases ha : a = true
  · have hb := hGood i ha
    simp [a, ha, hb]
  · have haf := Bool.eq_false_of_not_eq_true ha
    simp [a, haf]

set_option maxHeartbeats 3000000 in
theorem deletionReachesNamed_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (p deleted target : Nat) (hp : p < 6) (_hd : deleted < 18)
    (ht : target < 18) (middle : V)
    (hmNamed : middle ∈ namedVertexSet G C)
    (hmNeDeleted : middle ≠ namedVertex G C L deleted)
    (hFirst : G.Adj (L.p ⟨p, hp⟩).1 middle)
    (hLast : G.Adj middle (namedVertex G C L target)) :
    ActualTail.deletionReachesNamed (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) p deleted target = true := by
  obtain ⟨middleIndex, hMiddle⟩ :=
    (namedLabelEquiv G C L hG).surjective ⟨middle, hmNamed⟩
  have hMiddleVal : namedVertex G C L middleIndex.val = middle := by
    simpa using congrArg Subtype.val hMiddle
  rw [ActualTail.deletionReachesNamed, any_eq_true_iff]
  refine ⟨middleIndex.val, middleIndex.isLt, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hmNeSource : middleIndex.val ≠ 8 + p := by
    intro heq
    have hNamedSource : namedVertex G C L (8 + p) = (L.p ⟨p, hp⟩).1 := by
      simp [namedVertex, labelledVertex, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega]
    have hmSource : middle = (L.p ⟨p, hp⟩).1 :=
      hMiddleVal.symm.trans (by simpa [heq] using hNamedSource)
    exact hG.1 _ (hmSource ▸ hFirst)
  have hmNeDeletedIndex : middleIndex.val ≠ deleted := by
    intro heq
    apply hmNeDeleted
    rw [← hMiddleVal, heq]
  have hmNeTarget : middleIndex.val ≠ target := by
    intro heq
    have hmTarget : middle = namedVertex G C L target :=
      hMiddleVal.symm.trans (by rw [heq])
    exact hG.1 _ (hmTarget ▸ hLast)
  refine ⟨⟨⟨⟨hmNeSource, hmNeDeletedIndex⟩, hmNeTarget⟩, ?_⟩, ?_⟩
  · rw [pDirect_eq_adj G C L hG p middleIndex.val hp middleIndex.isLt,
      hMiddleVal]
    exact decide_eq_true hFirst
  · rw [actualNamedArc_eq_adj G C L hG middleIndex.val target
      middleIndex.isLt ht, hMiddleVal]
    exact decide_eq_true hLast

set_option maxHeartbeats 3000000 in
theorem deletionSecondNamed_eighteen (C : G.LocalConfiguration)
    (L : Labels G 3 C) (p deleted : Nat) (hd : deleted < 18) :
    ActualTail.deletionSecondNamed (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) p deleted 18 = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hSecond
  simp only [ActualTail.deletionSecondNamed, Bool.and_eq_true] at hSecond
  have hReach : ActualTail.deletionReachesNamed (graphArc G L)
      (graphPToZ G L) (graphRealAuxArc G C L) p deleted 18 = true := by
    split at hSecond
    · omega
    · simp only [Bool.and_eq_true] at hSecond
      exact hSecond.2.2
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 18 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  have hLast := hPath.2
  simp [ActualTail.actualNamedArc, graphRealAuxArc] at hLast

set_option maxHeartbeats 3000000 in
theorem deletionConditions_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex) (p : Fin 6)
    (hDegree : G.outdegree (L.p p).1 = 8)
    (W : Finset V) (hW : W = outsideSecondSet G C L p)
    (hWCard : W.card ≤ 7) :
    ActualTail.deletionConditions (graphArc G L) (graphPToZ G L)
      (graphRealAuxArc G C L) (graphOutsideArc G C L W) p.val = true := by
  rw [ActualTail.deletionConditions, all_eq_true_iff]
  intro d hd
  let deleted := 1 + d
  change (!pDirect (graphArc G L) (graphPToZ G L) p.val deleted ||
    (7 : BitVec 8).ule (ActualTail.deletionSecondCount (graphArc G L)
      (graphPToZ G L) (graphRealAuxArc G C L) (graphOutsideArc G C L W)
      p.val deleted)) = true
  by_cases hArc : pDirect (graphArc G L) (graphPToZ G L)
      p.val deleted = true
  · simp only [hArc, Bool.not_true, Bool.false_or,
      BitVec.ule_eq_decide, decide_eq_true_eq]
    let source := (L.p p).1
    let deletedVertex := namedVertex G C L deleted
    let S := (G.outNeighborFinset source).erase deletedVertex
    let expansion := G.outNeighborFinsetOf S \ (S ∪ {source})
    have hGraphArc : G.Adj source deletedVertex := by
      rw [pDirect_eq_adj G C L hG p.val deleted p.isLt (by omega)] at hArc
      exact of_decide_eq_true hArc
    have hExpansion : 7 ≤ expansion.card := by
      simpa [source, deletedVertex, S, expansion] using
        Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour hDegree hGraphArc
    have hExpansionCaptured : expansion ⊆ namedVertexSet G C ∪ W := by
      intro v hv
      by_cases hvNamed : v ∈ namedVertexSet G C
      · exact Finset.mem_union_left W hvNamed
      · apply Finset.mem_union_right _
        rw [hW, outsideSecondSet]
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, hvNamed⟩
        rcases Finset.mem_sdiff.mp hv with ⟨hvReach, hvOutsideExpansion⟩
        obtain ⟨middle, hmS, hmv⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
        have hmOut : middle ∈ G.outNeighborFinset source :=
          Finset.mem_of_mem_erase hmS
        have hFirst : G.Adj source middle :=
          (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
        have hvNotDirect : ¬G.Adj source v := by
          intro hsv
          apply hvOutsideExpansion
          apply Finset.mem_union_left {source}
          apply Finset.mem_erase.mpr
          refine ⟨?_, (Digraph.mem_outNeighborFinset (G := G)).mpr hsv⟩
          intro hvDeleted
          apply hvNamed
          rw [hvDeleted]
          dsimp [deletedVertex]
          rw [← namedLabelEquiv_val G C L hG ⟨deleted, by omega⟩]
          exact (namedLabelEquiv G C L hG ⟨deleted, by omega⟩).2
        have hvNeSource : v ≠ source := by
          intro hvs
          apply hvOutsideExpansion
          exact Finset.mem_union_right S (Finset.mem_singleton.mpr hvs)
        rw [Digraph.mem_secondOutNeighborFinset,
          Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨middle, hFirst, hmv⟩, hvNotDirect, hvNeSource⟩
    let localExpansion := (namedVertexSet G C).filter fun v ↦ v ∈ expansion
    let outsideExpansion := W.filter fun v ↦ v ∈ expansion
    have hParts : expansion.card ≤ localExpansion.card + outsideExpansion.card := by
      have hSub : expansion ⊆ localExpansion ∪ outsideExpansion := by
        intro v hv
        rcases Finset.mem_union.mp (hExpansionCaptured hv) with hvNamed | hvW'
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvNamed, hv⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvW', hv⟩)
      have hCard := Finset.card_le_card hSub
      have hDisjoint : Disjoint localExpansion outsideExpansion := by
        rw [Finset.disjoint_left]
        intro v hvLocal hvOutside
        have hvNamed := (Finset.mem_filter.mp hvLocal).1
        have hvW' := (Finset.mem_filter.mp hvOutside).1
        rw [hW, outsideSecondSet] at hvW'
        exact (Finset.mem_sdiff.mp hvW').2 hvNamed
      rw [Finset.card_union_of_disjoint hDisjoint] at hCard
      exact hCard
    have hLocalCount : localExpansion.card ≤
        (count 19 (ActualTail.deletionSecondNamed (graphArc G L)
          (graphPToZ G L) (graphRealAuxArc G C L) p.val deleted)).toNat := by
      rw [count_nineteen_eq_eighteen _
        (deletionSecondNamed_eighteen G C L p.val deleted (by omega))]
      apply filterCard_le_count (namedVertexSet G C)
        (namedLabelEquiv G C L hG)
        (ActualTail.deletionSecondNamed (graphArc G L) (graphPToZ G L)
          (graphRealAuxArc G C L) p.val deleted)
        (fun v ↦ v ∈ expansion) (by omega)
      intro target htExpansion
      rw [namedLabelEquiv_val G C L hG] at htExpansion
      rcases Finset.mem_sdiff.mp htExpansion with ⟨htReach, htOutside⟩
      obtain ⟨middle, hmS, hmt⟩ :=
        (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
      have hmOut : middle ∈ G.outNeighborFinset source :=
        Finset.mem_of_mem_erase hmS
      have hFirst : G.Adj source middle :=
        (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
      have hmNamed := p_outgoing_mem_named G C L hG (L.p p).2 hFirst
      have hmNeDeleted : middle ≠ deletedVertex := (Finset.mem_erase.mp hmS).1
      have hReach := deletionReachesNamed_true G C L hG p.val deleted
        target.val p.isLt (by omega) target.isLt middle hmNamed hmNeDeleted
        hFirst hmt
      have htNeSource : target.val ≠ 8 + p.val := by
        intro heq
        apply htOutside
        apply Finset.mem_union_right S
        apply Finset.mem_singleton.mpr
        dsimp [source]
        have hNamedSource : namedVertex G C L (8 + p.val) = (L.p p).1 := by
          simp [namedVertex, labelledVertex, show ¬8 + p.val < 8 by omega,
            show 8 + p.val < 14 by omega]
        simpa [heq] using hNamedSource
      unfold ActualTail.deletionSecondNamed
      rw [Bool.and_eq_true]
      refine ⟨decide_eq_true htNeSource, ?_⟩
      split
      · exact hReach
      · rename_i htNeDeleted
        rw [Bool.and_eq_true]
        refine ⟨?_, hReach⟩
        by_cases hDirect : pDirect (graphArc G L) (graphPToZ G L)
            p.val target.val = true
        · exfalso
          rw [pDirect_eq_adj G C L hG p.val target.val p.isLt
            target.isLt] at hDirect
          apply htOutside
          apply Finset.mem_union_left {source}
          apply Finset.mem_erase.mpr
          refine ⟨?_, (Digraph.mem_outNeighborFinset (G := G)).mpr
            (of_decide_eq_true hDirect)⟩
          intro hVertices
          apply htNeDeleted
          have hFin : target = ⟨deleted, by omega⟩ := by
            apply (namedLabelEquiv G C L hG).injective
            apply Subtype.ext
            simpa [namedLabelEquiv_val G C L hG, deletedVertex]
              using hVertices
          exact Fin.ext_iff.mp hFin
        · have hDirectFalse := Bool.eq_false_of_not_eq_true hDirect
          simp [hDirectFalse]
    have hOutsideCount : outsideExpansion.card ≤
        (count 7 (ActualTail.deletionSlotReached (graphArc G L)
          (graphPToZ G L) (graphOutsideArc G C L W) p.val deleted)).toNat := by
      apply padded_filterCard_le_count W hWCard (fun v ↦ v ∈ expansion)
        (ActualTail.deletionSlotReached (graphArc G L) (graphPToZ G L)
          (graphOutsideArc G C L W) p.val deleted)
      intro slot hSlotExpansion
      cases hSlot : paddedOutsideLabels W slot with
      | none => simp [hSlot] at hSlotExpansion
      | some v =>
        simp only [hSlot, decide_eq_true_eq] at hSlotExpansion
        rcases Finset.mem_sdiff.mp hSlotExpansion with ⟨hvReach, _⟩
        obtain ⟨middle, hmS, hmv⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
        have hmOut : middle ∈ G.outNeighborFinset source :=
          Finset.mem_of_mem_erase hmS
        have hFirst : G.Adj source middle :=
          (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
        have hvW := paddedOutsideLabels_some_mem W hWCard slot v hSlot
        have hvOutside : v ∉ namedVertexSet G C := by
          rw [hW, outsideSecondSet] at hvW
          exact (Finset.mem_sdiff.mp hvW).2
        obtain ⟨i, hi⟩ := outside_path_middle_auxiliary G C L hG
          (L.p p).2 hFirst hmv hvOutside
        rw [ActualTail.deletionSlotReached, any_eq_true_iff]
        refine ⟨i.val, i.isLt, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        have hiDeleted : 14 + i.val ≠ deleted := by
          intro heq
          have hmNeDeleted := (Finset.mem_erase.mp hmS).1
          apply hmNeDeleted
          rw [hi, auxiliaryVertex_eq_named G C L i, heq]
        refine ⟨⟨hiDeleted, ?_⟩, ?_⟩
        · rw [pDirect_eq_adj G C L hG p.val (14 + i.val)
            p.isLt (by omega), ← auxiliaryVertex_eq_named G C L i]
          simpa [hi] using hFirst
        · simp only [graphOutsideArc, i.isLt, slot.isLt, dite_true, hSlot]
          simpa [hi] using decide_eq_true hmv
    change 7 ≤ (ActualTail.deletionSecondCount (graphArc G L)
      (graphPToZ G L) (graphRealAuxArc G C L) (graphOutsideArc G C L W)
      p.val deleted).toNat
    unfold ActualTail.deletionSecondCount
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have hLocalBound := count_toNat_le 19
        (ActualTail.deletionSecondNamed (graphArc G L) (graphPToZ G L)
          (graphRealAuxArc G C L) p.val deleted) (by omega)
      have hOutsideBound := count_toNat_le 7
        (ActualTail.deletionSlotReached (graphArc G L) (graphPToZ G L)
          (graphOutsideArc G C L W) p.val deleted) (by omega)
      omega)]
    omega
  · have hFalse := Bool.eq_false_of_not_eq_true hArc
    simp [hFalse]

set_option maxHeartbeats 3000000 in
theorem outsideSecondSet_card_le_seven (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 6) (hDegree : G.outdegree (L.p p).1 = 8) :
    (outsideSecondSet G C L p).card ≤ 7 := by
  have hSubset : outsideSecondSet G C L p ⊆
      G.secondOutNeighborFinset (L.p p).1 := Finset.sdiff_subset
  have hCard := Finset.card_le_card hSubset
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs ↦ hNoSeymour ⟨(L.p p).1, hs⟩)
  change (G.secondOutNeighborFinset (L.p p).1).card <
    G.outdegree (L.p p).1 at hStrict
  rw [hDegree] at hStrict
  omega

set_option maxHeartbeats 3000000 in
theorem pDegree_eight_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (p : Fin 6) (hDegree : G.outdegree (L.p p).1 = 8) :
    (pDegree 1 3 (graphArc G L) (graphPToZ G L) p.val == 8) = true := by
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have hPDegree := pDegree_toNat G C L hG hHCard hy (Or.inr rfl)
    (by omega) p.val p.isLt
  have hPDegree' :
      (pDegree 1 3 (graphArc G L) (graphPToZ G L) p.val).toNat =
        directCount G C.P (L.p p).1 + directCount G C.H (L.p p).1 +
          directCount G (externalTargets G C) (L.p p).1 +
            (if G.Adj (L.p p).1 (L.q 0).1 then 1 else 0) := by
    simpa using hPDegree
  have hQ := qSingleton G C L
  have hCaptured :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG (L.p p).1 (L.p p).2
  have hDis : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
  rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hDis] at hCaptured
  have hQDirect : directCount G {(L.q 0).1} (L.p p).1 =
      if G.Adj (L.p p).1 (L.q 0).1 then 1 else 0 := by
    by_cases hAdj : G.Adj (L.p p).1 (L.q 0).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  rw [hQDirect] at hCaptured
  have hNat : directCount G C.P (L.p p).1 + directCount G C.H (L.p p).1 +
      directCount G (externalTargets G C) (L.p p).1 +
        (if G.Adj (L.p p).1 (L.q 0).1 then 1 else 0) = 8 := by
    rw [hDegree] at hCaptured
    omega
  rw [hPDegree', hNat]
  decide

set_option maxHeartbeats 3000000 in
theorem combinedAuxArc_eq_real_fun (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    combinedAuxArc (graphAuxArc G C L hMin) (graphRealAuxArc G C L) =
      graphRealAuxArc G C L := by
  funext i target
  by_cases hi : i < 4
  · exact combinedAuxArc_eq_real G C L hMin i target hi
  · simp [combinedAuxArc, graphAuxArc, graphRealAuxArc, hi]

set_option maxHeartbeats 3000000 in
theorem actualTailCore_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1) (p : Fin 6)
    (hDegree : G.outdegree (L.p p).1 = 8) :
    ActualTail.actualTailCore p.val (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) (graphRealAuxArc G C L)
      (graphOutsideArc G C L (outsideSecondSet G C L p)) = true := by
  let W := outsideSecondSet G C L p
  have hWCard : W.card ≤ 7 := by
    exact outsideSecondSet_card_le_seven G C L hNoSeymour p hDegree
  have hCanonical :=
    canonicalAuxiliaryCore_true G C L hG hMin hNoSeymour
  have hPDegree := pDegree_eight_true G C L hG hHCard hy p hDegree
  have hActualOriented := actualAuxiliaryOriented_true G C L hG
  have hPrefix := reachedSlotPrefix_true G C L hG p W rfl hWCard
  have hSecond := actualSecondCount_le_seven_true G C L hG hNoSeymour
    p hDegree W rfl hWCard
  have hDeletion := deletionConditions_true G hBound C L hG hNoSeymour
    p hDegree W rfl hWCard
  have hCombined := combinedAuxArc_eq_real_fun G C L hMin
  unfold ActualTail.actualTailCore
  rw [hCombined]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hCanonical, hPDegree⟩, hActualOriented⟩, hPrefix⟩,
    hSecond⟩, hDeletion⟩

set_option maxHeartbeats 3000000 in
theorem capacityDefect_degreeSum (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    ∑ p ∈ C.P, G.outdegree p =
      54 - (capacityDefect (graphArc G L) (graphPToZ G L)).toNat := by
  have hCapacity := defectCapacity_le_six G C L hG hMin hHCard hy
    hACond hDual
  have hAlpha := alpha_toNat G C L hG hHCard hACond hDual
  have hDelta := aMissing_toNat_le_four G C L hG hACond
  have hPToHCapacity := two_aMissing_add_PToH_le_fifteen G C L hG hHCard
    hACond hDual
  have hBeta := internalMissing_toNat G C L hG
  have hM := externalMissing_toNat G C L hG hHCard 1 hy
    (Or.inr rfl) (by omega)
  have hQ := qSingleton G C L
  have hAuxRaw := auxiliarySet_eq G C L 1 hy (Or.inr rfl)
  have hAux : auxiliarySet G C = C.Q ∪ (externalTargets G C) := by simpa [hQ] using hAuxRaw
  have hAccount := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hDis : Disjoint C.Q (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ) hvZ
  rw [hAux, edgeCount_union_of_disjoint G C.P C.Q (externalTargets G C) hDis] at hM
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hQCard : C.Q.card = 1 := by
    simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = 3 := by
    simpa using (Fintype.card_congr L.z).symm
  have hAuxCap := edgeCount_le_card_mul_card G C.P (C.Q ∪ (externalTargets G C))
  rw [hPCard, Finset.card_union_of_disjoint hDis, hQCard, hZCard,
    edgeCount_union_of_disjoint G C.P C.Q (externalTargets G C) hDis] at hAuxCap
  have hPPcap := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hPPcap
  norm_num [Nat.choose] at hPPcap
  have hAlphaEq : (alpha 1 (graphArc G L)).toNat +
      2 * (aMissing (graphArc G L)).toNat + edgeCount G C.P C.H = 15 := by
    omega
  have hBetaEq : (internalMissing (graphArc G L)).toNat +
      edgeCount G C.P C.P = 15 := by omega
  have hMEq :
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) = 24 := by omega
  have hAlphaLe : (alpha 1 (graphArc G L)).toNat ≤ 15 := by omega
  have hBetaLe : (internalMissing (graphArc G L)).toNat ≤ 15 := by omega
  have hD : (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat =
      (alpha 1 (graphArc G L)).toNat +
        (internalMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hTwice : (2 * aMissing (graphArc G L)).toNat =
      2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_mul, hTwo, Nat.mod_eq_of_lt (by omega)]
  have hFirst : (externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
      2 * aMissing (graphArc G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_add, hTwice, Nat.mod_eq_of_lt (by omega)]
  have hTotal : (capacityDefect (graphArc G L) (graphPToZ G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat +
          (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat := by
    unfold capacityDefect
    rw [BitVec.toNat_add, hFirst, Nat.mod_eq_of_lt (by omega)]
  rw [hD] at hTotal
  omega

set_option maxHeartbeats 3000000 in
theorem internalDefect_toNat_eq_add (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat =
      (alpha 1 (graphArc G L)).toNat +
        (internalMissing (graphArc G L)).toNat := by
  have hAlpha := alpha_toNat G C L hG hHCard hACond hDual
  have hBeta := internalMissing_toNat G C L hG
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 3000000 in
theorem externalMissing_le_capacityDefect (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat ≤
      (capacityDefect (graphArc G L) (graphPToZ G L)).toNat := by
  have hCapacity := defectCapacity_le_six G C L hG hMin hHCard hy
    hACond hDual
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hTwice : (2 * aMissing (graphArc G L)).toNat =
      2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_mul, hTwo, Nat.mod_eq_of_lt (by omega)]
  have hFirst : (externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
      2 * aMissing (graphArc G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_add, hTwice, Nat.mod_eq_of_lt (by omega)]
  have hTotal : (capacityDefect (graphArc G L) (graphPToZ G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat +
          (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat := by
    unfold capacityDefect
    rw [BitVec.toNat_add, hFirst, Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxHeartbeats 3000000 in
theorem capacityDefect_toNat_eq_components (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true) :
    (capacityDefect (graphArc G L) (graphPToZ G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat +
          (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat := by
  have hCapacity := defectCapacity_le_six G C L hG hMin hHCard hy
    hACond hDual
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hTwice : (2 * aMissing (graphArc G L)).toNat =
      2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_mul, hTwo, Nat.mod_eq_of_lt (by omega)]
  have hFirst : (externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
      2 * aMissing (graphArc G L)).toNat =
      (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
        2 * (aMissing (graphArc G L)).toNat := by
    rw [BitVec.toNat_add, hTwice, Nat.mod_eq_of_lt (by omega)]
  unfold capacityDefect
  rw [BitVec.toNat_add, hFirst, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 3000000 in
theorem pInvariant_degree_bounds (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hAOneCard : C.A1.card = 3)
    (hXCard : C.X.card = 4) (p : Fin 6) :
    G.outdegree (L.p p).1 * 65536 ≤
        pInvariantKey G C (L.q 0).1 (L.p p).1 ∧
      pInvariantKey G C (L.q 0).1 (L.p p).1 <
        G.outdegree (L.p p).1 * 65536 + 65536 := by
  have hQ := qSingleton G C L
  have hCaptured :=
    SeymourEight.BSevenKTwo.RSix.XTwoRoot.GraphBridge.P_outdegree_eq_blocks
      G C (L.q 0).1 (L.q 0).2 hQ hG (L.p p).1 (L.p p).2
  have hDis : Disjoint ({(L.q 0).1} : Finset V) (externalTargets G C) := by
    rw [Finset.disjoint_left]
    intro v hvQ hvZ
    have hv : v = (L.q 0).1 := Finset.mem_singleton.mp hvQ
    subst v
    exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C (L.q 0).2) hvZ
  rw [directCount_union_of_disjoint G {(L.q 0).1} (externalTargets G C) _ hDis] at hCaptured
  have hQDirect : directCount G {(L.q 0).1} (L.p p).1 =
      if G.Adj (L.p p).1 (L.q 0).1 then 1 else 0 := by
    by_cases hAdj : G.Adj (L.p p).1 (L.q 0).1 <;>
      simp [directCount, CertificateBridge.internalFirstNeighbors,
        Finset.filter_singleton, hAdj]
  rw [hQDirect] at hCaptured
  have hHead : directCount G C.P (L.p p).1 + directCount G C.H (L.p p).1 +
      directCount G (externalTargets G C) (L.p p).1 +
        (if G.Adj (L.p p).1 (L.q 0).1 then 1 else 0) =
      G.outdegree (L.p p).1 := by omega
  have hPLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p p).1) C.P)
  have hZLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p p).1) (externalTargets G C))
  have hAOneLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p p).1) C.A1)
  have hXLe := Finset.card_le_card
    (Finset.filter_subset (G.Adj (L.p p).1) C.X)
  have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = 3 := by simpa using (Fintype.card_congr L.z).symm
  change directCount G C.P (L.p p).1 ≤ C.P.card at hPLe
  change directCount G (externalTargets G C) (L.p p).1 ≤ (externalTargets G C).card at hZLe
  change directCount G C.A1 (L.p p).1 ≤ C.A1.card at hAOneLe
  change directCount G C.X (L.p p).1 ≤ C.X.card at hXLe
  rw [hPCard] at hPLe
  rw [hZCard] at hZLe
  rw [hAOneCard] at hAOneLe
  rw [hXCard] at hXLe
  unfold pInvariantKey
  rw [hHead]
  split <;> omega

set_option maxHeartbeats 3000000 in
theorem pDegrees_antitone (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hAOneCard : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hOrder : ∀ q : Fin 5,
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1) :
    ∀ q : Fin 5, G.outdegree (L.p ⟨q.val + 1, by omega⟩).1 ≤
      G.outdegree (L.p ⟨q.val, by omega⟩).1 := by
  intro q
  have hNext := pInvariant_degree_bounds G C L hG hAOneCard hXCard
    ⟨q.val + 1, by omega⟩
  have hPrev := pInvariant_degree_bounds G C L hG hAOneCard hXCard
    ⟨q.val, by omega⟩
  have hKey := hOrder q
  omega

set_option maxHeartbeats 3000000 in
theorem selectedP_degree_eight (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hAOneCard : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hACond : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hOrder : ∀ q : Fin 5,
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1)
    (capacity : Nat) (hCapacityPositive : 1 ≤ capacity)
    (hCapacityLe : capacity ≤ 6)
    (hCapacity :
      (capacityDefect (graphArc G L) (graphPToZ G L)).toNat = capacity) :
    G.outdegree (L.p ⟨6 - capacity, by omega⟩).1 = 8 := by
  classical
  have hSum := capacityDefect_degreeSum G C L hG hMin hHCard hy
    hACond hDual
  rw [hCapacity] at hSum
  have hLabelSum : (∑ i : Fin 6, G.outdegree (L.p i).1) =
      ∑ v ∈ C.P, G.outdegree v := by
    calc
      _ = ∑ v : {v : V // v ∈ C.P}, G.outdegree v.1 := by
        exact Equiv.sum_comp L.p (fun v : {v : V // v ∈ C.P} ↦
          G.outdegree v.1)
      _ = ∑ v ∈ C.P, G.outdegree v := by
        rw [show (Finset.univ : Finset {v : V // v ∈ C.P}) = C.P.attach by
          exact Finset.univ_eq_attach C.P]
        exact C.P.sum_attach G.outdegree
  have hSumFin : (∑ i : Fin 6, G.outdegree (L.p i).1) = 54 - capacity := by
    rw [hLabelSum]
    exact hSum
  have hAnti := pDegrees_antitone G C L hG hAOneCard hXCard hOrder
  let d0 := G.outdegree (L.p ⟨0, by omega⟩).1
  let d1 := G.outdegree (L.p ⟨1, by omega⟩).1
  let d2 := G.outdegree (L.p ⟨2, by omega⟩).1
  let d3 := G.outdegree (L.p ⟨3, by omega⟩).1
  let d4 := G.outdegree (L.p ⟨4, by omega⟩).1
  let d5 := G.outdegree (L.p ⟨5, by omega⟩).1
  have h01 : d1 ≤ d0 := by simpa [d0, d1] using hAnti ⟨0, by omega⟩
  have h12 : d2 ≤ d1 := by simpa [d1, d2] using hAnti ⟨1, by omega⟩
  have h23 : d3 ≤ d2 := by simpa [d2, d3] using hAnti ⟨2, by omega⟩
  have h34 : d4 ≤ d3 := by simpa [d3, d4] using hAnti ⟨3, by omega⟩
  have h45 : d5 ≤ d4 := by simpa [d4, d5] using hAnti ⟨4, by omega⟩
  have h0 : 8 ≤ d0 := by exact hMin _
  have h1 : 8 ≤ d1 := by exact hMin _
  have h2 : 8 ≤ d2 := by exact hMin _
  have h3 : 8 ≤ d3 := by exact hMin _
  have h4 : 8 ≤ d4 := by exact hMin _
  have h5 : 8 ≤ d5 := by exact hMin _
  have hSumExplicit : d0 + d1 + d2 + d3 + d4 + d5 = 54 - capacity := by
    simp only [Fin.sum_univ_succ] at hSumFin
    change d0 + (d1 + (d2 + (d3 + (d4 + d5)))) = 54 - capacity at hSumFin
    omega
  interval_cases capacity
  · change d5 = 8
    omega
  · change d4 = 8
    omega
  · change d3 = 8
    omega
  · change d2 = 8
    omega
  · change d1 = 8
    omega
  · change d0 = 8
    omega

set_option maxHeartbeats 3000000 in
theorem commonCore_aConditions_true (L : Labels G 3 C)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true) :
    aConditions (graphArc G L) = true := by
  simp only [commonCore, Bool.and_eq_true] at hCommon
  tauto

set_option maxHeartbeats 3000000 in
theorem commonCore_degreeAndDual_true (L : Labels G 3 C)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true) :
    degreeAndDualConditions 1 (graphArc G L) = true := by
  simp only [commonCore, Bool.and_eq_true] at hCommon
  tauto

set_option maxHeartbeats 3000000 in
theorem zeroCapacityLeaf_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true)
    (hCapacity :
      (capacityDefect (graphArc G L) (graphPToZ G L)).toNat = 0) :
    zeroCapacityLeaf (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  have hCanonical :=
    canonicalAuxiliaryCore_true G C L hG hMin hNoSeymour
  have hCapacityBV : capacityDefect (graphArc G L) (graphPToZ G L) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hCapacity
  simp [zeroCapacityLeaf, hCommon, hCanonical, hCapacityBV]

set_option maxHeartbeats 3000000 in
theorem actualCapacityLeaf_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1) (hAOneCard : C.A1.card = 3)
    (hXCard : C.X.card = 4)
    (hOrder : ∀ q : Fin 5,
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true)
    (capacity : Nat) (hCapacityPositive : 1 ≤ capacity)
    (hCapacityLe : capacity ≤ 6)
    (hCapacity :
      (capacityDefect (graphArc G L) (graphPToZ G L)).toNat = capacity) :
    actualCapacityLeaf capacity (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) (graphRealAuxArc G C L)
      (graphOutsideArc G C L
        (outsideSecondSet G C L ⟨6 - capacity, by omega⟩)) = true := by
  have hACond := commonCore_aConditions_true G L hCommon
  have hDual := commonCore_degreeAndDual_true G L hCommon
  let p : Fin 6 := ⟨6 - capacity, by omega⟩
  have hDegree := selectedP_degree_eight G C L hG hMin hHCard hy
    hAOneCard hXCard hACond hDual hOrder capacity hCapacityPositive
      hCapacityLe hCapacity
  have hTail := actualTailCore_true G hBound C L hG hMin hNoSeymour
    hHCard hy p hDegree
  have hCapacityBV : capacityDefect (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 capacity := by
    apply BitVec.eq_of_toNat_eq
    rw [hCapacity]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  unfold actualCapacityLeaf
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hCommon, hCapacityBV⟩, by simpa [p] using hTail⟩

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ActualTailBridge
