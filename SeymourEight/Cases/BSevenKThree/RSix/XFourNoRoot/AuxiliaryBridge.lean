import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.DefectBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Canonical
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ActualTailDefs
import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  EffectiveBridge CommonBridge DefectBridge
open AuxiliaryCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
def auxiliaryVertex (C : G.LocalConfiguration) (L : Labels G 3 C)
    (i : Fin 4) : V :=
  if hi : i.val = 0 then (L.q 0).1 else (L.z ⟨i.val - 1, by omega⟩).1

set_option maxHeartbeats 2000000 in
noncomputable def auxiliaryTrim (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 4) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq
    (s := G.outNeighborFinset (auxiliaryVertex G C L i))
      (by simpa [Digraph.outdegree] using hMin (auxiliaryVertex G C L i)))

set_option maxHeartbeats 2000000 in
theorem auxiliaryTrim_subset (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 4) :
    auxiliaryTrim G C L hMin i ⊆
      G.outNeighborFinset (auxiliaryVertex G C L i) :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := G.outNeighborFinset (auxiliaryVertex G C L i))
      (by simpa [Digraph.outdegree] using hMin (auxiliaryVertex G C L i)))).1

set_option maxHeartbeats 2000000 in
theorem auxiliaryTrim_card (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 4) :
    (auxiliaryTrim G C L hMin i).card = 8 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := G.outNeighborFinset (auxiliaryVertex G C L i))
      (by simpa [Digraph.outdegree] using hMin (auxiliaryVertex G C L i)))).2

set_option maxHeartbeats 2000000 in
def namedVertex (C : G.LocalConfiguration) (L : Labels G 3 C)
    (target : Nat) : V := labelledVertex G L target

set_option maxHeartbeats 2000000 in
/-- The graph interpretation uses the eighteen retained vertices.  Certificate
slot 18 is kept syntactically for compatibility but is forced inactive below;
strict second neighbors outside this set use the complete padded slots. -/
def namedVertexSet (C : G.LocalConfiguration) : Finset V :=
  retainedVertexSet G C

set_option maxHeartbeats 2000000 in
noncomputable def namedLabelEquiv (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) :
    Fin 18 ≃ {v : V // v ∈ namedVertexSet G C} := by
  simpa [namedVertexSet] using retainedLabelEquiv G C L hG

@[simp] theorem namedLabelEquiv_val (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (i : Fin 18) :
    (namedLabelEquiv G C L hG i).1 = namedVertex G C L i := by
  exact retainedLabelEquiv_val G C L hG i

set_option maxHeartbeats 2000000 in
noncomputable def graphAuxArc (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i target : Nat) : Bool :=
  if hi : i < 4 then
    if _ht : target < 18 then
      decide (namedVertex G C L target ∈ auxiliaryTrim G C L hMin ⟨i, hi⟩)
    else false
  else false

@[simp] theorem graphAuxArc_eq (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i target : Nat) (hi : i < 4) :
    target < 18 →
    graphAuxArc G C L hMin i target =
      decide (namedVertex G C L target ∈ auxiliaryTrim G C L hMin ⟨i, hi⟩) := by
  intro ht
  simp [graphAuxArc, hi, ht]

@[simp] theorem graphAuxArc_eighteen (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Nat) :
    graphAuxArc G C L hMin i 18 = false := by
  simp [graphAuxArc]

set_option maxHeartbeats 2000000 in
theorem count_nineteen_eq_eighteen (b : Nat → Bool) (hLast : b 18 = false) :
    count 19 b = count 18 b := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_count 19 b (by omega), toNat_count 18 b (by omega),
    Finset.sum_range_succ]
  simp [hLast, bitCount]

set_option maxHeartbeats 2000000 in
noncomputable def graphSignature (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (mask : Nat) : BitVec 4 :=
  canonicalSignature (graphAuxArc G C L hMin) mask

set_option maxHeartbeats 2000000 in
theorem auxNamedOut_toNat (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 4) :
    (auxNamedOut (graphAuxArc G C L hMin) i).toNat =
      ((namedVertexSet G C).filter fun v =>
        v ∈ auxiliaryTrim G C L hMin i).card := by
  rw [auxNamedOut, count_nineteen_eq_eighteen _ (graphAuxArc_eighteen G C L hMin i),
    toNat_count_eq_fin_sum 18 _ (by omega),
    filterCard_eq_sum_fin (namedVertexSet G C) (namedLabelEquiv G C L hG)]
  apply Finset.sum_congr rfl
  intro target _
  rw [graphAuxArc_eq G C L hMin i target i.isLt target.isLt,
    namedLabelEquiv_val G C L hG]
  by_cases hmem : namedVertex G C L target ∈
      auxiliaryTrim G C L hMin i <;> simp [hmem]

set_option maxHeartbeats 2000000 in
theorem auxNamedOut_le_eight_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    (all 4 fun i => (auxNamedOut (graphAuxArc G C L hMin) i).ule 8) = true := by
  rw [all_eq_true_iff]
  intro i hi
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [auxNamedOut_toNat G C L hG hMin ⟨i, hi⟩]
  calc
    _ ≤ (auxiliaryTrim G C L hMin ⟨i, hi⟩).card :=
      Finset.card_le_card (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2)
    _ = 8 := auxiliaryTrim_card G C L hMin ⟨i, hi⟩

set_option maxHeartbeats 2000000 in
theorem auxiliaryExact_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    auxiliaryExact (graphAuxArc G C L hMin) (graphSignature G C L hMin) = true := by
  exact auxiliaryExact_canonical _
    (auxNamedOut_le_eight_true G C L hG hMin)

@[simp] theorem auxiliaryVertex_eq_named (C : G.LocalConfiguration)
    (L : Labels G 3 C) (i : Fin 4) :
    auxiliaryVertex G C L i = namedVertex G C L (14 + i.val) := by
  fin_cases i <;> simp [auxiliaryVertex, namedVertex, labelledVertex]

set_option maxHeartbeats 2000000 in
theorem graphAuxArc_true_adj (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i target : Nat)
    (hi : i < 4) (hArc : graphAuxArc G C L hMin i target = true) :
    G.Adj (auxiliaryVertex G C L ⟨i, hi⟩) (namedVertex G C L target) := by
  have ht : target < 18 := by
    by_contra hn
    simp [graphAuxArc, hi, show ¬target < 18 by omega] at hArc
  rw [graphAuxArc_eq G C L hMin i target hi ht] at hArc
  have hMem := auxiliaryTrim_subset G C L hMin ⟨i, hi⟩
    (of_decide_eq_true hArc)
  exact (Digraph.mem_outNeighborFinset (G := G)).mp hMem

set_option maxHeartbeats 2000000 in
theorem incomingToAux_eq_adj (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (source i : Nat) (hs : source < 14) (hi : i < 4) :
    incomingToAux (graphArc G L) (graphPToZ G L) source i =
      decide (G.Adj (namedVertex G C L source)
        (auxiliaryVertex G C L ⟨i, hi⟩)) := by
  by_cases hsA : source < 8
  · by_cases hi0 : i = 0
    · subst i
      simp [incomingToAux, hsA, namedVertex, labelledVertex, auxiliaryVertex,
        aToQ_graph G L source hsA]
    · have hn : ¬G.Adj (namedVertex G C L source)
          (auxiliaryVertex G C L ⟨i, hi⟩) := by
        intro hAdj
        have hZ : auxiliaryVertex G C L ⟨i, hi⟩ ∈ (externalTargets G C) := by
          simp [auxiliaryVertex, hi0]
        exact GraphFacts.A_not_adj_external G C hG _ _
          (by simp [namedVertex, labelledVertex, hsA]) hZ hAdj
      have hn' : ¬G.Adj (namedVertex G C L source)
          (namedVertex G C L (14 + i)) := by
        simpa using hn
      simp [incomingToAux, hsA, hi0, hn']
  · have hsP : source < 14 := hs
    by_cases hi0 : i = 0
    · subst i
      simp [incomingToAux, hsA, hsP, namedVertex, labelledVertex,
        auxiliaryVertex, pToQ_graph G L (source - 8) (by omega)]
    · have hiz : i - 1 < 3 := by omega
      simp [incomingToAux, hsA, hsP, hi0, namedVertex, labelledVertex,
        auxiliaryVertex, pToZ_graph G L (source - 8) (i - 1)
          (by omega) hiz]

set_option maxHeartbeats 2000000 in
theorem auxiliaryOriented_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    auxiliaryOriented (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  simp only [auxiliaryOriented, Bool.and_eq_true, all_eq_true_iff]
  constructor
  · intro i hi source hs
    rw [Bool.not_eq_true']
    by_contra hFalse
    have hBoth : (incomingToAux (graphArc G L) (graphPToZ G L) source i &&
        graphAuxArc G C L hMin i source) = true :=
      Bool.eq_true_of_not_eq_false hFalse
    rw [Bool.and_eq_true] at hBoth
    have hIn := hBoth.1
    have hOut := hBoth.2
    rw [incomingToAux_eq_adj G C L hG source i hs hi] at hIn
    exact hG.2 (of_decide_eq_true hIn)
      (graphAuxArc_true_adj G C L hMin i source hi hOut)
  · intro i hi j hj
    rw [Bool.not_eq_true']
    by_contra hFalse
    have hBoth : (graphAuxArc G C L hMin i (14 + j) &&
        graphAuxArc G C L hMin j (14 + i)) = true :=
      Bool.eq_true_of_not_eq_false hFalse
    rw [Bool.and_eq_true] at hBoth
    have hij := hBoth.1
    have hji := hBoth.2
    have hij' := graphAuxArc_true_adj G C L hMin i (14 + j) hi hij
    have hji' := graphAuxArc_true_adj G C L hMin j (14 + i) hj hji
    rw [← auxiliaryVertex_eq_named G C L ⟨j, hj⟩] at hij'
    rw [← auxiliaryVertex_eq_named G C L ⟨i, hi⟩] at hji'
    exact hG.2 hij' hji'

set_option maxHeartbeats 2000000 in
noncomputable def trimOutside (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 4) : Finset V :=
  auxiliaryTrim G C L hMin i \ namedVertexSet G C

set_option maxHeartbeats 2000000 in
theorem canonicalOutsideNeed_toNat (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 4) :
    (canonicalOutsideNeed (graphAuxArc G C L hMin) i).toNat =
      (trimOutside G C L hMin i).card := by
  have hEight : ((8 : BitVec 8).toNat) = 8 := by decide
  rw [canonicalOutsideNeed, BitVec.toNat_sub_of_le]
  · rw [auxNamedOut_toNat G C L hG hMin]
    rw [hEight]
    rw [← auxiliaryTrim_card G C L hMin i]
    unfold trimOutside
    rw [Finset.card_sdiff]
    have hEq : namedVertexSet G C ∩ auxiliaryTrim G C L hMin i =
        (namedVertexSet G C).filter fun v ↦
          v ∈ auxiliaryTrim G C L hMin i := by
      ext v
      simp [and_comm]
    rw [hEq]
  · rw [BitVec.le_def]
    rw [hEight]
    rw [auxNamedOut_toNat G C L hG hMin]
    calc
      _ ≤ (auxiliaryTrim G C L hMin i).card :=
        Finset.card_le_card (by
          intro v hv
          exact (Finset.mem_filter.mp hv).2)
      _ = 8 := auxiliaryTrim_card G C L hMin i

set_option maxHeartbeats 2000000 in
theorem sourceDirect_eq_adj (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (source target : Nat)
    (hs : source < 14) (ht : target < 18) :
    sourceDirect (graphArc G L) (graphPToZ G L) source target =
      decide (G.Adj (namedVertex G C L source) (namedVertex G C L target)) := by
  simp only [sourceDirect, ht, if_true]
  exact coreArc_graph G C L hG source target hs ht

set_option maxHeartbeats 2000000 in
theorem namedArc_true_adj (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (middle target : Nat) (hm : middle < 18) (_ht : target < 19)
    (hArc : namedArc (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) middle target = true) :
    G.Adj (namedVertex G C L middle) (namedVertex G C L target) := by
  by_cases hm14 : middle < 14
  · have ht18 : target < 18 := by
      by_contra hn
      simp [namedArc, hm14, show ¬target < 18 by omega] at hArc
    simp only [namedArc, hm14, ht18, if_true] at hArc
    rw [coreArc_graph G C L hG middle target hm14 ht18] at hArc
    simpa [namedVertex] using of_decide_eq_true hArc
  · have hi : middle - 14 < 4 := by omega
    simp only [namedArc, hm14, hm, if_false, if_true] at hArc
    have hAdj := graphAuxArc_true_adj G C L hMin (middle - 14) target hi hArc
    rw [auxiliaryVertex_eq_named G C L ⟨middle - 14, hi⟩] at hAdj
    simpa [show 14 + (middle - 14) = middle by omega] using hAdj

set_option maxHeartbeats 2000000 in
theorem fullSecondNamed_true_mem (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source target : Nat) (hs : source < 8) (ht : target < 19)
    (hSecond : fullSecondNamed (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source target = true) :
    namedVertex G C L target ∈
      G.secondOutNeighborFinset (namedVertex G C L source) := by
  simp only [fullSecondNamed, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotDirect⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 18 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  have ht18 : target < 18 := by
    by_contra hn
    have htEq : target = 18 := by omega
    subst target
    simp [namedArc, graphAuxArc] at hLast
  rw [sourceDirect_eq_adj G C L hG source middle (by omega) hm] at hFirst
  have hNot : ¬G.Adj (namedVertex G C L source) (namedVertex G C L target) := by
    rw [sourceDirect_eq_adj G C L hG source target (by omega) ht18]
      at hNotDirect
    simpa using hNotDirect
  have hLast' := namedArc_true_adj G C L hG hMin middle target hm ht hLast
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨namedVertex G C L middle, of_decide_eq_true hFirst, hLast'⟩, ?_, ?_⟩
  · exact hNot
  · intro hEq
    apply hne
    have hFin : (⟨target, ht18⟩ : Fin 18) = ⟨source, by omega⟩ := by
      apply (namedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa using hEq
    exact Fin.ext_iff.mp hFin

set_option maxHeartbeats 2000000 in
theorem fullSecondNamed_count_le (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 8) :
    (count 19 (fullSecondNamed (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source)).toNat ≤
      ((namedVertexSet G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (namedVertex G C L source)).card := by
  rw [count_nineteen_eq_eighteen]
  · apply count_le_filterCard (namedVertexSet G C)
      (namedLabelEquiv G C L hG) _ _ (by omega)
    intro target hTarget
    rw [namedLabelEquiv_val G C L hG]
    exact fullSecondNamed_true_mem G C L hG hMin source target hs
      (by omega) hTarget
  · apply Bool.eq_false_of_not_eq_true
    intro hSecond
    simp only [fullSecondNamed, Bool.and_eq_true] at hSecond
    obtain ⟨middle, hm, hPath⟩ :=
      (any_eq_true_iff 18 _).mp hSecond.2
    simp only [Bool.and_eq_true] at hPath
    have hLast := hPath.2
    simp [namedArc, graphAuxArc] at hLast

set_option maxHeartbeats 2000000 in
theorem trimOutside_zero_second (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 8)
    (hToQ : aToQ (graphArc G L) source = true) :
    trimOutside G C L hMin 0 ⊆
      G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1 := by
  intro v hv
  have hvTrim := (Finset.mem_sdiff.mp hv).1
  have hvNotNamed := (Finset.mem_sdiff.mp hv).2
  have hqv := (Digraph.mem_outNeighborFinset (G := G)).mp
    (auxiliaryTrim_subset G C L hMin 0 hvTrim)
  have hsq : G.Adj (L.a ⟨source, hs⟩).1 (L.q 0).1 := by
    rw [aToQ_graph G L source hs] at hToQ
    exact of_decide_eq_true hToQ
  have hsv : ¬G.Adj (L.a ⟨source, hs⟩).1 v := by
    intro hAdj
    have hCap :=
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG (L.a ⟨source, hs⟩).1 (L.a _).2
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hAdj)
    apply hvNotNamed
    rcases Finset.mem_union.mp hCap with hvA | hvB
    · simp [namedVertexSet, retainedVertexSet, hvA]
    · rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C] at hvB
      rcases Finset.mem_union.mp hvB with hvP | hvQ
      · simp [namedVertexSet, retainedVertexSet, hvP]
      · simp [namedVertexSet, retainedVertexSet, hvQ]
  have hne : v ≠ (L.a ⟨source, hs⟩).1 := by
    intro heq
    apply hvNotNamed
    rw [heq]
    simp [namedVertexSet, retainedVertexSet, (L.a ⟨source, hs⟩).2]
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(L.q 0).1, hsq, by simpa [auxiliaryVertex] using hqv⟩, hsv, hne⟩

set_option maxHeartbeats 2000000 in
theorem innerSecond_true_mem (C : G.LocalConfiguration) (L : Labels G 3 C)
    (_hG : G.IsOriented) (source target : Nat)
    (hs : source < 8) (ht : target < 8)
    (hSecond : innerSecond (graphArc G L) source target = true) :
    (L.a ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1 := by
  simp only [innerSecond, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 8 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [aArc_graph G L source target hs ht] at hNot
  rw [aArc_graph G L source middle hs hm] at hFirst
  rw [aArc_graph G L middle target hm ht] at hLast
  have hneV : (L.a ⟨target, ht⟩).1 ≠ (L.a ⟨source, hs⟩).1 := by
    intro heq
    apply hne
    have hFin : (⟨target, ht⟩ : Fin 8) = ⟨source, hs⟩ := by
      apply L.a.injective
      apply Subtype.ext
      exact heq
    exact Fin.ext_iff.mp hFin
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(L.a ⟨middle, hm⟩).1, of_decide_eq_true hFirst,
    of_decide_eq_true hLast⟩, by simpa using hNot, hneV⟩

set_option maxHeartbeats 2000000 in
theorem innerSecondCount_le_graph (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (source : Nat) (hs : source < 8) :
    (innerSecondCount (graphArc G L) source).toNat ≤
      (C.A.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1).card := by
  apply count_le_filterCard C.A L.a _ _ (by omega)
  intro target hTarget
  exact innerSecond_true_mem G C L hG source target hs target.isLt hTarget

set_option maxHeartbeats 2000000 in
theorem hallZReached_true_mem (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source z : Nat) (hs : source < 8) (hz : z < 3)
    (hReached : hallZReached (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source z = true) :
    (L.z ⟨z, hz⟩).1 ∈
      G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1 := by
  simp only [hallZReached, Bool.or_eq_true] at hReached
  have hNot : ¬G.Adj (L.a ⟨source, hs⟩).1 (L.z ⟨z, hz⟩).1 :=
    GraphFacts.A_not_adj_external G C hG _ _ (L.a _).2 (L.z _).2
  have hne : (L.z ⟨z, hz⟩).1 ≠ (L.a ⟨source, hs⟩).1 := by
    intro heq
    exact GraphFacts.external_not_mem_A G C hG _ (L.z _).2 (heq ▸ (L.a _).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  rcases hReached with hP | hQ
  · obtain ⟨p, hp, hPath⟩ := (any_eq_true_iff 6 _).mp hP
    simp only [Bool.and_eq_true] at hPath
    rw [aToP_graph G L source p hs hp] at hPath
    rw [pToZ_graph G L p z hp hz] at hPath
    exact ⟨⟨(L.p ⟨p, hp⟩).1, of_decide_eq_true hPath.1,
      of_decide_eq_true hPath.2⟩, hNot, hne⟩
  · simp only [Bool.and_eq_true] at hQ
    rw [aToQ_graph G L source hs] at hQ
    have hLast := graphAuxArc_true_adj G C L hMin 0 (15 + z) (by omega) hQ.2
    simp only [auxiliaryVertex] at hLast
    have hTarget : namedVertex G C L (15 + z) = (L.z ⟨z, hz⟩).1 := by
      simp [namedVertex, labelledVertex, show ¬15 + z < 8 by omega,
        show ¬15 + z < 14 by omega, show 15 + z ≠ 14 by omega,
        show 15 + z < 18 by omega]
    rw [hTarget] at hLast
    exact ⟨⟨(L.q 0).1, of_decide_eq_true hQ.1, hLast⟩, hNot, hne⟩

set_option maxHeartbeats 2000000 in
theorem hallZCount_le_graph (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 8) :
    (count 3 (hallZReached (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source)).toNat ≤
      ((externalTargets G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1).card := by
  apply count_le_filterCard (externalTargets G C) L.z _ _ (by omega)
  intro z hZ
  exact hallZReached_true_mem G C L hG hMin source z hs z.isLt hZ

set_option maxHeartbeats 2000000 in
theorem canonicalFullNonSeymour_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    ActualTail.canonicalFullNonSeymour (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  rw [ActualTail.canonicalFullNonSeymour, all_eq_true_iff]
  intro h hh
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  let source : Nat := 1 + h
  let v : V := (L.a ⟨source, by omega⟩).1
  let namedSeconds := (namedVertexSet G C).filter fun w ↦
    w ∈ G.secondOutNeighborFinset v
  change (ActualTail.canonicalFullSecondCount (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source).toNat <
    (aDegree (graphArc G L) source).toNat
  by_cases hQ : aToQ (graphArc G L) source = true
  · let outsideSeconds := trimOutside G C L hMin 0
    have hNamed := fullSecondNamed_count_le G C L hG hMin source (by omega)
    have hNamedSource : namedVertex G C L source = v := by
      simp [v, source, namedVertex, labelledVertex, show 1 + h < 8 by omega]
    rw [hNamedSource] at hNamed
    change _ ≤ namedSeconds.card at hNamed
    have hOutsideSub : outsideSeconds ⊆ G.secondOutNeighborFinset v := by
      simpa [outsideSeconds, v, source] using
        trimOutside_zero_second G C L hG hMin source (by omega) hQ
    have hNamedSub : namedSeconds ⊆ G.secondOutNeighborFinset v := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hDisjoint : Disjoint namedSeconds outsideSeconds := by
      rw [Finset.disjoint_left]
      intro w hwN hwO
      exact (Finset.mem_sdiff.mp hwO).2 (Finset.mem_filter.mp hwN).1
    have hUnionSub : namedSeconds ∪ outsideSeconds ⊆
        G.secondOutNeighborFinset v :=
      Finset.union_subset hNamedSub hOutsideSub
    have hRepresented :
        (count 19 (fullSecondNamed (graphArc G L) (graphPToZ G L)
            (graphAuxArc G C L hMin) source)).toNat +
          (canonicalOutsideNeed (graphAuxArc G C L hMin) 0).toNat ≤
            G.secondOutdegree v := by
      rw [show (canonicalOutsideNeed (graphAuxArc G C L hMin) 0).toNat =
          (trimOutside G C L hMin (0 : Fin 4)).card by
        simpa using
          canonicalOutsideNeed_toNat G C L hG hMin (0 : Fin 4)]
      change _ + outsideSeconds.card ≤ _
      calc
        _ ≤ namedSeconds.card + outsideSeconds.card := Nat.add_le_add_right hNamed _
        _ = (namedSeconds ∪ outsideSeconds).card :=
          (Finset.card_union_of_disjoint hDisjoint).symm
        _ ≤ G.secondOutdegree v := Finset.card_le_card hUnionSub
    simp only [ActualTail.canonicalFullSecondCount, hQ, if_true]
    rw [BitVec.toNat_add,
      Nat.mod_eq_of_lt (by
        have hNamedCard : namedSeconds.card ≤ 18 := by
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
            simpa using
              (Fintype.card_congr (namedLabelEquiv G C L hG)).symm)
        have hOutsideCard : outsideSeconds.card ≤ 8 := by
          unfold outsideSeconds trimOutside
          exact (Finset.card_le_card (Finset.sdiff_subset)).trans_eq
            (auxiliaryTrim_card G C L hMin 0)
        have hOutsideEq :
            (canonicalOutsideNeed (graphAuxArc G C L hMin) 0).toNat =
              outsideSeconds.card := by
          simpa [outsideSeconds] using
            canonicalOutsideNeed_toNat G C L hG hMin (0 : Fin 4)
        omega)]
    have hAO := aOut_toNat G C L source (by omega)
    have hBO := aBOut_toNat G C L source (by omega)
    have hDegree := A_outdegree_eq_blocks G C L hG source (by omega)
    have hDirect : (aDegree (graphArc G L) source).toNat = G.outdegree v := by
      rw [aDegree, BitVec.toNat_add, hAO, hBO,
        Nat.mod_eq_of_lt (by
        have hA := Finset.card_le_card
          (Finset.filter_subset (G.Adj v) C.A)
        have hB := Finset.card_le_card
          (Finset.filter_subset (G.Adj v) C.B)
        have hACard : C.A.card = 8 := by
          simpa using (Fintype.card_congr L.a).symm
        have hBCard : C.B.card = 7 := by
          rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
          have hPCard : C.P.card = 6 := by
            simpa using (Fintype.card_congr L.p).symm
          have hQCard : C.Q.card = 1 := by
            simpa using (Fintype.card_congr L.q).symm
          have hr : C.r = 6 := by simpa [Digraph.LocalConfiguration.r] using hPCard
          omega
        change directCount G C.A v ≤ C.A.card at hA
        change directCount G C.B v ≤ C.B.card at hB
        dsimp [v] at hA hB
        omega)]
      change directCount G C.A (L.a ⟨source, by omega⟩).1 +
        directCount G C.B (L.a ⟨source, by omega⟩).1 =
          G.outdegree (L.a ⟨source, by omega⟩).1
      exact hDegree.symm
    rw [hDirect]
    change (count 19 (fullSecondNamed (graphArc G L) (graphPToZ G L)
        (graphAuxArc G C L hMin) source)).toNat +
      (canonicalOutsideNeed (graphAuxArc G C L hMin) 0).toNat <
        G.outdegree v
    exact hRepresented.trans_lt
      (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun hv ↦ hNoSeymour ⟨v, hv⟩))
  · have hQFalse := Bool.eq_false_of_not_eq_true hQ
    simp only [ActualTail.canonicalFullSecondCount, hQFalse, Bool.false_eq_true,
      if_false]
    have hNamed := fullSecondNamed_count_le G C L hG hMin source (by omega)
    have hNamedSource : namedVertex G C L source = v := by
      simp [v, source, namedVertex, labelledVertex, show 1 + h < 8 by omega]
    rw [hNamedSource] at hNamed
    change _ ≤ namedSeconds.card at hNamed
    have hNamedCard : namedSeconds.card ≤ G.secondOutdegree v := by
      apply Finset.card_le_card
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hAO := aOut_toNat G C L source (by omega)
    have hBO := aBOut_toNat G C L source (by omega)
    have hDegree := A_outdegree_eq_blocks G C L hG source (by omega)
    have hDirect : (aDegree (graphArc G L) source).toNat = G.outdegree v := by
      rw [aDegree, BitVec.toNat_add, hAO, hBO,
        Nat.mod_eq_of_lt (by
          have hA := Finset.card_le_card
            (Finset.filter_subset (G.Adj v) C.A)
          have hB := Finset.card_le_card
            (Finset.filter_subset (G.Adj v) C.B)
          have hACard : C.A.card = 8 := by
            simpa using (Fintype.card_congr L.a).symm
          have hBCard : C.B.card = 7 := by
            rw [Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C]
            have hPCard : C.P.card = 6 := by
              simpa using (Fintype.card_congr L.p).symm
            have hQCard : C.Q.card = 1 := by
              simpa using (Fintype.card_congr L.q).symm
            have hr : C.r = 6 := by simpa [Digraph.LocalConfiguration.r] using hPCard
            omega
          change directCount G C.A v ≤ C.A.card at hA
          change directCount G C.B v ≤ C.B.card at hB
          dsimp [v] at hA hB
          omega)]
      change directCount G C.A (L.a ⟨source, by omega⟩).1 +
        directCount G C.B (L.a ⟨source, by omega⟩).1 =
          G.outdegree (L.a ⟨source, by omega⟩).1
      exact hDegree.symm
    rw [hDirect]
    have hResult := lt_of_le_of_lt (hNamed.trans hNamedCard)
      (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun hv ↦ hNoSeymour ⟨v, hv⟩))
    simpa [BitVec.toNat_add] using hResult

set_option maxHeartbeats 2000000 in
theorem canonicalHallConditions_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    ActualTail.canonicalHallConditions (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  rw [ActualTail.canonicalHallConditions, all_eq_true_iff]
  intro source hs
  by_cases hInner : innerSeymour (graphArc G L) source = true
  · simp only [hInner, Bool.not_true, Bool.false_or,
      BitVec.ult_eq_decide, decide_eq_true_eq]
    let v : V := (L.a ⟨source, hs⟩).1
    let innerTargets := C.A.filter fun w ↦ w ∈ G.secondOutNeighborFinset v
    let hallNamed := (externalTargets G C).filter fun w ↦ w ∈ G.secondOutNeighborFinset v
    let outsideTargets := if aToQ (graphArc G L) source = true then
      trimOutside G C L hMin 0 else ∅
    let hallTargets := hallNamed ∪ outsideTargets
    have hInnerCount := innerSecondCount_le_graph G C L hG source hs
    change _ ≤ innerTargets.card at hInnerCount
    have hHallNamed := hallZCount_le_graph G C L hG hMin source hs
    change _ ≤ hallNamed.card at hHallNamed
    have hOutsideSub : outsideTargets ⊆ G.secondOutNeighborFinset v := by
      by_cases hQ : aToQ (graphArc G L) source = true
      · simpa [outsideTargets, hQ, v] using
          trimOutside_zero_second G C L hG hMin source hs hQ
      · simp [outsideTargets, hQ]
    have hHallNamedSub : hallNamed ⊆ G.secondOutNeighborFinset v := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hInnerSub : innerTargets ⊆ G.secondOutNeighborFinset v := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hHallOutsideDisjoint : Disjoint hallNamed outsideTargets := by
      rw [Finset.disjoint_left]
      intro w hwZ hwO
      by_cases hQ : aToQ (graphArc G L) source = true
      · have hwNotNamed : w ∉ namedVertexSet G C := by
          have hwTrim : w ∈ trimOutside G C L hMin 0 := by
            simpa [outsideTargets, hQ] using hwO
          unfold trimOutside at hwTrim
          exact (Finset.mem_sdiff.mp hwTrim).2
        apply hwNotNamed
        have hwZ' := (Finset.mem_filter.mp hwZ).1
        simp [namedVertexSet, retainedVertexSet, hwZ']
      · simp [outsideTargets, hQ] at hwO
    have hHallSub : hallTargets ⊆ G.secondOutNeighborFinset v := by
      exact Finset.union_subset hHallNamedSub hOutsideSub
    have hInnerHallDisjoint : Disjoint innerTargets hallTargets := by
      rw [Finset.disjoint_left]
      intro w hwA hwHall
      rcases Finset.mem_union.mp hwHall with hwZ | hwO
      · have hwA' := (Finset.mem_filter.mp hwA).1
        have hwZ' := (Finset.mem_filter.mp hwZ).1
        exact GraphFacts.external_not_mem_A G C hG w hwZ' hwA'
      · by_cases hQ : aToQ (graphArc G L) source = true
        · have hwNotNamed : w ∉ namedVertexSet G C :=
            (by
              have hwTrim : w ∈ trimOutside G C L hMin 0 := by
                simpa [outsideTargets, hQ] using hwO
              unfold trimOutside at hwTrim
              exact (Finset.mem_sdiff.mp hwTrim).2)
          apply hwNotNamed
          have hwA' := (Finset.mem_filter.mp hwA).1
          simp [namedVertexSet, retainedVertexSet, hwA']
        · simp [outsideTargets, hQ] at hwO
    have hUnionSub : innerTargets ∪ hallTargets ⊆
        G.secondOutNeighborFinset v :=
      Finset.union_subset hInnerSub hHallSub
    have hUnionCard : innerTargets.card + hallTargets.card ≤
        G.secondOutdegree v := by
      rw [← Finset.card_union_of_disjoint hInnerHallDisjoint]
      exact Finset.card_le_card hUnionSub
    have hOutsideCount :
        (if aToQ (graphArc G L) source = true then
          canonicalOutsideNeed (graphAuxArc G C L hMin) 0 else 0).toNat =
          outsideTargets.card := by
      by_cases hQ : aToQ (graphArc G L) source = true
      · simp only [hQ, if_true]
        simpa [outsideTargets, hQ] using
          canonicalOutsideNeed_toNat G C L hG hMin (0 : Fin 4)
      · have hQFalse := Bool.eq_false_of_not_eq_true hQ
        simp [outsideTargets, hQ]
    have hHallCount :
        (ActualTail.canonicalHallCount (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) source).toNat ≤ hallTargets.card := by
      rw [ActualTail.canonicalHallCount, BitVec.toNat_add,
        Nat.mod_eq_of_lt (by
          have hNamedCard : hallNamed.card ≤ 3 := by
            exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
              simpa using (Fintype.card_congr L.z).symm)
          have hOutsideCard : outsideTargets.card ≤ 8 := by
            by_cases hQ : aToQ (graphArc G L) source = true
            · simp only [outsideTargets, hQ, if_true]
              exact (Finset.card_le_card Finset.sdiff_subset).trans_eq
                (auxiliaryTrim_card G C L hMin 0)
            · simp [outsideTargets, hQ]
          omega), hOutsideCount]
      rw [Finset.card_union_of_disjoint hHallOutsideDisjoint]
      exact Nat.add_le_add hHallNamed (le_refl _)
    have hInnerNat : (aOut (graphArc G L) source).toNat ≤
        (innerSecondCount (graphArc G L) source).toNat := by
      unfold innerSeymour at hInner
      simpa [BitVec.ule_eq_decide] using hInner
    have hAO := aOut_toNat G C L source hs
    have hBO := aBOut_toNat G C L source hs
    have hDegree := A_outdegree_eq_blocks G C L hG source hs
    have hSecondStrict : G.secondOutdegree v < G.outdegree v :=
      Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun hv ↦ hNoSeymour ⟨v, hv⟩)
    rw [hBO]
    dsimp [v] at hUnionCard hSecondStrict
    omega
  · have hInnerFalse := Bool.eq_false_of_not_eq_true hInner
    simp [hInnerFalse]

set_option maxHeartbeats 2000000 in
theorem canonicalAuxiliaryCore_true (C : G.LocalConfiguration)
    (L : Labels G 3 C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    ActualTail.canonicalAuxiliaryCore (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  have hOriented := auxiliaryOriented_true G C L hG hMin
  have hDegree := auxNamedOut_le_eight_true G C L hG hMin
  have hHall := canonicalHallConditions_true G C L hG hMin hNoSeymour
  have hFull := canonicalFullNonSeymour_true G C L hG hMin hNoSeymour
  simp only [ActualTail.canonicalAuxiliaryCore, Bool.and_eq_true]
  exact ⟨⟨⟨hOriented, hDegree⟩, hHall⟩, hFull⟩

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryBridge
