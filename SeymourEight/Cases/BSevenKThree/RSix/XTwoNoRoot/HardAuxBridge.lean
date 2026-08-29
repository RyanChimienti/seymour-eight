import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.EasyBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardAuxBridge

open Shared Shared.FiniteCore CertificateBridge Labels Encoding EasyBridge
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
open SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def namedVertex (C : G.LocalConfiguration) (L : Labels G 5 C)
    (i : Nat) : V :=
  if hi : i < 15 then localVertex G L i
  else if hi20 : i < 20 then (L.z ⟨i - 15, by omega⟩).1 else (L.q 0).1

def namedVertexSet (C : G.LocalConfiguration) : Finset V :=
  localSet G C ∪ externalTargets G C

noncomputable def namedEquiv (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) :
    Fin 20 ≃ {v : V // v ∈ namedVertexSet G C} := by
  let f : Fin 20 → {v : V // v ∈ namedVertexSet G C} := fun i ↦
    if hi : i.val < 15 then
      ⟨(localEquiv G C L ⟨i, hi⟩).1, by
        exact Finset.mem_union_left _ (localEquiv G C L ⟨i, hi⟩).2⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1, by
      simp [namedVertexSet, (L.z ⟨i.val - 15, by omega⟩).2]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvLocal | hvExternal
    · obtain ⟨i, hi⟩ := (localEquiv G C L).surjective ⟨v, hvLocal⟩
      refine ⟨⟨i, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, i.isLt] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvExternal⟩
      refine ⟨⟨15 + i, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬15 + i.val < 15 by omega] using congrArg Subtype.val hi
  · rw [show Fintype.card {v : V // v ∈ namedVertexSet G C} =
        (namedVertexSet G C).card by simp]
    change Fintype.card (Fin 20) = (localSet G C ∪ externalTargets G C).card
    rw [show localSet G C = C.A ∪ C.B by rfl]
    rw [Finset.card_union_of_disjoint
      (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG)]
    have hLocal : (C.A ∪ C.B).card = 15 := by
      have h := (Fintype.card_congr (localEquiv G C L)).symm
      rw [Fintype.card_fin] at h
      rw [show Fintype.card {v : V // v ∈ localSet G C} =
        (localSet G C).card by simp] at h
      simpa only [localSet] using h
    have hExternal : (externalTargets G C).card = 5 := by
      simpa using (Fintype.card_congr L.z).symm
    simp [hLocal, hExternal]

@[simp] theorem namedEquiv_val (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (i : Fin 20) :
    (namedEquiv G C L hG i).1 = namedVertex G C L i := by
  by_cases hi : i.val < 15
  · simp [namedEquiv, namedVertex, hi, localEquiv_val]
  · simp [namedEquiv, namedVertex, hi, i.isLt]

noncomputable def auxTrim (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 6) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq
    (s := G.outNeighborFinset (auxiliaryVertex G L i))
      (by simpa [Digraph.outdegree] using hMin (auxiliaryVertex G L i)))

theorem auxTrim_subset (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 6) :
    auxTrim G C L hMin i ⊆ G.outNeighborFinset (auxiliaryVertex G L i) :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := G.outNeighborFinset (auxiliaryVertex G L i))
      (by simpa [Digraph.outdegree] using hMin (auxiliaryVertex G L i)))).1

theorem auxTrim_card (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 6) :
    (auxTrim G C L hMin i).card = 8 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := G.outNeighborFinset (auxiliaryVertex G L i))
      (by simpa [Digraph.outdegree] using hMin (auxiliaryVertex G L i)))).2

noncomputable abbrev qTrim (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) : Finset V := auxTrim G C L hMin 0

theorem qTrim_subset (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) :
    qTrim G C L hMin ⊆ G.outNeighborFinset (L.q 0).1 := by
  simpa [auxiliaryVertex] using auxTrim_subset G C L hMin (0 : Fin 6)

theorem qTrim_card (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) : (qTrim G C L hMin).card = 8 :=
  auxTrim_card G C L hMin 0

noncomputable def graphAuxArc (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (aux target : Nat) : Bool :=
  if ha : aux < 6 then
    if _ht : target < 20 then
      decide (namedVertex G C L target ∈ auxTrim G C L hMin ⟨aux, ha⟩)
    else false
  else false

@[simp] theorem graphAuxArc_eq (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (aux target : Nat)
    (ha : aux < 6) (ht : target < 20) :
    graphAuxArc G C L hMin aux target =
      decide (namedVertex G C L target ∈ auxTrim G C L hMin ⟨aux, ha⟩) := by
  simp [graphAuxArc, ha, ht]

theorem graphAuxArc_true_adj_aux (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (aux target : Nat) (ha : aux < 6)
    (hArc : graphAuxArc G C L hMin aux target = true) :
    G.Adj (auxiliaryVertex G L aux) (namedVertex G C L target) := by
  have ht : target < 20 := by
    by_contra hn
    simp [graphAuxArc, show ¬target < 20 by omega] at hArc
  rw [graphAuxArc_eq G C L hMin aux target ha ht] at hArc
  exact (Digraph.mem_outNeighborFinset (G := G)).mp
    (auxTrim_subset G C L hMin ⟨aux, ha⟩ (of_decide_eq_true hArc))

theorem graphAuxArc_true_adj (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (target : Nat)
    (hArc : graphAuxArc G C L hMin 0 target = true) :
    G.Adj (L.q 0).1 (namedVertex G C L target) := by
  simpa [auxiliaryVertex] using
    graphAuxArc_true_adj_aux G C L hMin 0 target (by omega) hArc

theorem auxNamedOut_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 6) :
    (HardCore.auxNamedOut (graphAuxArc G C L hMin) i).toNat =
      ((namedVertexSet G C).filter fun v ↦ v ∈ auxTrim G C L hMin i).card := by
  rw [HardCore.auxNamedOut, toNat_count_eq_fin_sum 20 _ (by omega),
    filterCard_eq_sum_fin (namedVertexSet G C) (namedEquiv G C L hG)]
  apply Finset.sum_congr rfl
  intro target _
  rw [graphAuxArc_eq G C L hMin i target i.isLt target.isLt,
    namedEquiv_val G C L hG]
  by_cases hm : namedVertex G C L target ∈ auxTrim G C L hMin i <;> simp [hm]

theorem auxiliaryExact_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    HardCore.auxiliaryExact (graphAuxArc G C L hMin) = true := by
  simp only [HardCore.auxiliaryExact, BitVec.ule_eq_decide, decide_eq_true_eq,
    all_eq_true_iff]
  intro i hi
  rw [auxNamedOut_toNat G C L hG hMin ⟨i, hi⟩]
  exact (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2)).trans_eq (auxTrim_card G C L hMin ⟨i, hi⟩)

theorem auxIncoming_zero_eq_adj (C : G.LocalConfiguration) (L : Labels G 5 C)
    (source : Nat) (hs : source < 14) :
    HardCore.auxIncoming (graphArc G L) (graphPToZ G L) source 0 =
      decide (G.Adj (localVertex G L source) (L.q 0).1) := by
  by_cases hsA : source < 8
  · simp [HardCore.auxIncoming, aToQ, hsA, localVertex,
      graphArc_AQ G L source hsA]
  · simp [HardCore.auxIncoming, pToQ, hsA, hs, localVertex,
      graphArc_PQ G L (source - 8) (by omega)]

theorem auxIncoming_eq_adj (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (source aux : Nat) (hs : source < 14) (ha : aux < 6) :
    HardCore.auxIncoming (graphArc G L) (graphPToZ G L) source aux =
      decide (G.Adj (localVertex G L source) (auxiliaryVertex G L aux)) := by
  by_cases hsA : source < 8
  · by_cases ha0 : aux = 0
    · subst aux
      simpa [auxiliaryVertex] using auxIncoming_zero_eq_adj G C L source hs
    · have hzBound : aux - 1 < 5 := by omega
      have hNot : ¬G.Adj (localVertex G L source)
          (auxiliaryVertex G L aux) := by
        exact SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.A_not_adj_external
          G C hG _ _ (by simp [localVertex, hsA])
          (by simp [auxiliaryVertex, ha, ha0])
      simp [HardCore.auxIncoming, hsA, ha0, hNot]
  · by_cases ha0 : aux = 0
    · subst aux
      simpa [auxiliaryVertex] using auxIncoming_zero_eq_adj G C L source hs
    · have hp : source - 8 < 6 := by omega
      have hz : aux - 1 < 5 := by omega
      simp [HardCore.auxIncoming, hsA, hs, ha0, auxiliaryVertex, ha,
        localVertex, graphPToZ_eq G L (source - 8) (aux - 1) hp hz]

@[simp] theorem auxiliaryVertex_eq_named (C : G.LocalConfiguration)
    (L : Labels G 5 C) (i : Nat) (hi : i < 6) :
    auxiliaryVertex G L i = namedVertex G C L (14 + i) := by
  by_cases hi0 : i = 0
  · subst i
    simp [auxiliaryVertex, namedVertex, localVertex]
  · simp only [auxiliaryVertex, dif_pos hi, hi0, if_false,
      namedVertex, dif_neg (show ¬14 + i < 15 by omega),
      dif_pos (show 14 + i < 20 by omega)]
    have heq : (⟨14 + i - 15, by omega⟩ : Fin 5) = ⟨i - 1, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [heq]

theorem auxiliaryOriented_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    HardCore.auxiliaryOriented (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  simp only [HardCore.auxiliaryOriented, Bool.and_eq_true, all_eq_true_iff]
  constructor
  · intro aux ha source hs
    rw [Bool.not_eq_true']
    by_contra hn
    have hb := Bool.eq_true_of_not_eq_false hn
    rw [Bool.and_eq_true] at hb
    rw [auxIncoming_eq_adj G C L hG source aux hs ha] at hb
    have hNamed : namedVertex G C L source = localVertex G L source := by
      simp [namedVertex, show source < 15 by omega]
    have hOut := graphAuxArc_true_adj_aux G C L hMin aux source ha hb.2
    rw [hNamed] at hOut
    exact hG.2 (of_decide_eq_true hb.1) hOut
  · intro aux ha
    constructor
    · rw [Bool.not_eq_true']
      apply Bool.eq_false_of_not_eq_true
      intro hLoop
      have hAdj := graphAuxArc_true_adj_aux G C L hMin aux (14 + aux) ha hLoop
      rw [← auxiliaryVertex_eq_named G C L aux ha] at hAdj
      exact hG.1 _ hAdj
    · intro other ho
      by_cases heq : aux = other
      · simp [heq]
      · simp only [heq, decide_false, Bool.false_or]
        rw [Bool.not_eq_true']
        apply Bool.eq_false_of_not_eq_true
        intro hBoth
        rw [Bool.and_eq_true] at hBoth
        have h1 := graphAuxArc_true_adj_aux G C L hMin aux (14 + other) ha hBoth.1
        have h2 := graphAuxArc_true_adj_aux G C L hMin other (14 + aux) ho hBoth.2
        rw [← auxiliaryVertex_eq_named G C L other ho] at h1
        rw [← auxiliaryVertex_eq_named G C L aux ha] at h2
        exact hG.2 h1 h2

noncomputable def qOutside (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) : Finset V :=
  qTrim G C L hMin \ namedVertexSet G C

noncomputable def auxOutsideSet (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 6) : Finset V :=
  auxTrim G C L hMin i \ namedVertexSet G C

theorem auxOutsideNeed_toNat_aux (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) (i : Fin 6) :
    (HardCore.auxOutsideNeed (graphAuxArc G C L hMin) i).toNat =
      (auxOutsideSet G C L hMin i).card := by
  have hEight : ((8 : BitVec 8).toNat) = 8 := by decide
  rw [HardCore.auxOutsideNeed, BitVec.toNat_sub_of_le]
  · rw [auxNamedOut_toNat G C L hG hMin i, hEight,
      ← auxTrim_card G C L hMin i]
    unfold auxOutsideSet
    rw [Finset.card_sdiff]
    have hEq : namedVertexSet G C ∩ auxTrim G C L hMin i =
        (namedVertexSet G C).filter fun v ↦ v ∈ auxTrim G C L hMin i := by
      ext v
      simp [and_comm]
    rw [hEq]
  · rw [BitVec.le_def, hEight, auxNamedOut_toNat G C L hG hMin i]
    exact (Finset.card_le_card (by
      intro v hv
      exact (Finset.mem_filter.mp hv).2)).trans_eq (auxTrim_card G C L hMin i)

theorem auxOutsideNeed_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) :
    (HardCore.auxOutsideNeed (graphAuxArc G C L hMin) 0).toNat =
      (qOutside G C L hMin).card := by
  simpa [qOutside, auxOutsideSet] using
    auxOutsideNeed_toNat_aux G C L hG hMin (0 : Fin 6)

theorem coreArc_eq_adj (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (source target : Nat)
    (hs : source < 14) (ht : target < 20) :
    coreArc 5 (graphArc G L) (graphPToZ G L) source target =
      decide (G.Adj (localVertex G L source) (namedVertex G C L target)) := by
  by_cases hsA : source < 8
  · by_cases htLocal : target < 15
    · simp [coreArc, hsA, htLocal, namedVertex,
        graphArc_eq_adj G C L source target hs htLocal]
    · have hTarget : namedVertex G C L target =
          (L.z ⟨target - 15, by omega⟩).1 := by
        simp [namedVertex, htLocal, ht]
      have hNot : ¬G.Adj (localVertex G L source) (namedVertex G C L target) := by
        rw [hTarget]
        exact SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.A_not_adj_external
          G C hG _ _ (by simp [localVertex, hsA])
          (L.z _).2
      simp [coreArc, hsA, htLocal, hNot]
  · have hsP : source < 14 := hs
    by_cases htLocal : target < 15
    · simp [coreArc, hsA, hsP, htLocal, namedVertex,
        graphArc_eq_adj G C L source target hs htLocal]
    · have hz : target - 15 < 5 := by omega
      have hSource : localVertex G L source =
          (L.p ⟨source - 8, by omega⟩).1 := by
        simp [localVertex, hsA, hs]
      simp [coreArc, hsA, hsP, htLocal, ht, namedVertex, hSource,
        graphPToZ_eq G L (source - 8) (target - 15) (by omega) hz]

theorem namedDirect_eq_adj (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (source target : Nat)
    (hs : source < 14) (ht : target < 20) :
    HardCore.namedDirect (graphArc G L) (graphPToZ G L) source target =
      decide (G.Adj (namedVertex G C L source) (namedVertex G C L target)) := by
  rw [HardCore.namedDirect, if_pos hs, coreArc_eq_adj G C L hG source target hs ht]
  have hSource : namedVertex G C L source = localVertex G L source := by
    simp [namedVertex, show source < 15 by omega]
  rw [hSource]

theorem namedArc_true_adj (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (middle target : Nat) (hm : middle < 20) (ht : target < 20)
    (hArc : HardCore.namedArc (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) middle target = true) :
    G.Adj (namedVertex G C L middle) (namedVertex G C L target) := by
  by_cases hm14 : middle < 14
  · simp only [HardCore.namedArc, hm14, if_true] at hArc
    rw [coreArc_eq_adj G C L hG middle target hm14 ht] at hArc
    have hLocal : namedVertex G C L middle = localVertex G L middle := by
      simp [namedVertex, show middle < 15 by omega]
    simpa [hLocal] using of_decide_eq_true hArc
  · have ha : middle - 14 < 6 := by omega
    simp only [HardCore.namedArc, hm14, hm, if_false, if_true] at hArc
    have hAdj := graphAuxArc_true_adj_aux G C L hMin (middle - 14) target ha hArc
    rw [auxiliaryVertex_eq_named G C L (middle - 14) ha] at hAdj
    simpa [show 14 + (middle - 14) = middle by omega] using hAdj

theorem fullSecondNamed_true_mem (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source target : Nat) (hs : source < 14) (ht : target < 20)
    (hSecond : HardCore.fullSecondNamed (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source target = true) :
    namedVertex G C L target ∈
      G.secondOutNeighborFinset (namedVertex G C L source) := by
  simp only [HardCore.fullSecondNamed, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotDirect⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 20 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [namedDirect_eq_adj G C L hG source middle (by omega) hm] at hFirst
  rw [namedDirect_eq_adj G C L hG source target (by omega) ht] at hNotDirect
  have hLast' := namedArc_true_adj G C L hG hMin middle target hm ht hLast
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨namedVertex G C L middle, of_decide_eq_true hFirst, hLast'⟩,
    by simpa using hNotDirect, ?_⟩
  intro heq
  apply hne
  have hFin : (⟨target, ht⟩ : Fin 20) = ⟨source, by omega⟩ := by
    apply (namedEquiv G C L hG).injective
    apply Subtype.ext
    simpa only [namedEquiv_val] using heq
  exact Fin.ext_iff.mp hFin

theorem fullSecondNamed_count_le (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 14) :
    (count 20 (HardCore.fullSecondNamed (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source)).toNat ≤
      ((namedVertexSet G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (namedVertex G C L source)).card := by
  apply SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.count_le_filterCard
    (namedVertexSet G C) (namedEquiv G C L hG) _ _ (by omega)
  intro target hTarget
  rw [namedEquiv_val G C L hG]
  exact fullSecondNamed_true_mem G C L hG hMin source target hs target.isLt hTarget

theorem threshold_count_eq (need : BitVec 8) (hLe : need.ule 8 = true) :
    count 8 (fun slot ↦ (BitVec.ofNat 8 (slot + 1)).ule need) = need := by
  have hLe' : need.toNat ≤ 8 := by
    simpa [BitVec.ule_eq_decide] using hLe
  apply BitVec.eq_of_toNat_eq
  interval_cases hNeed : need.toNat <;>
    simp [count, bitCount, BitVec.ule_eq_decide, hNeed]

theorem nested_union_count_le (incoming : Nat → Bool) (need : Nat → BitVec 8)
    (bound : BitVec 8)
    (hBound : (all 6 fun i ↦ !incoming i || (need i).ule bound) = true) :
    (count 8 fun slot ↦ any 6 fun i ↦ incoming i &&
      (BitVec.ofNat 8 (slot + 1)).ule (need i)).ule bound = true := by
  simp only [all, any, count, bitCount] at hBound ⊢
  bv_decide

theorem auxOutside_count_eq (auxArc : Nat → Nat → Bool)
    (hLe : (HardCore.auxOutsideNeed auxArc 0).ule 8 = true) :
    count 8 (HardCore.auxOutside auxArc 0) = HardCore.auxOutsideNeed auxArc 0 := by
  exact threshold_count_eq _ hLe

theorem fullOutsideSecond_eq (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (source slot : Nat) (hs : source < 8) :
    HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source slot =
      (aToQ (graphArc G L) source &&
        HardCore.auxOutside (graphAuxArc G C L hMin) 0 slot) := by
  simp [HardCore.fullOutsideSecond, HardCore.auxIncoming, hs, any]

theorem qOutside_second (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 8)
    (hToQ : aToQ (graphArc G L) source = true) :
    qOutside G C L hMin ⊆
      G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1 := by
  intro v hv
  have hvTrim := (Finset.mem_sdiff.mp hv).1
  have hvNotNamed := (Finset.mem_sdiff.mp hv).2
  have hqv := (Digraph.mem_outNeighborFinset (G := G)).mp
    (qTrim_subset G C L hMin hvTrim)
  have hsq : G.Adj (L.a ⟨source, hs⟩).1 (L.q 0).1 := by
    rw [aToQ, graphArc_AQ G L source hs] at hToQ
    exact of_decide_eq_true hToQ
  have hsv : ¬G.Adj (L.a ⟨source, hs⟩).1 v := by
    intro hAdj
    have hCap :=
      SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
        G C hG (L.a ⟨source, hs⟩).1 (L.a _).2
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hAdj)
    apply hvNotNamed
    rcases Finset.mem_union.mp hCap with hvA | hvB
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvA)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvB)
  have hne : v ≠ (L.a ⟨source, hs⟩).1 := by
    intro heq
    apply hvNotNamed
    rw [heq]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (L.a ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(L.q 0).1, hsq, hqv⟩, hsv, hne⟩

theorem auxOutside_second (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source aux : Nat) (hs : source < 14) (ha : aux < 6)
    (hIncoming : HardCore.auxIncoming (graphArc G L) (graphPToZ G L)
      source aux = true) :
    auxOutsideSet G C L hMin ⟨aux, ha⟩ ⊆
      G.secondOutNeighborFinset (localVertex G L source) := by
  intro v hv
  have hvTrim := (Finset.mem_sdiff.mp hv).1
  have hvNotNamed := (Finset.mem_sdiff.mp hv).2
  have hLast := (Digraph.mem_outNeighborFinset (G := G)).mp
    (auxTrim_subset G C L hMin ⟨aux, ha⟩ hvTrim)
  rw [auxIncoming_eq_adj G C L hG source aux hs ha] at hIncoming
  have hFirst := of_decide_eq_true hIncoming
  have hNotDirect : ¬G.Adj (localVertex G L source) v := by
    intro hAdj
    apply hvNotNamed
    by_cases hsA : source < 8
    · have hCap :=
        SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
          G C hG (localVertex G L source) (by simp [localVertex, hsA])
            ((Digraph.mem_outNeighborFinset (G := G)).mpr hAdj)
      rcases Finset.mem_union.mp hCap with hvA | hvB
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvA)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvB)
    · have hp : source - 8 < 6 := by omega
      have hCap := BSixKThree.P_outgoingCaptured_general G C hG
        (localVertex G L source) (by simp [localVertex, hsA, hs])
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hAdj)
      rcases Finset.mem_union.mp hCap with hvKnown | hvExt
      · rcases Finset.mem_union.mp hvKnown with hvHP | hvQ
        · rcases Finset.mem_union.mp hvHP with hvH | hvP
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ))
      · exact Finset.mem_union_right _ hvExt
  have hne : v ≠ localVertex G L source := by
    intro heq
    apply hvNotNamed
    rw [heq]
    apply Finset.mem_union_left _
    rw [← localEquiv_val G C L ⟨source, by omega⟩]
    exact (localEquiv G C L ⟨source, by omega⟩).2
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨auxiliaryVertex G L aux, hFirst, hLast⟩, hNotDirect, hne⟩

theorem fullOutsideCount_le_actual (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 14) :
    (count 8 (HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source)).toNat ≤
      (G.secondOutNeighborFinset (localVertex G L source) \ namedVertexSet G C).card := by
  let outsideSeconds :=
    G.secondOutNeighborFinset (localVertex G L source) \ namedVertexSet G C
  let boundNat := min outsideSeconds.card 8
  let bound : BitVec 8 := BitVec.ofNat 8 boundNat
  have hEach : (all 6 fun aux ↦
      !HardCore.auxIncoming (graphArc G L) (graphPToZ G L) source aux ||
        (HardCore.auxOutsideNeed (graphAuxArc G C L hMin) aux).ule bound) = true := by
    rw [all_eq_true_iff]
    intro aux ha
    by_cases hIn : HardCore.auxIncoming (graphArc G L) (graphPToZ G L)
        source aux = true
    · have hSub : auxOutsideSet G C L hMin ⟨aux, ha⟩ ⊆ outsideSeconds := by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨auxOutside_second G C L hG hMin
          source aux hs ha hIn hv, (Finset.mem_sdiff.mp hv).2⟩
      have hNeed := auxOutsideNeed_toNat_aux G C L hG hMin ⟨aux, ha⟩
      have hNeedEight : (auxOutsideSet G C L hMin ⟨aux, ha⟩).card ≤ 8 :=
        (Finset.card_le_card Finset.sdiff_subset).trans_eq
          (auxTrim_card G C L hMin ⟨aux, ha⟩)
      have hNeedOutside := Finset.card_le_card hSub
      have hBoundNat : bound.toNat = boundNat := by
        simp [bound, boundNat]
      simp only [hIn, Bool.not_true, Bool.false_or, BitVec.ule_eq_decide,
        decide_eq_true_eq]
      rw [hNeed, hBoundNat]
      dsimp [boundNat]
      omega
    · have hFalse := Bool.eq_false_of_not_eq_true hIn
      simp [hFalse]
  have hNested := nested_union_count_le
    (fun aux ↦ HardCore.auxIncoming (graphArc G L) (graphPToZ G L) source aux)
    (HardCore.auxOutsideNeed (graphAuxArc G C L hMin)) bound hEach
  change (count 8 (HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
    (graphAuxArc G C L hMin) source)).toNat ≤ outsideSeconds.card
  change (count 8 (HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
    (graphAuxArc G C L hMin) source)).ule bound = true at hNested
  have hNat : (count 8 (HardCore.fullOutsideSecond (graphArc G L)
      (graphPToZ G L) (graphAuxArc G C L hMin) source)).toNat ≤ bound.toNat := by
    simpa [BitVec.ule_eq_decide] using hNested
  have hBoundNat : bound.toNat = boundNat := by simp [bound, boundNat]
  rw [hBoundNat] at hNat
  exact hNat.trans (Nat.min_le_left _ _)

theorem aDegree_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (source : Nat) (hs : source < 8) :
    (aDegree (graphArc G L) source).toNat = G.outdegree (L.a ⟨source, hs⟩).1 := by
  have hA := internalA_toNat G C L source hs
  have hB := outB_toNat G C L source hs
  have hCap :=
    SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG (L.a ⟨source, hs⟩).1 (L.a _).2
  have hDegree := BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G (L.a ⟨source, hs⟩).1 (localSet G C) hCap
  rw [aDegree, BitVec.toNat_add,
    show aOut (graphArc G L) source =
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.internalA
        (graphArc G L) source by rfl,
    show aBOut (graphArc G L) source =
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.outB
        (graphArc G L) source by rfl,
    hA, hB, Nat.mod_eq_of_lt (by
      have ha : directCount G C.A (L.a ⟨source, hs⟩).1 ≤ 8 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr L.a).symm)
      have hb : directCount G C.B (L.a ⟨source, hs⟩).1 ≤ 7 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
          have hq : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
          rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
            Finset.card_union_of_disjoint
              (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C), hp, hq])
      omega)]
  rw [← directCount_union_of_disjoint G C.A C.B _
    (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)]
  exact hDegree.symm

theorem pDegree_eq_easy (arc pToZ : Nat → Nat → Bool) (p : Nat)
    (hZero : arc (8 + p) 0 = false)
    (hSix : arc (8 + p) 6 = false) (hSeven : arc (8 + p) 7 = false) :
    HardCore.pDegree arc pToZ p =
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.localOut arc (8 + p) +
        SeymourEight.BSixKThreeCore.sumN 5 (pToZ p) := by
  simp only [HardCore.pDegree, HardCore.pHOut, pAuxOut, pZOut, pToQ,
    pOut, pArc, pToA,
    SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.localOut,
    SeymourEight.BSixKThreeCore.sumN, SeymourEight.BSixKThreeCore.bitCount,
    count, bitCount,
    hZero, hSix, hSeven, Bool.false_eq_true, if_false]
  bv_decide

theorem pDegree_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (p : Nat) (hp : p < 6) :
    (HardCore.pDegree (graphArc G L) (graphPToZ G L) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hZero : graphArc G L (8 + p) 0 = false := by
    rw [graphArc_PA G L p 0 hp (by omega)]
    apply Bool.eq_false_of_not_eq_true
    intro hAdj
    have hBack : G.Adj C.a1 (L.p ⟨p, hp⟩).1 :=
      (Finset.mem_filter.mp (L.p ⟨p, hp⟩).2).2
    exact hG.2 (of_decide_eq_true hAdj) (by simpa [L.a_zero] using hBack)
  have hSix : graphArc G L (8 + p) 6 = false := by
    rw [graphArc_PA G L p 6 hp (by omega)]
    exact decide_eq_false (BSixKThreeCoreGraphBridge.P_not_adj_R G C
      (L.p ⟨p, hp⟩).1 (L.a ⟨6, by omega⟩).1 (L.p _).2
      (by simpa using L.a_r ⟨0, by omega⟩))
  have hSeven : graphArc G L (8 + p) 7 = false := by
    rw [graphArc_PA G L p 7 hp (by omega)]
    exact decide_eq_false (BSixKThreeCoreGraphBridge.P_not_adj_R G C
      (L.p ⟨p, hp⟩).1 (L.a ⟨7, by omega⟩).1 (L.p _).2
      (by simpa using L.a_r ⟨1, by omega⟩))
  have hLocal := localOut_toNat G C L (8 + p) (by omega)
  have hExt := externalOut_toNat G C L p hp (by omega) (by omega)
  have hpVertex : localVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [localVertex, show ¬8 + p < 8 by omega, show 8 + p < 14 by omega]
  rw [hpVertex] at hLocal
  rw [pDegree_eq_easy _ _ p hZero hSix hSeven, BitVec.toNat_add,
    hLocal, hExt,
    Nat.mod_eq_of_lt (by
      have hl : directCount G (localSet G C) (L.p ⟨p, hp⟩).1 ≤ 15 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr (localEquiv G C L)).symm)
      have he : directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 ≤ 5 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr L.z).symm)
      omega), ← directCount_union_of_disjoint G (localSet G C)
        (externalTargets G C) _
          (BSixKThreeCoreGraphBridge.disjoint_local_external G C hG)]
  have hCap : G.outNeighborFinset (L.p ⟨p, hp⟩).1 ⊆
      localSet G C ∪ externalTargets G C := by
    intro v hv
    have hv' := BSixKThree.P_outgoingCaptured_general G C hG
      (L.p ⟨p, hp⟩).1 (L.p _).2 hv
    rcases Finset.mem_union.mp hv' with hvLocal | hvExt
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hvLocal with hvHP | hvQ
      · rcases Finset.mem_union.mp hvHP with hvH | hvP
        · exact Finset.mem_union_left C.B
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
        · exact Finset.mem_union_right C.A
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
      · exact Finset.mem_union_right C.A
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
    · exact Finset.mem_union_right _ hvExt
  exact (BSixKThreeCoreGraphBridge.outdegree_eq_directCount_of_captured
    G (L.p ⟨p, hp⟩).1 _ hCap).symm

theorem fullNonSeymourA_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    (all 8 fun a ↦ (HardCore.fullSecondCount (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) a).ult (aDegree (graphArc G L) a)) = true := by
  rw [all_eq_true_iff]
  intro source hs
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  let v := (L.a ⟨source, hs⟩).1
  let namedSeconds := (namedVertexSet G C).filter fun w ↦
    w ∈ G.secondOutNeighborFinset v
  let outsideSeconds := if aToQ (graphArc G L) source = true then
    qOutside G C L hMin else ∅
  have hNamed := fullSecondNamed_count_le G C L hG hMin source (by omega)
  have hSource : namedVertex G C L source = v := by
    simp [namedVertex, v, show source < 15 by omega, localVertex, hs]
  rw [hSource] at hNamed
  change _ ≤ namedSeconds.card at hNamed
  have hOutsideSub : outsideSeconds ⊆ G.secondOutNeighborFinset v := by
    by_cases hQ : aToQ (graphArc G L) source = true
    · simpa [outsideSeconds, hQ, v] using qOutside_second G C L hG hMin source hs hQ
    · simp [outsideSeconds, hQ]
  have hNamedSub : namedSeconds ⊆ G.secondOutNeighborFinset v := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hDisjoint : Disjoint namedSeconds outsideSeconds := by
    rw [Finset.disjoint_left]
    intro w hwN hwO
    by_cases hQ : aToQ (graphArc G L) source = true
    · have hwOut : w ∈ qOutside G C L hMin := by simpa [outsideSeconds, hQ] using hwO
      exact (Finset.mem_sdiff.mp hwOut).2 (Finset.mem_filter.mp hwN).1
    · simp [outsideSeconds, hQ] at hwO
  have hUnionSub : namedSeconds ∪ outsideSeconds ⊆
      G.secondOutNeighborFinset v := Finset.union_subset hNamedSub hOutsideSub
  have hOutsideCount :
      (count 8 (HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
        (graphAuxArc G C L hMin) source)).toNat = outsideSeconds.card := by
    by_cases hQ : aToQ (graphArc G L) source = true
    · have hFun : HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) source =
          HardCore.auxOutside (graphAuxArc G C L hMin) 0 := by
        funext slot
        simp [fullOutsideSecond_eq G C L hMin source slot hs, hQ]
      rw [hFun, auxOutside_count_eq]
      · simpa [outsideSeconds, hQ] using auxOutsideNeed_toNat G C L hG hMin
      · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
        have hCard := auxOutsideNeed_toNat G C L hG hMin
        rw [hCard]
        exact (Finset.card_le_card Finset.sdiff_subset).trans_eq
          (qTrim_card G C L hMin)
    · have hQFalse := Bool.eq_false_of_not_eq_true hQ
      have hFun : HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) source = fun _ ↦ false := by
        funext slot
        simp [fullOutsideSecond_eq G C L hMin source slot hs, hQFalse]
      rw [hFun]
      simp [count, bitCount, outsideSeconds, hQ]
  change (HardCore.fullSecondCount (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source).toNat <
    (aDegree (graphArc G L) source).toNat
  rw [HardCore.fullSecondCount, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by
      have hn : namedSeconds.card ≤ 20 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr (namedEquiv G C L hG)).symm)
      have ho : outsideSeconds.card ≤ 8 := by
        by_cases hQ : aToQ (graphArc G L) source = true
        · simp only [outsideSeconds, hQ, if_true]
          exact (Finset.card_le_card Finset.sdiff_subset).trans_eq
            (qTrim_card G C L hMin)
        · simp [outsideSeconds, hQ]
      have hc1 := hNamed.trans hn
      have hc2 :
          (count 8 (HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
            (graphAuxArc G C L hMin) source)).toNat ≤ 8 := by
        rw [hOutsideCount]
        exact ho
      omega), hOutsideCount, aDegree_toNat G C L hG source hs]
  have hRepresented :
      (count 20 (HardCore.fullSecondNamed (graphArc G L) (graphPToZ G L)
        (graphAuxArc G C L hMin) source)).toNat + outsideSeconds.card ≤
        G.secondOutdegree v := by
    calc
      _ ≤ namedSeconds.card + outsideSeconds.card := Nat.add_le_add_right hNamed _
      _ = (namedSeconds ∪ outsideSeconds).card :=
        (Finset.card_union_of_disjoint hDisjoint).symm
      _ ≤ G.secondOutdegree v := Finset.card_le_card hUnionSub
  exact hRepresented.trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hv ↦ hNoSeymour ⟨v, hv⟩))

theorem fullNonSeymourP_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    (all 6 fun p ↦ (HardCore.fullSecondCount (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) (8 + p)).ult
        (HardCore.pDegree (graphArc G L) (graphPToZ G L) p)) = true := by
  rw [all_eq_true_iff]
  intro p hp
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  let source := 8 + p
  let v := (L.p ⟨p, hp⟩).1
  let namedSeconds := (namedVertexSet G C).filter fun w ↦
    w ∈ G.secondOutNeighborFinset v
  let outsideSeconds := G.secondOutNeighborFinset v \ namedVertexSet G C
  have hNamed := fullSecondNamed_count_le G C L hG hMin source (by omega)
  have hSourceLocal : localVertex G L source = v := by
    simp [source, v, localVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega]
  have hSourceNamed : namedVertex G C L source = v := by
    simp [namedVertex, show source < 15 by omega, hSourceLocal]
  rw [hSourceNamed] at hNamed
  change _ ≤ namedSeconds.card at hNamed
  have hOutside := fullOutsideCount_le_actual G C L hG hMin source (by omega)
  rw [hSourceLocal] at hOutside
  change _ ≤ outsideSeconds.card at hOutside
  have hNamedSub : namedSeconds ⊆ G.secondOutNeighborFinset v := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hOutsideSub : outsideSeconds ⊆ G.secondOutNeighborFinset v :=
    Finset.sdiff_subset
  have hDisjoint : Disjoint namedSeconds outsideSeconds := by
    rw [Finset.disjoint_left]
    intro w hwN hwO
    exact (Finset.mem_sdiff.mp hwO).2 (Finset.mem_filter.mp hwN).1
  have hUnionSub : namedSeconds ∪ outsideSeconds ⊆
      G.secondOutNeighborFinset v := Finset.union_subset hNamedSub hOutsideSub
  change (HardCore.fullSecondCount (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source).toNat <
    (HardCore.pDegree (graphArc G L) (graphPToZ G L) p).toNat
  rw [HardCore.fullSecondCount, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by
      have hn : namedSeconds.card ≤ 20 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr (namedEquiv G C L hG)).symm)
      have hc1 := hNamed.trans hn
      have hc2 := hOutside.trans (show outsideSeconds.card ≤
          G.secondOutdegree v by
        exact Finset.card_le_card Finset.sdiff_subset)
      have hc2' : (count 8 (HardCore.fullOutsideSecond (graphArc G L)
          (graphPToZ G L) (graphAuxArc G C L hMin) source)).toNat ≤ 8 := by
        have := BitVec.isLt (count 8 (HardCore.fullOutsideSecond (graphArc G L)
          (graphPToZ G L) (graphAuxArc G C L hMin) source))
        -- The count has only eight Boolean summands.
        rw [toNat_count_eq_fin_sum 8 _ (by omega)]
        calc
          _ ≤ ∑ _ : Fin 8, 1 := Finset.sum_le_sum (fun _ _ ↦ by
            split <;> simp)
          _ = 8 := by simp
      omega), pDegree_toNat G C L hG p hp]
  have hRepresented :
      (count 20 (HardCore.fullSecondNamed (graphArc G L) (graphPToZ G L)
        (graphAuxArc G C L hMin) source)).toNat +
        (count 8 (HardCore.fullOutsideSecond (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) source)).toNat ≤ G.secondOutdegree v := by
    calc
      _ ≤ namedSeconds.card + outsideSeconds.card := Nat.add_le_add hNamed hOutside
      _ = (namedSeconds ∪ outsideSeconds).card :=
        (Finset.card_union_of_disjoint hDisjoint).symm
      _ ≤ G.secondOutdegree v := Finset.card_le_card hUnionSub
  exact hRepresented.trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hv ↦ hNoSeymour ⟨v, hv⟩))

theorem fullNonSeymour_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    HardCore.fullNonSeymour (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  rw [HardCore.fullNonSeymour, Bool.and_eq_true]
  exact ⟨fullNonSeymourA_true G C L hG hMin hNoSeymour,
    fullNonSeymourP_true G C L hG hMin hNoSeymour⟩

theorem innerSecond_true_mem (C : G.LocalConfiguration) (L : Labels G 5 C)
    (source target : Nat) (hs : source < 8) (ht : target < 8)
    (hSecond : innerSecond (graphArc G L) source target = true) :
    (L.a ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1 := by
  simp only [innerSecond, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNot⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 8 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [aArc, graphArc_A G L source target hs ht] at hNot
  rw [aArc, graphArc_A G L source middle hs hm] at hFirst
  rw [aArc, graphArc_A G L middle target hm ht] at hLast
  have hneV : (L.a ⟨target, ht⟩).1 ≠ (L.a ⟨source, hs⟩).1 := by
    intro heq
    apply hne
    exact Fin.ext_iff.mp (L.a.injective (Subtype.ext heq))
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(L.a ⟨middle, hm⟩).1, of_decide_eq_true hFirst,
    of_decide_eq_true hLast⟩, by simpa using hNot, hneV⟩

theorem innerSecondCount_le (C : G.LocalConfiguration) (L : Labels G 5 C)
    (source : Nat) (hs : source < 8) :
    (innerSecondCount (graphArc G L) source).toNat ≤
      (C.A.filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1).card := by
  apply SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.count_le_filterCard
    C.A L.a _ _ (by omega)
  intro target hTarget
  exact innerSecond_true_mem G C L source target hs target.isLt hTarget

theorem hallZReached_true_mem (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v) (source z : Nat)
    (hs : source < 8) (hz : z < 5)
    (hReached : HardCore.fullHallZReached (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source z = true) :
    (L.z ⟨z, hz⟩).1 ∈
      G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1 := by
  simp only [HardCore.fullHallZReached, Bool.or_eq_true] at hReached
  have hNot : ¬G.Adj (L.a ⟨source, hs⟩).1 (L.z ⟨z, hz⟩).1 :=
    SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.A_not_adj_external
      G C hG _ _ (L.a _).2 (L.z _).2
  have hne : (L.z ⟨z, hz⟩).1 ≠ (L.a ⟨source, hs⟩).1 := by
    intro heq
    exact SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.external_not_mem_A
      G C hG _ (L.z _).2 (heq ▸ (L.a _).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  rcases hReached with hP | hQ
  · obtain ⟨p, hp, hPath⟩ := (any_eq_true_iff 6 _).mp hP
    simp only [Bool.and_eq_true] at hPath
    rw [aToP, graphArc_AP G L source p hs hp] at hPath
    rw [graphPToZ_eq G L p z hp hz] at hPath
    exact ⟨⟨(L.p ⟨p, hp⟩).1, of_decide_eq_true hPath.1,
      of_decide_eq_true hPath.2⟩, hNot, hne⟩
  · simp only [Bool.and_eq_true] at hQ
    rw [aToQ, graphArc_AQ G L source hs] at hQ
    have hLast := graphAuxArc_true_adj G C L hMin (15 + z) hQ.2
    have hTarget : namedVertex G C L (15 + z) = (L.z ⟨z, hz⟩).1 := by
      simp [namedVertex, show ¬15 + z < 15 by omega, show 15 + z < 20 by omega]
    rw [hTarget] at hLast
    exact ⟨⟨(L.q 0).1, of_decide_eq_true hQ.1, hLast⟩, hNot, hne⟩

theorem hallZCount_le (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 8) :
    (count 5 (HardCore.fullHallZReached (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) source)).toNat ≤
      ((externalTargets G C).filter fun v ↦
        v ∈ G.secondOutNeighborFinset (L.a ⟨source, hs⟩).1).card := by
  apply SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.count_le_filterCard
    (externalTargets G C) L.z _ _ (by omega)
  intro z hZ
  exact hallZReached_true_mem G C L hG hMin source z hs z.isLt hZ

theorem fullHallConditions_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    HardCore.fullHallConditions (graphArc G L) (graphPToZ G L)
      (graphAuxArc G C L hMin) = true := by
  rw [HardCore.fullHallConditions, all_eq_true_iff]
  intro source hs
  by_cases hInner : innerSeymour (graphArc G L) source = true
  · simp only [hInner, Bool.not_true, Bool.false_or,
      BitVec.ult_eq_decide, decide_eq_true_eq]
    let v := (L.a ⟨source, hs⟩).1
    let innerTargets := C.A.filter fun w ↦ w ∈ G.secondOutNeighborFinset v
    let namedTargets := (externalTargets G C).filter fun w ↦
      w ∈ G.secondOutNeighborFinset v
    let outsideTargets := if aToQ (graphArc G L) source = true then
      qOutside G C L hMin else ∅
    let hallTargets := namedTargets ∪ outsideTargets
    have hInnerCount := innerSecondCount_le G C L source hs
    change _ ≤ innerTargets.card at hInnerCount
    have hNamedCount := hallZCount_le G C L hG hMin source hs
    change _ ≤ namedTargets.card at hNamedCount
    have hOutsideSub : outsideTargets ⊆ G.secondOutNeighborFinset v := by
      by_cases hQ : aToQ (graphArc G L) source = true
      · simpa [outsideTargets, hQ, v] using
          qOutside_second G C L hG hMin source hs hQ
      · simp [outsideTargets, hQ]
    have hNamedSub : namedTargets ⊆ G.secondOutNeighborFinset v := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hInnerSub : innerTargets ⊆ G.secondOutNeighborFinset v := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hNamedOutsideDisjoint : Disjoint namedTargets outsideTargets := by
      rw [Finset.disjoint_left]
      intro w hwN hwO
      by_cases hQ : aToQ (graphArc G L) source = true
      · have hwOut : w ∈ qOutside G C L hMin := by
          simpa [outsideTargets, hQ] using hwO
        exact (Finset.mem_sdiff.mp hwOut).2 (by
          apply Finset.mem_union_right (localSet G C)
          exact (Finset.mem_filter.mp hwN).1)
      · simp [outsideTargets, hQ] at hwO
    have hHallSub : hallTargets ⊆ G.secondOutNeighborFinset v :=
      Finset.union_subset hNamedSub hOutsideSub
    have hInnerHallDisjoint : Disjoint innerTargets hallTargets := by
      rw [Finset.disjoint_left]
      intro w hwA hwHall
      rcases Finset.mem_union.mp hwHall with hwZ | hwO
      · exact SeymourEight.BSevenKThree.RSix.XFourNoRoot.GraphFacts.external_not_mem_A
          G C hG w (Finset.mem_filter.mp hwZ).1 (Finset.mem_filter.mp hwA).1
      · by_cases hQ : aToQ (graphArc G L) source = true
        · have hwOut : w ∈ qOutside G C L hMin := by
            simpa [outsideTargets, hQ] using hwO
          apply (Finset.mem_sdiff.mp hwOut).2
          apply Finset.mem_union_left (externalTargets G C)
          apply Finset.mem_union_left C.B
          exact (Finset.mem_filter.mp hwA).1
        · simp [outsideTargets, hQ] at hwO
    have hUnionSub : innerTargets ∪ hallTargets ⊆
        G.secondOutNeighborFinset v := Finset.union_subset hInnerSub hHallSub
    have hUnionCard : innerTargets.card + hallTargets.card ≤
        G.secondOutdegree v := by
      rw [← Finset.card_union_of_disjoint hInnerHallDisjoint]
      exact Finset.card_le_card hUnionSub
    have hOutsideCount :
        (count 8 fun slot ↦ aToQ (graphArc G L) source &&
          HardCore.auxOutside (graphAuxArc G C L hMin) 0 slot).toNat =
          outsideTargets.card := by
      by_cases hQ : aToQ (graphArc G L) source = true
      · have hFun : (fun slot ↦ aToQ (graphArc G L) source &&
            HardCore.auxOutside (graphAuxArc G C L hMin) 0 slot) =
            HardCore.auxOutside (graphAuxArc G C L hMin) 0 := by
          funext slot
          simp [hQ]
        rw [hFun, auxOutside_count_eq]
        · simpa [outsideTargets, hQ] using auxOutsideNeed_toNat G C L hG hMin
        · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
          rw [auxOutsideNeed_toNat G C L hG hMin]
          exact (Finset.card_le_card Finset.sdiff_subset).trans_eq
            (qTrim_card G C L hMin)
      · have hQFalse := Bool.eq_false_of_not_eq_true hQ
        simp [hQFalse, count, bitCount, outsideTargets]
    have hHallCount :
        (HardCore.fullHallCount (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) source).toNat ≤ hallTargets.card := by
      rw [HardCore.fullHallCount, BitVec.toNat_add,
        Nat.mod_eq_of_lt (by
          have hZ : namedTargets.card ≤ 5 :=
            (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
              simpa using (Fintype.card_congr L.z).symm)
          have hO : outsideTargets.card ≤ 8 := by
            by_cases hQ : aToQ (graphArc G L) source = true
            · simp only [outsideTargets, hQ, if_true]
              exact (Finset.card_le_card Finset.sdiff_subset).trans_eq
                (qTrim_card G C L hMin)
            · simp [outsideTargets, hQ]
          have hc1 := hNamedCount.trans hZ
          have hc2 : (count 8 fun slot ↦ aToQ (graphArc G L) source &&
              HardCore.auxOutside (graphAuxArc G C L hMin) 0 slot).toNat ≤ 8 := by
            rw [hOutsideCount]
            exact hO
          omega), hOutsideCount,
        Finset.card_union_of_disjoint hNamedOutsideDisjoint]
      exact Nat.add_le_add hNamedCount (le_refl _)
    have hInnerNat : (aOut (graphArc G L) source).toNat ≤
        (innerSecondCount (graphArc G L) source).toNat := by
      unfold innerSeymour at hInner
      simpa [BitVec.ule_eq_decide] using hInner
    have hB := outB_toNat G C L source hs
    have hDegree := aDegree_toNat G C L hG source hs
    have hADegree := congrArg BitVec.toNat (show
      aDegree (graphArc G L) source =
        aOut (graphArc G L) source + aBOut (graphArc G L) source by rfl)
    have hSecondStrict : G.secondOutdegree v < G.outdegree v :=
      Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun hv ↦ hNoSeymour ⟨v, hv⟩)
    have hB' : (aBOut (graphArc G L) source).toNat =
        directCount G C.B v := by
      rw [show aBOut (graphArc G L) source =
        SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.outB
          (graphArc G L) source by rfl]
      simpa [v] using hB
    have hDegreeParts : G.outdegree v =
        (aOut (graphArc G L) source).toNat +
          (aBOut (graphArc G L) source).toNat := by
      rw [← hDegree]
      rw [aDegree, BitVec.toNat_add, Nat.mod_eq_of_lt (by
        have ha : (aOut (graphArc G L) source).toNat ≤ 8 := by
          rw [show aOut (graphArc G L) source =
            SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.internalA
              (graphArc G L) source by rfl,
            internalA_toNat G C L source hs]
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
            simpa using (Fintype.card_congr L.a).symm)
        have hb : (aBOut (graphArc G L) source).toNat ≤ 7 := by
          rw [hB']
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
            have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
            have hq : C.Q.card = 1 := by simpa using (Fintype.card_congr L.q).symm
            rw [← Digraph.LocalConfiguration.P_union_Q (G := G) C,
              Finset.card_union_of_disjoint
                (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C), hp, hq])
        omega)]
    omega
  · have hInnerFalse := Bool.eq_false_of_not_eq_true hInner
    simp [hInnerFalse]

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardAuxBridge
