import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.MicroBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.GraphBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.GraphFacts

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoRoot.MicroBridge

open Shared Shared.FiniteCore
open RSix.XTwoNoRoot
open RSix.XTwoNoRoot.Labels RSix.XTwoNoRoot.Encoding
open RSix.XTwoNoRoot.Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev bits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) : Core.Encoding := Encoding.coreBits G.Adj L

def labelledVertex {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 14 then (L.p ⟨n - 8, by omega⟩).1
  else if hnE : n < 18 then L.e ⟨n - 14, by omega⟩
  else C.s

theorem coreArc_four_graphBits (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heExt : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ ∈ externalTargets G C)
    (source target : Nat) (hs : source < 14) (ht : target < 18) :
    coreArc 4 true (bits G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  have hA0P : ∀ i : Fin 6, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 6, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i => hG.2 (hA0P i)
  have hA0Q : ¬G.Adj (L.a 0).1 q := by
    rw [L.a_zero]
    intro ha1q
    exact (Finset.mem_sdiff.mp hqQ).2
      (Finset.mem_filter.mpr
        ⟨Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ, ha1q⟩)
  have hPR : ∀ i : Fin 6, ∀ r : Fin 3,
      ¬G.Adj (L.p i).1 (L.a ⟨r + 5, by omega⟩).1 :=
    fun i r => RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
      G C _ _ (L.p i).2 (L.a_r r)
  unfold coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA, aArc_coreBits G.Adj L source target hsA htA]
      simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 14
      · rw [if_pos htP]
        unfold aToP
        by_cases hs0 : source = 0
        · subst source
          simp [hA0P, labelledVertex, htA, htP]
        by_cases hsH : source < 5
        · rw [if_neg hs0, if_pos hsH,
            hToP_coreBits G.Adj L (source - 1) (target - 8) (by omega) (by omega)]
          have hfin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          simp [labelledVertex, hsA, htA, htP, hfin]
        · rw [if_neg hs0, if_neg hsH,
            rToP_coreBits G.Adj L (source - 5) (target - 8) (by omega) (by omega)]
          have hfin : (⟨source - 5 + 5, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          simp [labelledVertex, hsA, htA, htP, hfin]
      · by_cases htq : target = 14
        · subst target
          simp only [if_neg (by omega : ¬14 < 14), Bool.true_and,
            decide_true, if_true]
          rw [aToQ_coreBits G.Adj L source hsA]
          by_cases hs0 : source = 0
          · subst source
            simp only [labelledVertex, dif_pos (by omega : 0 < 8),
              dif_neg (by omega : ¬14 < 8), dif_neg (by omega : ¬14 < 14),
              dif_pos (by omega : 14 < 18), ne_eq, not_true_eq_false]
            apply (decide_eq_false_iff_not.mpr ?_).symm
            rw [show (⟨0, hsA⟩ : Fin 8) = 0 by ext; rfl,
              show (⟨14 - 14, by omega⟩ : Fin 5) = 0 by ext; rfl, he0]
            exact hA0Q
          · simp only [labelledVertex, dif_pos hsA,
              dif_neg (by omega : ¬14 < 8), dif_neg (by omega : ¬14 < 14),
              dif_pos (by omega : 14 < 18)]
            rw [show decide (source ≠ 0 ∧ G.Adj (L.a ⟨source, hsA⟩).1 q) =
                decide (G.Adj (L.a ⟨source, hsA⟩).1 q) by
              exact Bool.decide_congr ⟨And.right, fun h => ⟨hs0, h⟩⟩]
            apply Bool.decide_congr
            rw [show (⟨14 - 14, by omega⟩ : Fin 5) = 0 by ext; rfl, he0]
        · have htExt : 14 < target := by omega
          let i : Fin 3 := ⟨target - 15, by omega⟩
          have hefin : (⟨target - 14, by omega⟩ : Fin 5) =
              ⟨i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
          have htail : L.e ⟨target - 14, by omega⟩ ∈ externalTargets G C := by
            rw [hefin]
            exact heExt i
          have hnot := RSeven.XThreeRoot.GraphFacts.A_not_adj_external
            G C hG (L.a ⟨source, hsA⟩).1
              (L.e ⟨target - 14, by omega⟩) (L.a _).2 htail
          simp only [if_neg htP, Bool.true_and,
            decide_eq_false_iff_not.mpr htq, Bool.not_true,
            Bool.false_and, labelledVertex, dif_pos hsA, dif_neg htA,
            dif_neg htP, dif_pos ht]
          exact (decide_eq_false_iff_not.mpr hnot).symm
  · have hsP : source < 14 := hs
    rw [if_neg hsA, if_pos hsP]
    by_cases htA : target < 8
    · rw [if_pos htA]
      unfold pToA
      by_cases htH : 0 < target ∧ target < 5
      · rw [if_pos (by simpa [Bool.and_eq_true] using htH),
          pToH_coreBits G.Adj L (source - 8) (target - 1) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA,
          show target - 1 + 1 = target by omega]
      · rw [if_neg (by simpa [Bool.and_eq_true] using htH)]
        have hc : target = 0 ∨ target = 5 ∨ target = 6 ∨ target = 7 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · simp [labelledVertex, hsA, hsP, hP0]
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 0
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 1
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 2
    · rw [if_neg htA]
      by_cases htP : target < 14
      · rw [if_pos htP, pArc_coreBits G.Adj L (source - 8) (target - 8)
          (by omega) (by omega)]
        have himp : G.Adj (L.p ⟨source - 8, by omega⟩).1
            (L.p ⟨target - 8, by omega⟩).1 → source - 8 ≠ target - 8 := by
          intro ha heq
          apply hG.1 (L.p ⟨source - 8, by omega⟩).1
          have hf : (⟨source - 8, by omega⟩ : Fin 6) =
              ⟨target - 8, by omega⟩ := Fin.ext heq
          simpa [hf] using ha
        rw [show decide (source - 8 ≠ target - 8 ∧
            G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) =
            decide (G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) by
          exact Bool.decide_congr ⟨And.right, fun h => ⟨himp h, h⟩⟩]
        simp [labelledVertex, hsA, hsP, htA, htP]
      · rw [if_neg htP, if_pos ht,
          pToE_coreBits G.Adj L (source - 8) (target - 14) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, htP, ht]

theorem labelledVertex_injective (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1) :
    Function.Injective (fun i : Fin 18 => labelledVertex G L i.val) := by
  have hEMem : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ ∈ E := by
    intro i
    rw [hELab i]
    exact (eEq i).2
  have hAP : Disjoint C.A C.P := by
    exact (Digraph.LocalConfiguration.disjoint_A_B (G := G) C).mono_right
      (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  have hAE : Disjoint C.A E := by
    rw [hE, Finset.disjoint_left]
    intro v hvA hvE
    rcases Finset.mem_union.mp hvE with hvq | hvExt
    · have hv : v = q := Finset.mem_singleton.mp hvq
      subst v
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
    · rcases Finset.mem_union.mp hvExt with hvZ | hvRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
            (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
      · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
        · have hvEq : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
        · simp [rootSecondFinset, hReach] at hvRoot
  have hPE : Disjoint C.P E := by
    rw [hE, Finset.disjoint_left]
    intro v hvP hvE
    rcases Finset.mem_union.mp hvE with hvq | hvExt
    · have hv : v = q := Finset.mem_singleton.mp hvq
      subst v
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP hqQ
    · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExt
  intro i j hij
  apply Fin.ext
  by_cases hiA : i.val < 8
  · by_cases hjA : j.val < 8
    · have haEq : L.a ⟨i.val, hiA⟩ = L.a ⟨j.val, hjA⟩ := by
        apply Subtype.ext
        simpa [labelledVertex, hiA, hjA] using hij
      have hv := Fin.ext_iff.mp (L.a.injective haEq)
      exact hv
    · by_cases hjP : j.val < 14
      · exfalso
        have heq : (L.a ⟨i.val, hiA⟩).1 =
            (L.p ⟨j.val - 8, by omega⟩).1 := by
          simpa [labelledVertex, hiA, hjA, hjP] using hij
        exact (Finset.disjoint_left.mp hAP) (L.a ⟨i.val, hiA⟩).2
          (heq ▸ (L.p _).2)
      · exfalso
        have heq : (L.a ⟨i.val, hiA⟩).1 = L.e ⟨j.val - 14, by omega⟩ := by
          simpa [labelledVertex, hiA, hjA, hjP, j.isLt] using hij
        exact (Finset.disjoint_left.mp hAE) (L.a _).2
          (heq ▸ hEMem ⟨j.val - 14, by omega⟩)
  · by_cases hiP : i.val < 14
    · by_cases hjA : j.val < 8
      · exfalso
        have heq : (L.p ⟨i.val - 8, by omega⟩).1 = (L.a ⟨j.val, hjA⟩).1 := by
          simpa [labelledVertex, hiA, hiP, hjA] using hij
        exact (Finset.disjoint_left.mp hAP) (heq ▸ (L.a _).2) (L.p _).2
      · by_cases hjP : j.val < 14
        · have hpEq : L.p ⟨i.val - 8, by omega⟩ =
              L.p ⟨j.val - 8, by omega⟩ := by
            apply Subtype.ext
            simpa [labelledVertex, hiA, hiP, hjA, hjP] using hij
          have hv := Fin.ext_iff.mp (L.p.injective hpEq)
          change i.val - 8 = j.val - 8 at hv
          omega
        · exfalso
          have heq : (L.p ⟨i.val - 8, by omega⟩).1 =
              L.e ⟨j.val - 14, by omega⟩ := by
            simpa [labelledVertex, hiA, hiP, hjA, hjP, j.isLt] using hij
          exact (Finset.disjoint_left.mp hPE) (L.p _).2
            (heq ▸ hEMem ⟨j.val - 14, by omega⟩)
    · by_cases hjA : j.val < 8
      · exfalso
        have heq : L.e ⟨i.val - 14, by omega⟩ = (L.a ⟨j.val, hjA⟩).1 := by
          simpa [labelledVertex, hiA, hiP, i.isLt, hjA] using hij
        exact (Finset.disjoint_left.mp hAE) (heq ▸ (L.a _).2)
          (hEMem ⟨i.val - 14, by omega⟩)
      · by_cases hjP : j.val < 14
        · exfalso
          have heq : L.e ⟨i.val - 14, by omega⟩ =
              (L.p ⟨j.val - 8, by omega⟩).1 := by
            simpa [labelledVertex, hiA, hiP, i.isLt, hjA, hjP] using hij
          exact (Finset.disjoint_left.mp hPE) (heq ▸ (L.p _).2)
            (hEMem ⟨i.val - 14, by omega⟩)
        · let ei : Fin 4 := ⟨i.val - 14, by omega⟩
          let ej : Fin 4 := ⟨j.val - 14, by omega⟩
          have heqL : L.e ⟨i.val - 14, by omega⟩ =
              L.e ⟨j.val - 14, by omega⟩ := by
            simpa [labelledVertex, hiA, hiP, i.isLt, hjA, hjP, j.isLt] using hij
          have heq : eEq ei = eEq ej := by
            apply Subtype.ext
            rw [← hELab ei, ← hELab ej]
            simpa [ei, ej] using heqL
          have hv := Fin.ext_iff.mp (eEq.injective heq)
          change i.val - 14 = j.val - 14 at hv
          omega

omit [Fintype V] [DecidableEq V] in
private theorem count_le_card_of_injective {n : Nat} (f : Nat → Bool)
    (label : Fin n → V) (S : Finset V) (hn : n < 256)
    (hinj : Function.Injective label)
    (hmem : ∀ i : Fin n, f i = true → label i ∈ S) :
    (count n f).toNat ≤ S.card := by
  classical
  let selected : Finset (Fin n) := Finset.univ.filter fun i => f i = true
  have hCard : selected.card = (count n f).toNat := by
    rw [toNat_count_eq_fin_sum n f hn]
    simp only [selected, Finset.card_filter]
  have hImageCard : (selected.image label).card = selected.card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hinj hab
  have hSubset : selected.image label ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact hmem i (Finset.mem_filter.mp hi).2
  rw [← hCard, ← hImageCard]
  exact Finset.card_le_card hSubset

theorem localSecondCount_four_le_graph (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heExt : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ ∈ externalTargets G C)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (source : Nat) (hs : source < 14) :
    (localSecondCount 4 true (bits G L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  have hinj := labelledVertex_injective G C q hqQ L hG E hE eEq hELab
  have hmem : ∀ i : Fin 18,
      strictSecondLocal 4 true (bits G L) source i.val = true →
        labelledVertex G L i.val ∈
          G.secondOutNeighborFinset (labelledVertex G L source) := by
    intro i hSecond
    simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
    rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
    obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 14 _).mp hReach
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
    rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
    rw [coreArc_four_graphBits G C q hqQ L hG he0 heExt source middle hs
      (by omega)] at hFirst
    rw [coreArc_four_graphBits G C q hqQ L hG he0 heExt middle i.val hm
      i.isLt] at hLast
    rw [coreArc_four_graphBits G C q hqQ L hG he0 heExt source i.val hs
      i.isLt] at hNotArc
    have hVertexNe : labelledVertex G L i.val ≠ labelledVertex G L source := by
      intro heq
      have hFin : i = ⟨source, by omega⟩ := hinj (by simpa using heq)
      exact (by simp [hFin] at hne)
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
      by simpa using hNotArc, hVertexNe⟩
  unfold localSecondCount Digraph.secondOutdegree
  exact count_le_card_of_injective
    (fun i => strictSecondLocal 4 true (bits G L) source i)
    (fun i : Fin 18 => labelledVertex G L i.val)
    (G.secondOutNeighborFinset (labelledVertex G L source)) (by omega)
    hinj hmem

theorem inactive_last (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hDummy : L.e 4 = (L.a 5).1)
    (source : Nat) (_hs : source < 14) :
    strictSecondLocal 5 true (bits G L) source 18 = false := by
  have hIncoming : ∀ middle, middle < 14 →
      coreArc 5 true (bits G L) middle 18 = false := by
    intro middle hm
    by_cases hmA : middle < 8
    · simp [coreArc, hmA]
    · have hmP : middle < 14 := hm
      rw [coreArc, if_neg hmA, if_pos hmP, if_neg (by omega : ¬18 < 8),
        if_neg (by omega : ¬18 < 14), if_pos (by omega : 18 < 19),
        pToE_coreBits G.Adj L (middle - 8) 4 (by omega) (by omega)]
      have he4 : (⟨4, by omega⟩ : Fin 5) = 4 := rfl
      rw [he4, hDummy]
      exact decide_eq_false
        (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
          G C (L.p ⟨middle - 8, by omega⟩).1 (L.a 5).1
            (L.p _).2 (L.a_r 0))
  simp only [strictSecondLocal, reachesLocal]
  have hAny : any 14 (fun middle => decide ((middle != source) = true) &&
      decide ((middle != 18) = true) && coreArc 5 true (bits G L) source middle &&
        coreArc 5 true (bits G L) middle 18) = false := by
    apply Bool.eq_false_iff.mpr
    intro hTrue
    obtain ⟨middle, hm, hMiddle⟩ := (any_eq_true_iff 14 _).mp hTrue
    simp [hIncoming middle hm] at hMiddle
  rw [hAny]
  simp

theorem localSecondCount_five_toNat_eq_four (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hDummy : L.e 4 = (L.a 5).1)
    (source : Nat) (hs : source < 14) :
    (localSecondCount 5 true (bits G L) source).toNat =
      (localSecondCount 4 true (bits G L) source).toNat := by
  simp only [localSecondCount]
  norm_num [vertexCount]
  rw [toNat_count 19 _ (by omega), toNat_count 18 _ (by omega)]
  rw [Finset.sum_range_succ]
  have hCore : ∀ u < 14, ∀ v < 18,
      coreArc 5 true (bits G L) u v = coreArc 4 true (bits G L) u v := by
    intro u hu v hv
    simp [coreArc, hu, hv, show v < 19 by omega]
  have hSame : ∀ i < 18,
      strictSecondLocal 5 true (bits G L) source i =
        strictSecondLocal 4 true (bits G L) source i := by
    intro i hi
    simp only [strictSecondLocal, reachesLocal]
    rw [hCore source hs i hi]
    have hAnyIff :
        any 14 (fun middle => decide ((middle != source) = true) &&
          decide ((middle != i) = true) && coreArc 5 true (bits G L) source middle &&
            coreArc 5 true (bits G L) middle i) = true ↔
        any 14 (fun middle => decide ((middle != source) = true) &&
          decide ((middle != i) = true) && coreArc 4 true (bits G L) source middle &&
            coreArc 4 true (bits G L) middle i) = true := by
      rw [any_eq_true_iff, any_eq_true_iff]
      constructor <;> rintro ⟨middle, hm, hmiddle⟩ <;>
        refine ⟨middle, hm, ?_⟩
      · simpa [hCore source hs middle (by omega), hCore middle hm i hi] using hmiddle
      · simpa [hCore source hs middle (by omega), hCore middle hm i hi] using hmiddle
    have hAny :
        any 14 (fun middle => decide ((middle != source) = true) &&
          decide ((middle != i) = true) && coreArc 5 true (bits G L) source middle &&
            coreArc 5 true (bits G L) middle i) =
        any 14 (fun middle => decide ((middle != source) = true) &&
          decide ((middle != i) = true) && coreArc 4 true (bits G L) source middle &&
            coreArc 4 true (bits G L) middle i) := by
      cases h5 : any 14 (fun middle => decide ((middle != source) = true) &&
          decide ((middle != i) = true) && coreArc 5 true (bits G L) source middle &&
            coreArc 5 true (bits G L) middle i) <;>
        cases h4 : any 14 (fun middle => decide ((middle != source) = true) &&
          decide ((middle != i) = true) && coreArc 4 true (bits G L) source middle &&
            coreArc 4 true (bits G L) middle i) <;> simp_all
    rw [hAny]
  have hHead : (∑ x ∈ Finset.range 18,
      (bitCount (strictSecondLocal 5 true (bits G L) source x)).toNat) =
      ∑ x ∈ Finset.range 18,
        (bitCount (strictSecondLocal 4 true (bits G L) source x)).toNat := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hSame i (Finset.mem_range.mp hi)]
  rw [hHead, inactive_last G C q L hDummy source hs]
  simp [bitCount]

theorem pDirectFour_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (p : Nat) (hp : p < 6) :
    (pOut (bits G L) p + pHOut (bits G L) p + pEOut 4 (bits G L) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hBlocks := XTwoNoRoot.GraphBridge.pBlockCounts G C q L hG hHCard E eEq
    (by omega) hELab p hp
  have hBlocks' :
      (pOut (bits G L) p).toNat = Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ∧
      (pHOut (bits G L) p).toNat = Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ∧
      (pEOut 4 (bits G L) p).toNat = Shared.directCount G E (L.p ⟨p, hp⟩).1 := by
    exact hBlocks
  have hDegree := XTwoRoot.GraphBridge.P_outdegree_eq_blocks
    G C q hqQ hQ hG (L.p ⟨p, hp⟩).1 (L.p _).2
  simp only [BitVec.toNat_add]
  rw [hBlocks'.1, hBlocks'.2.1, hBlocks'.2.2]
  have hSmall : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G E (L.p ⟨p, hp⟩).1 < 256 := by
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have h1 := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.P)
    have h2 := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.H)
    have h3 := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) E)
    change Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at h1
    change Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at h2
    change Shared.directCount G E (L.p ⟨p, hp⟩).1 ≤ E.card at h3
    have hECard : E.card = 4 := by simpa using (Fintype.card_congr eEq).symm
    omega
  have hSmallPH : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 < 256 := by omega
  rw [Nat.mod_eq_of_lt hSmallPH, Nat.mod_eq_of_lt hSmall]
  rw [hE]
  exact hDegree.symm

theorem pDirectCore_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (p : Nat) (hp : p < 6) :
    (pOut (bits G L) p + pHOut (bits G L) p + pEOut 5 (bits G L) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hBlocks := XTwoNoRoot.GraphBridge.pBlockCounts G C q L hG hHCard E eEq
    (by omega) hELab p hp
  have hBlocks' :
      (pOut (bits G L) p).toNat = Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ∧
      (pHOut (bits G L) p).toNat = Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ∧
      (pEOut 5 (bits G L) p).toNat = Shared.directCount G E (L.p ⟨p, hp⟩).1 := by
    exact hBlocks
  have hDegree := XTwoRoot.GraphBridge.P_outdegree_eq_blocks
    G C q hqQ hQ hG (L.p ⟨p, hp⟩).1 (L.p _).2
  simp only [BitVec.toNat_add]
  rw [hBlocks'.1, hBlocks'.2.1, hBlocks'.2.2]
  have hSmall : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 +
      Shared.directCount G E (L.p ⟨p, hp⟩).1 < 256 := by
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have h1 := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.P)
    have h2 := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) C.H)
    have h3 := Finset.card_le_card
      (Finset.filter_subset (G.Adj (L.p ⟨p, hp⟩).1) E)
    change Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card at h1
    change Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card at h2
    change Shared.directCount G E (L.p ⟨p, hp⟩).1 ≤ E.card at h3
    have hECard : E.card = 5 := by simpa using (Fintype.card_congr eEq).symm
    omega
  have hSmallPH : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 +
      Shared.directCount G C.H (L.p ⟨p, hp⟩).1 < 256 := by omega
  rw [Nat.mod_eq_of_lt hSmallPH, Nat.mod_eq_of_lt hSmall]
  rw [hE]
  exact hDegree.symm

theorem all_pMicroNonSeymourCore_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (c : Nat) : all 6 (pMicroNonSeymourCore c (bits G L)) = true := by
  have heInj : Function.Injective L.e := by
    intro i j hij
    apply eEq.injective
    apply Subtype.ext
    simpa [hELab] using hij
  have hNoHLoop :=
    (XTwoNoRoot.MicroScratch.structural_no_arcs_graphBits G C q L hG).2
  rw [all_eq_true_iff]
  intro p hp
  simp only [pMicroNonSeymourCore, BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSubset := XTwoNoRoot.MicroScratch.pMicroSecondCountCore_le_local
    c (bits G L) p hp hNoHLoop
  have hLocal := XTwoNoRoot.MicroScratch.localSecondCount_lt_outdegree
    G C q hqQ L hG he0 heZ heInj hNoSeymour (8 + p) (by omega)
  have hLabel : XTwoNoRoot.MicroScratch.labelledVertex G L (8 + p) =
      (L.p ⟨p, hp⟩).1 := by
    simp [XTwoNoRoot.MicroScratch.labelledVertex,
      show ¬8 + p < 8 by omega, show 8 + p < 14 by omega]
  rw [hLabel] at hLocal
  rw [pDirectCore_toNat G C q hqQ hQ L hG hHCard E hE eEq hELab p hp]
  exact hSubset.trans_lt hLocal

theorem all_hRestrictedNonSeymourFour_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (he0 : L.e 0 = q)
    (heExt : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ ∈ externalTargets G C)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (hDummy : L.e 4 = (L.a 5).1) (c : Nat) :
    all 4 (hRestrictedNonSeymourFour c (bits G L)) = true := by
  have hFixed := XTwoNoRoot.MicroScratch.fixedA_graphBits_true G C q L hG
  have hStruct := XTwoNoRoot.MicroScratch.structural_no_arcs_graphBits G C q L hG
  rw [all_eq_true_iff]
  intro h hh
  simp only [hRestrictedNonSeymourFour, BitVec.ult_eq_decide,
    decide_eq_true_eq]
  have hFourCore := XTwoNoRoot.MicroScratch.hRestrictedSecondCountFour_le_core
    c (bits G L) h
  have hSubset := XTwoNoRoot.MicroScratch.hRestrictedSecondCountCore_le_local
    c (bits G L) h hh hFixed hStruct.1 hStruct.2
  have hLocal := localSecondCount_four_le_graph G C q hqQ L hG he0 heExt
    E hE eEq hELab (1 + h) (by omega)
  have hEq := localSecondCount_five_toNat_eq_four G C q L hDummy (1 + h)
    (by omega)
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨(L.a ⟨h + 1, by omega⟩).1, hs⟩)
  have hDirect := XTwoNoRoot.GraphBridge.hDirectCore_toNat G C q hqQ hQ L hG
    hHCard hRCard h hh
  have hDirect' : (hDirectCore 0 (bits G L) h).toNat =
      G.outdegree (L.a ⟨h + 1, by omega⟩).1 := by
    exact hDirect
  change (hRestrictedSecondCountFour c (bits G L) h).toNat <
    (hDirectCore c (bits G L) h).toNat
  have hc : hDirectCore c (bits G L) h = hDirectCore 0 (bits G L) h := rfl
  rw [hc, hDirect']
  have hLabel : labelledVertex G L (1 + h) = (L.a ⟨h + 1, by omega⟩).1 := by
    unfold labelledVertex
    rw [dif_pos (by omega : 1 + h < 8)]
    have hfin : (⟨1 + h, by omega⟩ : Fin 8) = ⟨h + 1, by omega⟩ :=
      Fin.ext (Nat.add_comm 1 h)
    rw [hfin]
  rw [hLabel] at hLocal
  exact hFourCore.trans hSubset |>.trans_eq hEq |>.trans hLocal |>.trans_lt hNS

theorem all_pMicroNonSeymourFour_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (he0 : L.e 0 = q)
    (heExt : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ ∈ externalTargets G C)
    (hDummy : L.e 4 = (L.a 5).1) (c : Nat) :
    all 6 (pMicroNonSeymourFour c (bits G L)) = true := by
  have hNoHLoop :=
    (XTwoNoRoot.MicroScratch.structural_no_arcs_graphBits G C q L hG).2
  rw [all_eq_true_iff]
  intro p hp
  simp only [pMicroNonSeymourFour, BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSubset := XTwoNoRoot.MicroScratch.pMicroSecondCountCore_le_local
    c (bits G L) p hp hNoHLoop
  have hEq := localSecondCount_five_toNat_eq_four G C q L hDummy (8 + p)
    (by omega)
  have hLocal := localSecondCount_four_le_graph G C q hqQ L hG he0 heExt
    E hE eEq hELab (8 + p) (by omega)
  have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨(L.p ⟨p, hp⟩).1, hs⟩)
  rw [pDirectFour_toNat G C q hqQ hQ L hG hHCard E hE eEq hELab p hp]
  have hLabel : labelledVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega]
  rw [hLabel] at hLocal
  exact hSubset.trans_eq hEq |>.trans hLocal |>.trans_lt hNS

end SeymourEight.BSevenKTwo.RSix.XTwoRoot.MicroBridge
