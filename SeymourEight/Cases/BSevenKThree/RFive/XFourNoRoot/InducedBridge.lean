import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.Assembly
import SeymourEight.Shared.InducedSeymour
import SeymourEight.Cases.BSevenKTwo.RSeven.XThreeNoRoot.GraphFacts

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.InducedBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def imageEquiv {n : Nat} (vertex : Fin n → V)
    (hinj : Function.Injective vertex) :
    Fin n ≃ {v : V // v ∈ Finset.univ.map ⟨vertex, hinj⟩} := by
  let f : Fin n → {v : V // v ∈ Finset.univ.map ⟨vertex, hinj⟩} := fun i ↦
    ⟨vertex i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply hinj
    simpa [f] using congrArg Subtype.val hij
  · rintro ⟨v, hv⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hv
    refine ⟨i, Subtype.ext ?_⟩
    simpa [f] using hi

omit [Fintype V] [DecidableEq V] in
@[simp] theorem imageEquiv_val {n : Nat} (vertex : Fin n → V)
    (hinj : Function.Injective vertex) (i : Fin n) :
    (imageEquiv vertex hinj i).1 = vertex i := by
  classical
  rfl

theorem indexedInducedWitness {n : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (arc : Nat → Nat → Bool) (idx : Nat → Nat) (vertex : Fin n → V)
    (hnPos : 0 < n) (hn : n ≤ 15) (hidx : ∀ i < n, idx i < 13)
    (hidxInj : ∀ i j : Fin n, idx i = idx j → i = j)
    (hinj : Function.Injective vertex)
    (hArc : ∀ i j : Fin n,
      arc (idx i) (idx j) = decide (G.Adj (vertex i) (vertex j))) :
    (any n fun source ↦
      (count n fun target ↦ arc (idx source) (idx target)).ule
      (count n fun target ↦ strictSecondLocal arc (idx source) (idx target))) = true := by
  let S : Finset V := Finset.univ.map ⟨vertex, hinj⟩
  let e := imageEquiv vertex hinj
  have hSNonempty : S.Nonempty := by
    exact ⟨vertex ⟨0, hnPos⟩, Finset.mem_map.mpr ⟨⟨0, hnPos⟩,
      Finset.mem_univ _, rfl⟩⟩
  have hSCard : S.card = n := by simp [S]
  obtain ⟨v, hvS, hv⟩ := Shared.inducedSeymour_of_card_le_fifteen
    G hBound hG S hSNonempty (by omega)
  obtain ⟨source, hsource⟩ := e.surjective ⟨v, hvS⟩
  rw [any_eq_true_iff]
  refine ⟨source, source.isLt, ?_⟩
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  have hSourceVal : vertex source = v := by
    simpa [e] using congrArg Subtype.val hsource
  have hDirect :
      (count n fun target ↦ arc (idx source) (idx target)).toNat =
        directCount G S v := by
    rw [toNat_count_eq_fin_sum n _ (by omega)]
    rw [directCount_eq_sum_bool G S e v]
    intro target
    rw [imageEquiv_val, hArc source target]
    simp [hSourceVal]
  have hSecond : (Shared.inducedSecondFinset G S v).card ≤
      (count n fun target ↦ strictSecondLocal arc (idx source)
        (idx target)).toNat := by
    have hFilter :=
      SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.GraphFacts.filterCard_le_count
        S e (fun target ↦ strictSecondLocal arc (idx source) (idx target))
        (fun w ↦ w ∈ Shared.inducedSecondFinset G S v) (by omega) (by
          intro target ht
          rw [imageEquiv_val] at ht
          rcases Finset.mem_filter.mp ht with
            ⟨_, hne, hNot, middle, hmS, hFirst, hLast⟩
          obtain ⟨middleIndex, hmEq⟩ := e.surjective ⟨middle, hmS⟩
          simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro heq
            apply hne
            have hIdxEq : target = source := hidxInj target source heq
            simp [hIdxEq, hSourceVal]
          · rw [hArc source target]
            simpa [hSourceVal] using hNot
          · rw [reachesLocal, any_eq_true_iff]
            refine ⟨idx middleIndex, hidx middleIndex middleIndex.isLt, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            have hmVal : vertex middleIndex = middle := by
              simpa [e] using congrArg Subtype.val hmEq
            refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
            · intro heq
              have : middleIndex = source := hidxInj middleIndex source heq
              have hmv : middle = v := by
                rw [← hmVal, this, hSourceVal]
              rw [hmv] at hFirst
              exact hG.1 v hFirst
            · intro heq
              have : middleIndex = target := hidxInj middleIndex target heq
              have hmw : middle = vertex target := by
                rw [← hmVal, this]
              rw [hmw] at hLast
              exact hG.1 (vertex target) hLast
            · rw [hArc source middleIndex]
              simpa [hSourceVal, hmVal] using hFirst
            · rw [hArc middleIndex target]
              simpa [hmVal] using hLast)
    have hFilterEq :
        (S.filter fun w ↦ w ∈ Shared.inducedSecondFinset G S v) =
          Shared.inducedSecondFinset G S v := by
      ext w
      simp [Shared.inducedSecondFinset]
    simpa [hFilterEq] using hFilter
  rw [hDirect]
  exact hv.trans hSecond

theorem contiguousInduced_true {zCount start size : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hSizePos : 0 < size) (hEnd : start + size ≤ 13) :
    hasContiguousInducedSeymour (graphArc G L) start size = true := by
  unfold hasContiguousInducedSeymour contiguousInducedSeymour
  apply indexedInducedWitness G hBound hG (graphArc G L) (fun i ↦ start + i)
    (fun i : Fin size ↦ labelledVertex G L (start + i)) hSizePos (by omega)
  · intro i hi
    omega
  · intro i j hij
    apply Fin.ext
    omega
  · intro i j hij
    have hFin : (⟨start + i, by omega⟩ : Fin (15 + zCount)) =
        ⟨start + j, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa using hij
    have hNat := Fin.ext_iff.mp hFin
    simp only at hNat
    apply Fin.ext
    omega
  · intro i j
    have h := coreArc_graph G C L hG (start + i) (start + j) (by omega) (by omega)
    simpa [coreArc, show start + i < 13 by omega,
      show start + j < 15 by omega] using h

theorem aOnePInduced_true {zCount : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    hasAOnePInducedSeymour (graphArc G L) = true := by
  unfold hasAOnePInducedSeymour aOnePSeymour
  apply indexedInducedWitness G hBound hG (graphArc G L) aOnePIndex
    (fun i : Fin 8 ↦ labelledVertex G L (aOnePIndex i)) (by omega) (by omega)
  · intro i hi
    simp [aOnePIndex]
    split <;> omega
  · intro i j hij
    apply Fin.ext
    simp only [aOnePIndex] at hij
    split at hij <;> split at hij <;> omega
  · intro i j hij
    have hi : aOnePIndex i < 13 := by simp [aOnePIndex]; split <;> omega
    have hj : aOnePIndex j < 13 := by simp [aOnePIndex]; split <;> omega
    have hFin : (⟨aOnePIndex i, by omega⟩ : Fin (15 + zCount)) =
        ⟨aOnePIndex j, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa using hij
    exact Fin.ext_iff.mp hFin |> fun h ↦ Fin.ext (by
      simp only [aOnePIndex] at h ⊢
      split at h <;> split at h <;> omega)
  · intro i j
    have hi : aOnePIndex i < 13 := by simp [aOnePIndex]; split <;> omega
    have hj : aOnePIndex j < 13 := by simp [aOnePIndex]; split <;> omega
    have h := coreArc_graph G C L hG (aOnePIndex i) (aOnePIndex j) hi (by omega)
    simpa [coreArc, hi, show aOnePIndex j < 15 by omega] using h

theorem inducedConditions_true {zCount : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented) :
    hasContiguousInducedSeymour (graphArc G L) 8 5 = true ∧
    hasAOnePInducedSeymour (graphArc G L) = true ∧
    hasContiguousInducedSeymour (graphArc G L) 1 12 = true ∧
    hasContiguousInducedSeymour (graphArc G L) 0 13 = true := by
  exact ⟨contiguousInduced_true G hBound C L hG (by omega) (by omega),
    aOnePInduced_true G hBound C L hG,
    contiguousInduced_true G hBound C L hG (by omega) (by omega),
    contiguousInduced_true G hBound C L hG (by omega) (by omega)⟩

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.InducedBridge
