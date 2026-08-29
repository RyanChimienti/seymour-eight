import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Counts
import SeymourEight.DegreeEight

set_option linter.style.header false

namespace SeymourEight.ThreeZHighDefectGraphBridge

open ThreeZHighDefect ThreeZHighDefectBridge FiveZExactGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem secondFromA_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 → V) (r : Fin 2 → V)
    (z : Fin 3 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 5, (a ⟨i + 1, by omega⟩).1 = h i)
    (hAR : ∀ i : Fin 2, (a ⟨i + 6, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 2, ¬G.Adj (p i).1 (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 3, ¬G.Adj (a i).1 (z j).1)
    (source target : Nat) (hs : source < 15) (ht : target < 18)
    (hSecond : secondFromA
      (coreBits G.Adj (fun i ↦ (p i).1) h r (fun i ↦ (z i).1)
        (fun i ↦ (a i).1)) source target = true) :
    labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
      (fun i ↦ (z i).1) target ∈
        G.secondOutNeighborFinset
          (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
            (fun i ↦ (z i).1) source) := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r
    (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  simp only [secondFromA, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hNotArcBool⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩, hSecondBool⟩
  have hFirst : G.Adj
      (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) source)
      (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) middle) := by
    rw [coreArc_coreBits G (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      hA0P hP0 hAH hAR hPR hAZ source middle (by omega) (by omega)] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj
      (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) middle)
      (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) target) := by
    rw [coreArc_coreBits G (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      hA0P hP0 hAH hAR hPR hAZ middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj
      (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) source)
      (labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) target) := by
    rw [coreArc_coreBits G (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      hA0P hP0 hAH hAR hPR hAZ source target (by omega) ht] at hNotArcBool
    simpa using hNotArcBool
  have hVertexNe :
      labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) target ≠
      labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
        (fun i ↦ (z i).1) source := by
    intro heq
    let e := retainedLabelEquiv G C a p z
    have hFin : (⟨target, ht⟩ : Fin 18) = ⟨source, by omega⟩ := by
      apply e.injective
      apply Subtype.ext
      simpa [e, retainedLabelEquiv_val] using heq
    exact hTargetNe (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, hFirst, hSecond'⟩, hNotArc, hVertexNe⟩

theorem aNonSeymour_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 → V) (r : Fin 2 → V)
    (z : Fin 3 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 5, (a ⟨i + 1, by omega⟩).1 = h i)
    (hAR : ∀ i : Fin 2, (a ⟨i + 6, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 2, ¬G.Adj (p i).1 (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 3, ¬G.Adj (a i).1 (z j).1)
    (source : Nat) (hs : source < 15) :
    aNonSeymour (coreBits G.Adj (fun i ↦ (p i).1) h r
      (fun i ↦ (z i).1) (fun i ↦ (a i).1)) source = true := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) h r
    (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  let e := retainedLabelEquiv G C a p z
  let u := labelledVertex (fun i ↦ (a i).1) (fun i ↦ (p i).1)
    (fun i ↦ (z i).1) source
  have hRep : (aSecondCount bits source).toNat ≤ G.secondOutdegree u := by
    have hFiltered := count_le_filterCard (V := V) (retainedVertexSet G C) e
      (secondFromA bits source) (fun v ↦ v ∈ G.secondOutNeighborFinset u)
      (by omega) (by
        intro j hj
        rw [retainedLabelEquiv_val]
        exact secondFromA_true_mem G C p h r z a hA0P hP0 hAH hAR hPR hAZ
          source j hs j.isLt hj)
    unfold Digraph.secondOutdegree
    apply hFiltered.trans
    apply Finset.card_le_card
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hStrict : G.secondOutdegree u < G.outdegree u :=
    Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hS ↦ hNoSeymour ⟨u, hS⟩)
  have hDegree := coreOutdegree_coreBits_toNat G C hG hPB hEpsilon p h r z a
    hA0P hP0 hAH hAR hPR hAZ source (by omega)
  simp only [aNonSeymour, BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [hDegree]
  exact hRep.trans_lt hStrict

end SeymourEight.ThreeZHighDefectGraphBridge
