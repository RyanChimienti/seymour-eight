import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.HighDefect.GraphFacts

set_option linter.style.header false

namespace SeymourEight.FiveZHighDefectGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  C.A ∪ C.P ∪ C.Z

/-- The compatible `A`, `P`, and `Z` labels form one labelling of the
twenty retained vertices. -/
noncomputable def retainedLabelEquiv (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z}) :
    Fin 20 ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin 20 → {v : V // v ∈ retainedVertexSet G C} := fun i =>
    if hiA : i.val < 8 then
      ⟨(a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left C.Z (Finset.mem_union_left C.P (a ⟨i.val, hiA⟩).2)⟩
    else if hiP : i.val < 15 then
      ⟨(p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left C.Z
          (Finset.mem_union_right C.A (p ⟨i.val - 8, by omega⟩).2)⟩
    else
      ⟨(z ⟨i.val - 15, by omega⟩).1,
        Finset.mem_union_right (C.A ∪ C.P) (z ⟨i.val - 15, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAP | hvZ
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · obtain ⟨i, hi⟩ := a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega,
          show i.val + 8 < 15 by omega] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 15 by omega] using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hAPZ : Disjoint (C.A ∪ C.P) C.Z := by
      rw [Finset.disjoint_left]
      intro v hvAP hvZ
      apply (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · exact Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA)
      · exact Finset.mem_union_right ({C.s} ∪ C.A)
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have ha : C.A.card = 8 := by
      simpa using (Fintype.card_congr a).symm
    have hp : C.P.card = 7 := by
      simpa using (Fintype.card_congr p).symm
    have hz : C.Z.card = 5 := by
      simpa using (Fintype.card_congr z).symm
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp]
    rw [retainedVertexSet, Finset.card_union_of_disjoint hAPZ,
      Finset.card_union_of_disjoint hAP, ha, hp, hz]
    norm_num

@[simp]
theorem retainedLabelEquiv_val (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z}) (i : Fin 20) :
    (retainedLabelEquiv G C a p z i).1 =
      labelledVertex (fun j ↦ (a j).1) (fun j ↦ (p j).1)
        (fun j ↦ (z j).1) i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

end SeymourEight.FiveZHighDefectGraphBridge
