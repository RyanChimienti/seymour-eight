import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.HighDefect.GraphFacts

set_option linter.style.header false

namespace SeymourEight.ThreeZHighDefectGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  C.A ∪ C.P ∪ C.Z

/-- The compatible `A`, `P`, and `Z` labels form one labelling of the
eighteen retained vertices. -/
noncomputable def retainedLabelEquiv (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 3 ≃ {v : V // v ∈ C.Z}) :
    Fin 18 ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin 18 → {v : V // v ∈ retainedVertexSet G C} := fun i =>
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
    have hz : C.Z.card = 3 := by
      simpa using (Fintype.card_congr z).symm
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp]
    rw [retainedVertexSet, Finset.card_union_of_disjoint hAPZ,
      Finset.card_union_of_disjoint hAP, ha, hp, hz]
    rfl

@[simp]
theorem retainedLabelEquiv_val (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 3 ≃ {v : V // v ∈ C.Z}) (i : Fin 18) :
    (retainedLabelEquiv G C a p z i).1 =
      labelledVertex (fun j ↦ (a j).1) (fun j ↦ (p j).1)
        (fun j ↦ (z j).1) i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

/-! Compatible orderings of `H = A₁ ∪ X` and `A = {a₁} ∪ H ∪ R`. -/

noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5)
    (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    Fin 5 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 5 → {v : V // v ∈ C.H} := fun i =>
    if hi : i.val = 0 then
      ⟨(eA1 0).1, Finset.mem_union_left C.X (eA1 0).2⟩
    else
      ⟨(eX ⟨i.val - 1, by omega⟩).1,
        Finset.mem_union_right C.A1 (eX ⟨i.val - 1, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    rcases Finset.mem_union.mp v.2 with hvA1 | hvX
    · obtain ⟨i, hi⟩ := eA1.surjective ⟨v.1, hvA1⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := eX.surjective ⟨v.1, hvX⟩
      refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show i.val + 1 ≠ 0 by omega] using congrArg Subtype.val hi
  · simp [hHCard]

@[simp] theorem hLabelEquiv_zero (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 0).1 = (eA1 0).1 := by rfl

@[simp] theorem hLabelEquiv_one (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 1).1 = (eX 0).1 := by rfl

@[simp] theorem hLabelEquiv_two (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 2).1 = (eX 1).1 := by rfl

@[simp] theorem hLabelEquiv_three (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 3).1 = (eX 2).1 := by rfl

@[simp] theorem hLabelEquiv_four (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5) (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 4).1 = (eX 3).1 := by rfl

noncomputable def aLabelEquiv (C : G.LocalConfiguration)
    (hACard : C.A.card = 8)
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i =>
    if hi0 : i.val = 0 then ⟨C.a1, C.a1_mem_root_outNeighbors⟩
    else if hiH : i.val ≤ 5 then
      ⟨(h ⟨i.val - 1, by omega⟩).1,
        Digraph.LocalConfiguration.H_subset_A (G := G) C
          (h ⟨i.val - 1, by omega⟩).2⟩
    else
      ⟨(eR ⟨i.val - 6, by omega⟩).1,
        Digraph.LocalConfiguration.R_subset_A (G := G) C
          (eR ⟨i.val - 6, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    have hvAll : v.1 ∈ (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R := by
      rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
      exact v.2
    rcases Finset.mem_union.mp hvAll with hvParts | hvR
    · rcases Finset.mem_union.mp hvParts with hvAX | hva1
      · rcases Finset.mem_union.mp hvAX with hvA1 | hvX
        · obtain ⟨i, hi⟩ := h.surjective
            ⟨v.1, Finset.mem_union_left C.X hvA1⟩
          refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show i.val + 1 ≠ 0 by omega,
            show i.val + 1 ≤ 5 by omega] using congrArg Subtype.val hi
        · obtain ⟨i, hi⟩ := h.surjective
            ⟨v.1, Finset.mem_union_right C.A1 hvX⟩
          refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show i.val + 1 ≠ 0 by omega,
            show i.val + 1 ≤ 5 by omega] using congrArg Subtype.val hi
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hva1).symm
    · obtain ⟨i, hi⟩ := eR.surjective ⟨v.1, hvR⟩
      refine ⟨⟨i.val + 6, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 6 ≤ 5 by omega] using congrArg Subtype.val hi
  · simp [hACard]

@[simp] theorem aLabelEquiv_zero (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) :
    (aLabelEquiv G C hACard h eR 0).1 = C.a1 := by rfl

@[simp] theorem aLabelEquiv_h (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) (j : Fin 5) :
    (aLabelEquiv G C hACard h eR ⟨j.val + 1, by omega⟩).1 = (h j).1 := by
  simp [aLabelEquiv,
    show j.val + 1 ≤ 5 by omega]

@[simp] theorem aLabelEquiv_r (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) (j : Fin 2) :
    (aLabelEquiv G C hACard h eR ⟨j.val + 6, by omega⟩).1 = (eR j).1 := by
  simp [aLabelEquiv,
    show ¬j.val + 6 ≤ 5 by omega, show j.val + 6 - 6 = j.val by omega]

end SeymourEight.ThreeZHighDefectGraphBridge
