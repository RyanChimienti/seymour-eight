import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGlobalBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.TerminalCoreGraphBridge

set_option linter.style.header false

/-!
# Compatible labels for the exact five-`Z` core

The finite predicate uses one common ordering of `H` inside both the `H`
incidence matrices and the eight-vertex ordering of `A`.  These equivalences
construct that ordering from labels of the disjoint local pieces.
-/

namespace SeymourEight.FiveZExactLabels

open Shared FiveZExactGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Label `H=A1∪X` with its unique `A1` member first. -/
noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (hHCard : C.H.card = 3)
    (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) :
    Fin 3 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 3 → {v : V // v ∈ C.H} := fun i =>
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

@[simp]
theorem hLabelEquiv_zero (C : G.LocalConfiguration)
    (hHCard : C.H.card = 3)
    (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 0).1 = (eA1 0).1 := by
  rfl

@[simp]
theorem hLabelEquiv_one (C : G.LocalConfiguration)
    (hHCard : C.H.card = 3)
    (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 1).1 = (eX 0).1 := by
  rfl

@[simp]
theorem hLabelEquiv_two (C : G.LocalConfiguration)
    (hHCard : C.H.card = 3)
    (eA1 : Fin 1 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) :
    (hLabelEquiv G C hHCard eA1 eX 2).1 = (eX 1).1 := by
  rfl

/-- Label `A` as `a1`, then the three labels of `H`, then the four labels of
`R`. -/
noncomputable def aLabelEquiv (C : G.LocalConfiguration)
    (hACard : C.A.card = 8)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (eR : Fin 4 ≃ {v : V // v ∈ C.R}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i =>
    if hi0 : i.val = 0 then ⟨C.a1, C.a1_mem_root_outNeighbors⟩
    else if hiH : i.val ≤ 3 then
      ⟨(h ⟨i.val - 1, by omega⟩).1,
        Digraph.LocalConfiguration.H_subset_A (G := G) C
          (h ⟨i.val - 1, by omega⟩).2⟩
    else
      ⟨(eR ⟨i.val - 4, by omega⟩).1,
        Digraph.LocalConfiguration.R_subset_A (G := G) C
          (eR ⟨i.val - 4, by omega⟩).2⟩
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
        · have hvH : v.1 ∈ C.H := Finset.mem_union_left C.X hvA1
          obtain ⟨i, hi⟩ := h.surjective ⟨v.1, hvH⟩
          refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show i.val + 1 ≠ 0 by omega,
            show i.val + 1 ≤ 3 by omega] using congrArg Subtype.val hi
        · have hvH : v.1 ∈ C.H := Finset.mem_union_right C.A1 hvX
          obtain ⟨i, hi⟩ := h.surjective ⟨v.1, hvH⟩
          refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show i.val + 1 ≠ 0 by omega,
            show i.val + 1 ≤ 3 by omega] using congrArg Subtype.val hi
      · have hvEq : v.1 = C.a1 := Finset.mem_singleton.mp hva1
        refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using hvEq.symm
    · obtain ⟨i, hi⟩ := eR.surjective ⟨v.1, hvR⟩
      refine ⟨⟨i.val + 4, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 4 ≤ 3 by omega] using congrArg Subtype.val hi
  · simp [hACard]

@[simp]
theorem aLabelEquiv_zero (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (eR : Fin 4 ≃ {v : V // v ∈ C.R}) :
    (aLabelEquiv G C hACard h eR 0).1 = C.a1 := by
  rfl

@[simp]
theorem aLabelEquiv_h (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (eR : Fin 4 ≃ {v : V // v ∈ C.R}) (j : Fin 3) :
    (aLabelEquiv G C hACard h eR ⟨j.val + 1, by omega⟩).1 = (h j).1 := by
  simp [aLabelEquiv,
    show j.val + 1 ≤ 3 by omega]

@[simp]
theorem aLabelEquiv_r (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (eR : Fin 4 ≃ {v : V // v ∈ C.R}) (j : Fin 4) :
    (aLabelEquiv G C hACard h eR ⟨j.val + 4, by omega⟩).1 = (eR j).1 := by
  simp [aLabelEquiv,
    show ¬j.val + 4 ≤ 3 by omega, show j.val + 4 - 4 = j.val by omega]

/-- Relabel any `n`-element finset so a chosen member has label zero. -/
noncomputable def finsetEquivFinAtZero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    Fin n ≃ {w : V // w ∈ S} :=
  let e := finsetEquivFin S hCard
  (Equiv.swap ⟨0, hn⟩ (e.symm ⟨v, hv⟩)).trans e

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZero_zero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    (finsetEquivFinAtZero S hn hCard v hv ⟨0, hn⟩).1 = v := by
  classical
  simp [finsetEquivFinAtZero]

omit [Fintype V] in
/-- From a six- or seven-element union, select six vertices while retaining
every vertex in its intersection with a three-element set. -/
theorem exists_six_subset_containing_inter (W H : Finset V)
    (hWCard : W.card = 6 ∨ W.card = 7) (hHCard : H.card = 3) :
    ∃ S : Finset V, S ⊆ W ∧ S.card = 6 ∧ W ∩ H ⊆ S := by
  classical
  rcases hWCard with hSix | hSeven
  · exact ⟨W, fun _ h ↦ h, hSix,
      fun _ h ↦ (Finset.mem_inter.mp h).1⟩
  · have hOutside : ∃ v ∈ W, v ∉ H := by
      by_contra hNot
      push Not at hNot
      have hSubset : W ⊆ H := fun v hv ↦ hNot v hv
      have := Finset.card_le_card hSubset
      omega
    obtain ⟨v, hvW, hvH⟩ := hOutside
    refine ⟨W.erase v, Finset.erase_subset _ _, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hvW, hSeven]
    · intro u hu
      rw [Finset.mem_erase]
      have hu' := Finset.mem_inter.mp hu
      refine ⟨?_, hu'.1⟩
      intro huv
      subst u
      exact hvH hu'.2

/-- Relabel an `n`-element finset so two distinct chosen members have labels
zero and one. -/
noncomputable def finsetEquivFinAtZeroOne {n : Nat} (S : Finset V)
    (hn : 1 < n) (hCard : S.card = n)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (_hne : v₀ ≠ v₁) : Fin n ≃ {w : V // w ∈ S} :=
  let e₀ := finsetEquivFinAtZero S (by omega) hCard v₀ hv₀
  let i₁ := e₀.symm ⟨v₁, hv₁⟩
  (Equiv.swap ⟨1, hn⟩ i₁).trans e₀

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZeroOne_one {n : Nat} (S : Finset V)
    (hn : 1 < n) (hCard : S.card = n)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (hne : v₀ ≠ v₁) :
    (finsetEquivFinAtZeroOne S hn hCard v₀ hv₀ v₁ hv₁ hne
      ⟨1, hn⟩).1 = v₁ := by
  classical
  simp [finsetEquivFinAtZeroOne]

/-- Relabel an `n`-element finset so three pairwise-distinct chosen members
have labels zero, one, and two. -/
noncomputable def finsetEquivFinAtZeroOneTwo {n : Nat} (S : Finset V)
    (hn : 2 < n) (hCard : S.card = n)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (v₂ : V) (hv₂ : v₂ ∈ S)
    (hne01 : v₀ ≠ v₁) (_hne02 : v₀ ≠ v₂) (_hne12 : v₁ ≠ v₂) :
    Fin n ≃ {w : V // w ∈ S} :=
  let e₁ := finsetEquivFinAtZeroOne S (by omega) hCard
    v₀ hv₀ v₁ hv₁ hne01
  let i₂ := e₁.symm ⟨v₂, hv₂⟩
  (Equiv.swap ⟨2, hn⟩ i₂).trans e₁

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZeroOneTwo_two {n : Nat} (S : Finset V)
    (hn : 2 < n) (hCard : S.card = n)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (v₂ : V) (hv₂ : v₂ ∈ S)
    (hne01 : v₀ ≠ v₁) (hne02 : v₀ ≠ v₂) (hne12 : v₁ ≠ v₂) :
    (finsetEquivFinAtZeroOneTwo S hn hCard v₀ hv₀ v₁ hv₁ v₂ hv₂
      hne01 hne02 hne12 ⟨2, hn⟩).1 = v₂ := by
  classical
  simp [finsetEquivFinAtZeroOneTwo]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZeroOne_zero_six (S : Finset V)
    (hCard : S.card = 6)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (hne : v₀ ≠ v₁) :
    (finsetEquivFinAtZeroOne S (by omega) hCard v₀ hv₀ v₁ hv₁ hne 0).1 =
      v₀ := by
  classical
  let e₀ := finsetEquivFinAtZero S (by omega) hCard v₀ hv₀
  have hi₁ : e₀.symm ⟨v₁, hv₁⟩ ≠ (0 : Fin 6) := by
    intro hi
    have := congrArg (fun x ↦ (e₀ x).1) hi
    simp only [Equiv.apply_symm_apply] at this
    have hz : (e₀ 0).1 = v₀ := by
      exact finsetEquivFinAtZero_zero S (by omega) hCard v₀ hv₀
    exact hne (hz.symm.trans this.symm)
  have hSwap : (Equiv.swap (1 : Fin 6) (e₀.symm ⟨v₁, hv₁⟩)) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (fun heq ↦ hi₁ heq.symm)
  change (e₀ ((Equiv.swap 1 (e₀.symm ⟨v₁, hv₁⟩)) 0)).1 = v₀
  rw [hSwap]
  exact finsetEquivFinAtZero_zero S (by omega) hCard v₀ hv₀

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZeroOneTwo_zero_six (S : Finset V)
    (hCard : S.card = 6)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (v₂ : V) (hv₂ : v₂ ∈ S)
    (hne01 : v₀ ≠ v₁) (hne02 : v₀ ≠ v₂) (hne12 : v₁ ≠ v₂) :
    (finsetEquivFinAtZeroOneTwo S (by omega) hCard
      v₀ hv₀ v₁ hv₁ v₂ hv₂ hne01 hne02 hne12 0).1 = v₀ := by
  classical
  let e₁ := finsetEquivFinAtZeroOne S (by omega) hCard
    v₀ hv₀ v₁ hv₁ hne01
  have hi₂0 : e₁.symm ⟨v₂, hv₂⟩ ≠ (0 : Fin 6) := by
    intro hi
    have := congrArg (fun x ↦ (e₁ x).1) hi
    simp only [Equiv.apply_symm_apply] at this
    have hz : (e₁ 0).1 = v₀ := by
      exact finsetEquivFinAtZeroOne_zero_six S hCard
        v₀ hv₀ v₁ hv₁ hne01
    exact hne02 (hz.symm.trans this.symm)
  have hSwap : (Equiv.swap (2 : Fin 6) (e₁.symm ⟨v₂, hv₂⟩)) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (fun heq ↦ hi₂0 heq.symm)
  change (e₁ ((Equiv.swap 2 (e₁.symm ⟨v₂, hv₂⟩)) 0)).1 = v₀
  rw [hSwap]
  exact finsetEquivFinAtZeroOne_zero_six S hCard
    v₀ hv₀ v₁ hv₁ hne01

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFinAtZeroOneTwo_one_six (S : Finset V)
    (hCard : S.card = 6)
    (v₀ : V) (hv₀ : v₀ ∈ S) (v₁ : V) (hv₁ : v₁ ∈ S)
    (v₂ : V) (hv₂ : v₂ ∈ S)
    (hne01 : v₀ ≠ v₁) (hne02 : v₀ ≠ v₂) (hne12 : v₁ ≠ v₂) :
    (finsetEquivFinAtZeroOneTwo S (by omega) hCard
      v₀ hv₀ v₁ hv₁ v₂ hv₂ hne01 hne02 hne12 1).1 = v₁ := by
  classical
  let e₁ := finsetEquivFinAtZeroOne S (by omega) hCard
    v₀ hv₀ v₁ hv₁ hne01
  have hi₂1 : e₁.symm ⟨v₂, hv₂⟩ ≠ (1 : Fin 6) := by
    intro hi
    have := congrArg (fun x ↦ (e₁ x).1) hi
    simp only [Equiv.apply_symm_apply] at this
    have ho : (e₁ 1).1 = v₁ := by
      exact finsetEquivFinAtZeroOne_one S (by omega) hCard
        v₀ hv₀ v₁ hv₁ hne01
    exact hne12 (ho.symm.trans this.symm)
  have hSwap : (Equiv.swap (2 : Fin 6) (e₁.symm ⟨v₂, hv₂⟩)) 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (fun heq ↦ hi₂1 heq.symm)
  change (e₁ ((Equiv.swap 2 (e₁.symm ⟨v₂, hv₂⟩)) 1)).1 = v₁
  rw [hSwap]
  exact finsetEquivFinAtZeroOne_one S (by omega) hCard
    v₀ hv₀ v₁ hv₁ hne01

end SeymourEight.FiveZExactLabels
