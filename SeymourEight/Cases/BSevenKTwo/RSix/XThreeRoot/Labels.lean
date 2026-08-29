import SeymourEight.Cases.BSevenKTwo.RSeven.XThreeNoRoot.Labels
import SeymourEight.Cases.BSixKThree.Counting

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XThreeRoot.Labels

open Shared Shared.CertificateLabels CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (C : G.LocalConfiguration) (q : V) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  e : Fin 4 ≃ {v : V // v ∈ ({q} ∪ externalTargets G C)}
  e_zero : (e 0).1 = q
  e_tail_Z : ∀ i : Fin 3, (e ⟨i.val + 1, by omega⟩).1 ∈ externalTargets G C
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 3, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 2, (a ⟨i.val + 6, by omega⟩).1 ∈ C.R

structure UnreachedLabels (C : G.LocalConfiguration) (q : V) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 4 ≃ {v : V // v ∈ externalTargets G C}
  q_mem : q ∈ C.Q
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 3, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 2, (a ⟨i.val + 6, by omega⟩).1 ∈ C.R

def pKey (v : V) : Nat := G.outdegree v
def structuralKey (C : G.LocalConfiguration) (v : V) : Nat :=
  directCount G C.B v

noncomputable def canonicalUnreachedLabels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 4) : UnreachedLabels G C q := by
  let p := sortedFinsetEquiv (pKey G) C.P (finsetEquivFin C.P hPCard)
  let eA1 := sortedFinsetEquiv (structuralKey G C) C.A1
    (finsetEquivFin C.A1 hAOneCard)
  let eX := sortedFinsetEquiv (structuralKey G C) C.X
    (finsetEquivFin C.X hXCard)
  let h := RSeven.XThreeNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX
  let eR := sortedFinsetEquiv (structuralKey G C) C.R
    (finsetEquivFin C.R hRCard)
  let a := RSeven.XThreeNoRoot.Labels.aLabelEquiv G C hACard h eR
  let z := finsetEquivFin (externalTargets G C) hZCard
  refine ⟨p, a, z, hqQ, ?_, ?_, ?_, ?_⟩
  · exact RSeven.XThreeNoRoot.Labels.aLabelEquiv_zero G C hACard h eR
  · intro i
    rw [RSeven.XThreeNoRoot.Labels.aLabelEquiv_h G C hACard h eR
        ⟨i.val, by omega⟩,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv_aOne G C hHCard eA1 eX i]
    exact (eA1 i).2
  · intro i
    rw [show (a ⟨i.val + 3, by omega⟩).1 =
        (h ⟨i.val + 2, by omega⟩).1 by
      simpa only [show i.val + 2 + 1 = i.val + 3 by omega] using
        RSeven.XThreeNoRoot.Labels.aLabelEquiv_h G C hACard h eR
          ⟨i.val + 2, by omega⟩,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv_x G C hHCard eA1 eX i]
    exact (eX i).2
  · intro i
    rw [RSeven.XThreeNoRoot.Labels.aLabelEquiv_r G C hACard h eR i]
    exact (eR i).2

theorem canonicalUnreachedLabels_p_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 4) (i : Fin 5) :
    G.outdegree ((canonicalUnreachedLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard).p ⟨i.val + 1, by omega⟩).1 ≤
    G.outdegree ((canonicalUnreachedLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard).p ⟨i.val, by omega⟩).1 := by
  simpa only [canonicalUnreachedLabels, pKey] using
    (sorted_key_anti (pKey G) C.P (finsetEquivFin C.P hPCard)
      (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (hij := by simp))

theorem canonicalUnreachedLabels_aOne_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 4) (i : Fin 1) :
    let L := canonicalUnreachedLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard
    structuralKey G C (L.a ⟨i.val + 2, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨i.val + 1, by omega⟩).1 := by
  dsimp only
  simpa (disch := omega) [canonicalUnreachedLabels,
      RSeven.XThreeNoRoot.Labels.aLabelEquiv,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
    (sorted_key_anti (structuralKey G C) C.A1
      (finsetEquivFin C.A1 hAOneCard)
      (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (hij := by simp))

theorem canonicalUnreachedLabels_x_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 4) (i : Fin 2) :
    let L := canonicalUnreachedLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard
    structuralKey G C (L.a ⟨4 + i.val, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨3 + i.val, by omega⟩).1 := by
  dsimp only
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simpa [canonicalUnreachedLabels,
        RSeven.XThreeNoRoot.Labels.aLabelEquiv,
        RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
      (sorted_key_anti (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard) (i := (0 : Fin 3)) (j := (1 : Fin 3))
        (hij := by decide))
  · simpa [canonicalUnreachedLabels,
        RSeven.XThreeNoRoot.Labels.aLabelEquiv,
        RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
      (sorted_key_anti (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard) (i := (1 : Fin 3)) (j := (2 : Fin 3))
        (hij := by decide))

theorem canonicalUnreachedLabels_r_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 4) (i : Fin 1) :
    let L := canonicalUnreachedLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard
    structuralKey G C (L.a ⟨i.val + 7, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨i.val + 6, by omega⟩).1 := by
  dsimp only
  simpa (disch := omega) [canonicalUnreachedLabels,
      RSeven.XThreeNoRoot.Labels.aLabelEquiv,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
    (sorted_key_anti (structuralKey G C) C.R
      (finsetEquivFin C.R hRCard)
      (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (hij := by simp))

noncomputable def canonicalLabels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 3) : Labels G C q := by
  let p := sortedFinsetEquiv (pKey G) C.P (finsetEquivFin C.P hPCard)
  let eA1 := sortedFinsetEquiv (structuralKey G C) C.A1
    (finsetEquivFin C.A1 hAOneCard)
  let eX := sortedFinsetEquiv (structuralKey G C) C.X
    (finsetEquivFin C.X hXCard)
  let h := RSeven.XThreeNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX
  let eR := sortedFinsetEquiv (structuralKey G C) C.R
    (finsetEquivFin C.R hRCard)
  let a := RSeven.XThreeNoRoot.Labels.aLabelEquiv G C hACard h eR
  let z := finsetEquivFin (externalTargets G C) hZCard
  have hqNotZ : q ∉ externalTargets G C := by
    exact fun hqZ => (Finset.disjoint_left.mp
      (BSixKThree.disjoint_B_externalTargets G C))
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ) hqZ
  let E := {q} ∪ externalTargets G C
  have hECard : E.card = 4 := by
    rw [Finset.card_union_of_disjoint]
    · simp [hZCard]
    · rw [Finset.disjoint_left]
      intro v hvq hvz
      exact hqNotZ (Finset.mem_singleton.mp hvq ▸ hvz)
  let f : Fin 4 → {v : V // v ∈ E} := fun i =>
    if hi : i.val = 0 then
      ⟨q, Finset.mem_union_left (externalTargets G C) (by simp)⟩
    else ⟨(z ⟨i.val - 1, by omega⟩).1,
      Finset.mem_union_right {q} (z _).2⟩
  let e : Fin 4 ≃ {v : V // v ∈ E} := by
    apply Equiv.ofBijective f
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hvq | hvz
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hvq).symm
      · obtain ⟨i, hi⟩ := z.surjective ⟨v, hvz⟩
        refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show i.val + 1 ≠ 0 by omega] using congrArg Subtype.val hi
    · simp [hECard]
  refine ⟨p, a, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro i
    have heval : (e ⟨i.val + 1, by omega⟩).1 = (z i).1 := by
      simp [e, f]
    rw [heval]
    exact (z i).2
  · exact RSeven.XThreeNoRoot.Labels.aLabelEquiv_zero G C hACard h eR
  · intro i
    rw [RSeven.XThreeNoRoot.Labels.aLabelEquiv_h G C hACard h eR
        ⟨i.val, by omega⟩,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv_aOne G C hHCard eA1 eX i]
    exact (eA1 i).2
  · intro i
    rw [show (a ⟨i.val + 3, by omega⟩).1 =
        (h ⟨i.val + 2, by omega⟩).1 by
      simpa only [show i.val + 2 + 1 = i.val + 3 by omega] using
        RSeven.XThreeNoRoot.Labels.aLabelEquiv_h G C hACard h eR
          ⟨i.val + 2, by omega⟩,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv_x G C hHCard eA1 eX i]
    exact (eX i).2
  · intro i
    rw [RSeven.XThreeNoRoot.Labels.aLabelEquiv_r G C hACard h eR i]
    exact (eR i).2

theorem canonicalLabels_p_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 3) (i : Fin 5) :
    G.outdegree ((canonicalLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard).p ⟨i.val + 1, by omega⟩).1 ≤
    G.outdegree ((canonicalLabels G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard).p ⟨i.val, by omega⟩).1 := by
  simpa only [canonicalLabels, pKey] using
    (sorted_key_anti (pKey G) C.P (finsetEquivFin C.P hPCard)
      (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (hij := by simp))

theorem canonicalLabels_aOne_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 3) (i : Fin 1) :
    let L := canonicalLabels G C q hqQ hPCard hACard hAOneCard hXCard
      hRCard hHCard hZCard
    structuralKey G C (L.a ⟨i.val + 2, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨i.val + 1, by omega⟩).1 := by
  dsimp only
  simpa (disch := omega) [canonicalLabels,
      RSeven.XThreeNoRoot.Labels.aLabelEquiv,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
    (sorted_key_anti (structuralKey G C) C.A1
      (finsetEquivFin C.A1 hAOneCard)
      (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (hij := by simp))

theorem canonicalLabels_x_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 3) (i : Fin 2) :
    let L := canonicalLabels G C q hqQ hPCard hACard hAOneCard hXCard
      hRCard hHCard hZCard
    structuralKey G C (L.a ⟨4 + i.val, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨3 + i.val, by omega⟩).1 := by
  dsimp only
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simpa [canonicalLabels, RSeven.XThreeNoRoot.Labels.aLabelEquiv,
        RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
      (sorted_key_anti (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard) (i := (0 : Fin 3)) (j := (1 : Fin 3))
        (hij := by decide))
  · simpa [canonicalLabels, RSeven.XThreeNoRoot.Labels.aLabelEquiv,
        RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
      (sorted_key_anti (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard) (i := (1 : Fin 3)) (j := (2 : Fin 3))
        (hij := by decide))

theorem canonicalLabels_r_order (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = 3) (i : Fin 1) :
    let L := canonicalLabels G C q hqQ hPCard hACard hAOneCard hXCard
      hRCard hHCard hZCard
    structuralKey G C (L.a ⟨i.val + 7, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨i.val + 6, by omega⟩).1 := by
  dsimp only
  simpa (disch := omega) [canonicalLabels,
      RSeven.XThreeNoRoot.Labels.aLabelEquiv,
      RSeven.XThreeNoRoot.Labels.hLabelEquiv] using
    (sorted_key_anti (structuralKey G C) C.R
      (finsetEquivFin C.R hRCard)
      (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (hij := by simp))

end SeymourEight.BSevenKTwo.RSix.XThreeRoot.Labels
