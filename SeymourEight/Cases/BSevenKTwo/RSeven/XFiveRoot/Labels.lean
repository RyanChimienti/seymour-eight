import SeymourEight.Cases.BSevenKTwo.Basic
import SeymourEight.Shared.CertificateLabels

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSeven.XFiveRoot.Labels

open Shared Shared.CertificateLabels CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 3 ≃ {v : V // v ∈ externalTargets G C}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 5, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X

noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (hHCard : C.H.card = 7)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 5 ≃ {v : V // v ∈ C.X}) :
    Fin 7 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 7 → {v : V // v ∈ C.H} := fun i =>
    if hi : i.val < 2 then
      ⟨(eA1 ⟨i.val, hi⟩).1, Finset.mem_union_left C.X (eA1 _).2⟩
    else
      ⟨(eX ⟨i.val - 2, by omega⟩).1, Finset.mem_union_right C.A1 (eX _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvA1 | hvX
    · obtain ⟨i, hi⟩ := eA1.surjective ⟨v, hvA1⟩
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := eX.surjective ⟨v, hvX⟩
      refine ⟨⟨i.val + 2, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 2 < 2 by omega] using congrArg Subtype.val hi
  · simpa using hHCard.symm

@[simp] theorem hLabelEquiv_aOne (C : G.LocalConfiguration)
    (hHCard : C.H.card = 7)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 5 ≃ {v : V // v ∈ C.X}) (i : Fin 2) :
    (hLabelEquiv G C hHCard eA1 eX ⟨i.val, by omega⟩).1 = (eA1 i).1 := by
  simp [hLabelEquiv]

@[simp] theorem hLabelEquiv_x (C : G.LocalConfiguration)
    (hHCard : C.H.card = 7)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 5 ≃ {v : V // v ∈ C.X}) (i : Fin 5) :
    (hLabelEquiv G C hHCard eA1 eX ⟨i.val + 2, by omega⟩).1 = (eX i).1 := by
  simp [hLabelEquiv, show ¬i.val + 2 < 2 by omega]

noncomputable def aLabelEquiv (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hRZero : C.R = ∅)
    (h : Fin 7 ≃ {v : V // v ∈ C.H}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i =>
    if hi0 : i.val = 0 then ⟨C.a1, C.a1_mem_root_outNeighbors⟩
    else ⟨(h ⟨i.val - 1, by omega⟩).1,
      Digraph.LocalConfiguration.H_subset_A (G := G) C (h _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    have hvAll : v ∈ C.H ∪ {C.a1} := by
      have hvParts : v ∈ (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R := by
        rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
        exact hv
      simpa [hRZero, Digraph.LocalConfiguration.H, Finset.union_assoc] using hvParts
    rcases Finset.mem_union.mp hvAll with hvH | hva1
    · obtain ⟨i, hi⟩ := h.surjective ⟨v, hvH⟩
      refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show i.val + 1 ≠ 0 by omega] using congrArg Subtype.val hi
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa [f] using (Finset.mem_singleton.mp hva1).symm
  · simpa using hACard.symm

@[simp] theorem aLabelEquiv_zero (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hRZero : C.R = ∅)
    (h : Fin 7 ≃ {v : V // v ∈ C.H}) :
    (aLabelEquiv G C hACard hRZero h 0).1 = C.a1 := by rfl

@[simp] theorem aLabelEquiv_h (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hRZero : C.R = ∅)
    (h : Fin 7 ≃ {v : V // v ∈ C.H}) (i : Fin 7) :
    (aLabelEquiv G C hACard hRZero h ⟨i.val + 1, by omega⟩).1 = (h i).1 := by
  simp [aLabelEquiv]

def pKey (C : G.LocalConfiguration) (v : V) : Nat :=
  (4096 * G.outdegree v + 256 * directCount G (externalTargets G C) v +
    16 * directCount G C.H v + directCount G C.P v) % 65536
def structuralKey (C : G.LocalConfiguration) (v : V) : Nat := directCount G C.P v
def eKey (p : Fin 7 → V) (v : V) : Nat := ∑ i, if G.Adj (p i) v then 1 else 0

noncomputable def canonicalLabels (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 5)
    (hHCard : C.H.card = 7) (hRZero : C.R = ∅)
    (hECard : (externalTargets G C).card = 3) : Labels G C := by
  let eP0 := finsetEquivFin C.P hPCard
  let p := sortedFinsetEquiv (pKey G C) C.P eP0
  let eA10 := finsetEquivFin C.A1 hA1Card
  let eA1 := sortedFinsetEquiv (structuralKey G C) C.A1 eA10
  let eX0 := finsetEquivFin C.X hXCard
  let eX := sortedFinsetEquiv (structuralKey G C) C.X eX0
  let h := hLabelEquiv G C hHCard eA1 eX
  let a := aLabelEquiv G C hACard hRZero h
  let eZ0 := finsetEquivFin (externalTargets G C) hECard
  let z := sortedFinsetEquiv (eKey G (fun i => (p i).1))
    (externalTargets G C) eZ0
  refine { p := p, a := a, z := z, a_zero := ?_, a_aOne := ?_, a_x := ?_ }
  · exact aLabelEquiv_zero G C hACard hRZero h
  · intro i
    rw [aLabelEquiv_h G C hACard hRZero h ⟨i.val, by omega⟩,
      hLabelEquiv_aOne G C hHCard eA1 eX i]
    exact (eA1 i).2
  · intro i
    rw [show (a ⟨i.val + 3, by omega⟩).1 = (h ⟨i.val + 2, by omega⟩).1 by
      simpa only [show i.val + 2 + 1 = i.val + 3 by omega] using
        aLabelEquiv_h G C hACard hRZero h ⟨i.val + 2, by omega⟩,
      hLabelEquiv_x G C hHCard eA1 eX i]
    exact (eX i).2

theorem canonicalLabels_p_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 5)
    (hHCard : C.H.card = 7) (hRZero : C.R = ∅)
    (hECard : (externalTargets G C).card = 3) (q : Fin 6) :
    let L := canonicalLabels G C hPCard hACard hA1Card hXCard hHCard hRZero hECard
    pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
      pKey G C (L.p ⟨q.val, by omega⟩).1 := by
  dsimp only
  simpa only [canonicalLabels] using sorted_key_anti (pKey G C) C.P
    (finsetEquivFin C.P hPCard) (i := ⟨q.val, by omega⟩)
    (j := ⟨q.val + 1, by omega⟩) (hij := by simp)

theorem canonicalLabels_e_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 5)
    (hHCard : C.H.card = 7) (hRZero : C.R = ∅)
    (hECard : (externalTargets G C).card = 3) (q : Fin 2) :
    let L := canonicalLabels G C hPCard hACard hA1Card hXCard hHCard hRZero hECard
    eKey G (fun i => (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
      eKey G (fun i => (L.p i).1) (L.z ⟨q.val, by omega⟩).1 := by
  dsimp only
  simpa only [canonicalLabels] using sorted_key_anti
    (eKey G (fun i => ((sortedFinsetEquiv (pKey G C) C.P
      (finsetEquivFin C.P hPCard)) i).1)) (externalTargets G C)
      (finsetEquivFin (externalTargets G C) hECard)
    (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩) (hij := by simp)

theorem canonicalLabels_aOne_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 5)
    (hHCard : C.H.card = 7) (hRZero : C.R = ∅)
    (hECard : (externalTargets G C).card = 3) :
    let L := canonicalLabels G C hPCard hACard hA1Card hXCard hHCard hRZero hECard
    structuralKey G C (L.a 2).1 ≤ structuralKey G C (L.a 1).1 := by
  dsimp only
  simpa [canonicalLabels, aLabelEquiv, hLabelEquiv] using
    sorted_key_anti (structuralKey G C) C.A1 (finsetEquivFin C.A1 hA1Card)
      (i := (0 : Fin 2)) (j := (1 : Fin 2)) (hij := by simp)

theorem canonicalLabels_x_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 5)
    (hHCard : C.H.card = 7) (hRZero : C.R = ∅)
    (hECard : (externalTargets G C).card = 3) (q : Fin 4) :
    let L := canonicalLabels G C hPCard hACard hA1Card hXCard hHCard hRZero hECard
    structuralKey G C (L.a ⟨q.val + 4, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨q.val + 3, by omega⟩).1 := by
  dsimp only
  simpa (disch := omega) [canonicalLabels, aLabelEquiv, hLabelEquiv,
    show ¬q.val + 3 < 2 by omega, show ¬q.val + 2 < 2 by omega] using
    sorted_key_anti (structuralKey G C) C.X (finsetEquivFin C.X hXCard)
      (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩) (hij := by simp)

end SeymourEight.BSevenKTwo.RSeven.XFiveRoot.Labels
