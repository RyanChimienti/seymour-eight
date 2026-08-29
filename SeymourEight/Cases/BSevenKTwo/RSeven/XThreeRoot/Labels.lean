import SeymourEight.Cases.BSevenKTwo.Basic
import SeymourEight.Shared.CertificateLabels

set_option linter.style.header false

/-!
# Canonical labels for the rooted `r = 7`, `x = 3` core

The fixed `A` layout is `a1, A1[2], X[3], R[2]`.  Each structural class,
`P`, and `Z` is sorted only by a graph-invariant degree key.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XThreeRoot.Labels

open Shared Shared.CertificateLabels CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (zCount : Nat) (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin zCount ≃ {v : V // v ∈ (externalTargets G C)}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 3, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 2, (a ⟨i.val + 6, by omega⟩).1 ∈ C.R

noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X}) :
    Fin 5 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 5 → {v : V // v ∈ C.H} := fun i =>
    if hi : i.val < 2 then
      ⟨(eA1 ⟨i.val, hi⟩).1, Finset.mem_union_left C.X (eA1 _).2⟩
    else
      ⟨(eX ⟨i.val - 2, by omega⟩).1,
        Finset.mem_union_right C.A1 (eX _).2⟩
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
    (hHCard : C.H.card = 5)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X}) (i : Fin 2) :
    (hLabelEquiv G C hHCard eA1 eX ⟨i.val, by omega⟩).1 = (eA1 i).1 := by
  simp [hLabelEquiv]

@[simp] theorem hLabelEquiv_x (C : G.LocalConfiguration)
    (hHCard : C.H.card = 5)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X}) (i : Fin 3) :
    (hLabelEquiv G C hHCard eA1 eX ⟨i.val + 2, by omega⟩).1 = (eX i).1 := by
  simp [hLabelEquiv, show ¬i.val + 2 < 2 by omega]

noncomputable def aLabelEquiv (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i =>
    if hi0 : i.val = 0 then ⟨C.a1, C.a1_mem_root_outNeighbors⟩
    else if hiH : i.val ≤ 5 then
      ⟨(h ⟨i.val - 1, by omega⟩).1,
        Digraph.LocalConfiguration.H_subset_A (G := G) C (h _).2⟩
    else
      ⟨(eR ⟨i.val - 6, by omega⟩).1,
        Digraph.LocalConfiguration.R_subset_A (G := G) C (eR _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    have hvAll : v ∈ (C.H ∪ {C.a1}) ∪ C.R := by
      have hvParts : v ∈ (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R := by
        rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
        exact hv
      simpa [Digraph.LocalConfiguration.H, Finset.union_assoc] using hvParts
    rcases Finset.mem_union.mp hvAll with hvHa | hvR
    · rcases Finset.mem_union.mp hvHa with hvH | hva1
      · obtain ⟨i, hi⟩ := h.surjective ⟨v, hvH⟩
        refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show i.val + 1 ≠ 0 by omega,
          show i.val + 1 ≤ 5 by omega] using congrArg Subtype.val hi
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hva1).symm
    · obtain ⟨i, hi⟩ := eR.surjective ⟨v, hvR⟩
      refine ⟨⟨i.val + 6, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show i.val + 6 ≠ 0 by omega,
        show ¬i.val + 6 ≤ 5 by omega] using congrArg Subtype.val hi
  · simpa using hACard.symm

@[simp] theorem aLabelEquiv_zero (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) :
    (aLabelEquiv G C hACard h eR 0).1 = C.a1 := by rfl

@[simp] theorem aLabelEquiv_h (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) (i : Fin 5) :
    (aLabelEquiv G C hACard h eR ⟨i.val + 1, by omega⟩).1 = (h i).1 := by
  simp [aLabelEquiv,
    show i.val + 1 ≤ 5 by omega]

@[simp] theorem aLabelEquiv_r (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R}) (i : Fin 2) :
    (aLabelEquiv G C hACard h eR ⟨i.val + 6, by omega⟩).1 = (eR i).1 := by
  simp [aLabelEquiv,
    show ¬i.val + 6 ≤ 5 by omega]

def pKey (C : G.LocalConfiguration) (v : V) : Nat :=
  (4096 * G.outdegree v + 256 * directCount G (externalTargets G C) v +
    16 * directCount G C.H v + directCount G C.P v) % 65536

def structuralKey (C : G.LocalConfiguration) (v : V) : Nat :=
  directCount G C.P v

def zKey (p : Fin 7 → V) (v : V) : Nat :=
  ∑ i, if G.Adj (p i) v then 1 else 0

noncomputable def canonicalLabels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = zCount) : Labels G zCount C := by
  let eP0 : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let p := sortedFinsetEquiv (pKey G C) C.P eP0
  let eA10 : Fin 2 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eA1 := sortedFinsetEquiv (structuralKey G C) C.A1 eA10
  let eX0 : Fin 3 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let eX := sortedFinsetEquiv (structuralKey G C) C.X eX0
  let h := hLabelEquiv G C hHCard eA1 eX
  let eR0 : Fin 2 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let eR := sortedFinsetEquiv (structuralKey G C) C.R eR0
  let a := aLabelEquiv G C hACard h eR
  let eZ0 : Fin zCount ≃ {v : V // v ∈ (externalTargets G C)} := finsetEquivFin (externalTargets G C) hZCard
  let z := sortedFinsetEquiv (zKey G (fun i => (p i).1)) (externalTargets G C) eZ0
  refine {
    p := p
    a := a
    z := z
    a_zero := ?_
    a_aOne := ?_
    a_x := ?_
    a_r := ?_ }
  · exact aLabelEquiv_zero G C hACard h eR
  · intro i
    rw [aLabelEquiv_h G C hACard h eR ⟨i.val, by omega⟩,
      hLabelEquiv_aOne G C hHCard eA1 eX i]
    exact (eA1 i).2
  · intro i
    rw [show (a ⟨i.val + 3, by omega⟩).1 =
        (h ⟨i.val + 2, by omega⟩).1 by
      simpa only [show i.val + 2 + 1 = i.val + 3 by omega] using
        aLabelEquiv_h G C hACard h eR ⟨i.val + 2, by omega⟩,
      hLabelEquiv_x G C hHCard eA1 eX i]
    exact (eX i).2
  · intro i
    rw [aLabelEquiv_r G C hACard h eR i]
    exact (eR i).2

theorem aLabelEquiv_aOne_key_order (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hHCard : C.H.card = 5)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R})
    (hOrder : ∀ q : Fin 1,
      structuralKey G C (eA1 ⟨q.val + 1, by omega⟩).1 ≤
        structuralKey G C (eA1 ⟨q.val, by omega⟩).1)
    (q : Fin 1) :
    structuralKey G C
        (aLabelEquiv G C hACard (hLabelEquiv G C hHCard eA1 eX) eR
          ⟨q.val + 2, by omega⟩).1 ≤
      structuralKey G C
        (aLabelEquiv G C hACard (hLabelEquiv G C hHCard eA1 eX) eR
          ⟨q.val + 1, by omega⟩).1 := by
  simpa (disch := omega) [aLabelEquiv, hLabelEquiv] using hOrder q

theorem aLabelEquiv_x_key_order (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hHCard : C.H.card = 5)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 3 ≃ {v : V // v ∈ C.X})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R})
    (hOrder : ∀ q : Fin 2,
      structuralKey G C (eX ⟨q.val + 1, by omega⟩).1 ≤
        structuralKey G C (eX ⟨q.val, by omega⟩).1)
    (q : Fin 2) :
    structuralKey G C
        (aLabelEquiv G C hACard (hLabelEquiv G C hHCard eA1 eX) eR
          ⟨4 + q.val, by omega⟩).1 ≤
      structuralKey G C
        (aLabelEquiv G C hACard (hLabelEquiv G C hHCard eA1 eX) eR
          ⟨3 + q.val, by omega⟩).1 := by
  have hq : q = 0 ∨ q = 1 := by omega
  rcases hq with rfl | rfl
  · simpa [aLabelEquiv, hLabelEquiv] using hOrder 0
  · simpa [aLabelEquiv, hLabelEquiv] using hOrder 1

theorem aLabelEquiv_r_key_order (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (eR : Fin 2 ≃ {v : V // v ∈ C.R})
    (hOrder : ∀ q : Fin 1,
      structuralKey G C (eR ⟨q.val + 1, by omega⟩).1 ≤
        structuralKey G C (eR ⟨q.val, by omega⟩).1)
    (q : Fin 1) :
    structuralKey G C (aLabelEquiv G C hACard h eR
        ⟨q.val + 7, by omega⟩).1 ≤
      structuralKey G C (aLabelEquiv G C hACard h eR
        ⟨q.val + 6, by omega⟩).1 := by
  simpa (disch := omega) [aLabelEquiv] using hOrder q

theorem canonicalLabels_p_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 6) :
    pKey G C ((canonicalLabels G zCount C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard).p ⟨q.val + 1, by omega⟩).1 ≤
      pKey G C ((canonicalLabels G zCount C hPCard hACard hA1Card hXCard
        hRCard hHCard hZCard).p ⟨q.val, by omega⟩).1 := by
  simpa only [canonicalLabels] using
    (sorted_key_anti (pKey G C) C.P
      (finsetEquivFin C.P hPCard)
      (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
      (hij := by simp))

theorem canonicalLabels_z_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin (zCount - 1)) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard
    zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
      zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val, by omega⟩).1 := by
  dsimp only
  simpa only [canonicalLabels] using
    (sorted_key_anti
      (zKey G (fun i ↦
        ((sortedFinsetEquiv (pKey G C) C.P
          (finsetEquivFin C.P hPCard)) i).1)) (externalTargets G C)
      (finsetEquivFin (externalTargets G C) hZCard)
      (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
      (hij := by simp))

theorem canonicalLabels_aOne_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 1) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard
    structuralKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨q.val + 1, by omega⟩).1 := by
  dsimp only
  simpa only [canonicalLabels] using
    (aLabelEquiv_aOne_key_order G C hACard hHCard
      (sortedFinsetEquiv (structuralKey G C) C.A1
        (finsetEquivFin C.A1 hA1Card))
      (sortedFinsetEquiv (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard))
      (sortedFinsetEquiv (structuralKey G C) C.R
        (finsetEquivFin C.R hRCard))
      (fun q ↦ sorted_key_anti (structuralKey G C) C.A1
        (finsetEquivFin C.A1 hA1Card)
        (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
        (hij := by simp)) q)

theorem canonicalLabels_x_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard
    structuralKey G C (L.a ⟨4 + q.val, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨3 + q.val, by omega⟩).1 := by
  dsimp only
  simpa only [canonicalLabels] using
    (aLabelEquiv_x_key_order G C hACard hHCard
      (sortedFinsetEquiv (structuralKey G C) C.A1
        (finsetEquivFin C.A1 hA1Card))
      (sortedFinsetEquiv (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard))
      (sortedFinsetEquiv (structuralKey G C) C.R
        (finsetEquivFin C.R hRCard))
      (fun q ↦ sorted_key_anti (structuralKey G C) C.X
        (finsetEquivFin C.X hXCard)
        (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
        (hij := by simp)) q)

theorem canonicalLabels_r_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 2) (hHCard : C.H.card = 5)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 1) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard
    structuralKey G C (L.a ⟨q.val + 7, by omega⟩).1 ≤
      structuralKey G C (L.a ⟨q.val + 6, by omega⟩).1 := by
  dsimp only
  simpa only [canonicalLabels] using
    (aLabelEquiv_r_key_order G C hACard
      (hLabelEquiv G C hHCard
        (sortedFinsetEquiv (structuralKey G C) C.A1
          (finsetEquivFin C.A1 hA1Card))
        (sortedFinsetEquiv (structuralKey G C) C.X
          (finsetEquivFin C.X hXCard)))
      (sortedFinsetEquiv (structuralKey G C) C.R
        (finsetEquivFin C.R hRCard))
      (fun q ↦ sorted_key_anti (structuralKey G C) C.R
        (finsetEquivFin C.R hRCard)
        (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
        (hij := by simp)) q)

end SeymourEight.BSevenKTwo.RSeven.XThreeRoot.Labels
