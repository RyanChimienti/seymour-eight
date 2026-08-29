import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.BroadFourEncoding
import SeymourEight.Shared.FinsetBridge
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

/-!
# Canonical labels for the broad four-`Z` core

The finite certificate quotients only genuine relabeling symmetries.  The
vertices of `P` are sorted by the graph version of the certificate row key;
after that choice, the vertices of `Z` are sorted by their incoming `P`
degree.  The `A` labels retain the structural order
`a1, A1[2], X[4], R`.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLabels

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 4 ≃ {v : V // v ∈ C.Z}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 4, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X
  a_r : (a 7).1 ∈ C.R

noncomputable def hLabelEquiv (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) :
    Fin 6 ≃ {v : V // v ∈ C.H} := by
  let f : Fin 6 → {v : V // v ∈ C.H} := fun i =>
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
    (hHCard : C.H.card = 6)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) (i : Fin 2) :
    (hLabelEquiv G C hHCard eA1 eX ⟨i.val, by omega⟩).1 = (eA1 i).1 := by
  simp [hLabelEquiv]

@[simp] theorem hLabelEquiv_x (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 4 ≃ {v : V // v ∈ C.X}) (i : Fin 4) :
    (hLabelEquiv G C hHCard eA1 eX ⟨i.val + 2, by omega⟩).1 = (eX i).1 := by
  simp [hLabelEquiv, show ¬i.val + 2 < 2 by omega]

noncomputable def aLabelEquiv (C : G.LocalConfiguration)
    (hACard : C.A.card = 8)
    (h : Fin 6 ≃ {v : V // v ∈ C.H})
    (eR : Fin 1 ≃ {v : V // v ∈ C.R}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i =>
    if hi0 : i.val = 0 then ⟨C.a1, C.a1_mem_root_outNeighbors⟩
    else if hiH : i.val ≤ 6 then
      ⟨(h ⟨i.val - 1, by omega⟩).1,
        Digraph.LocalConfiguration.H_subset_A (G := G) C (h _).2⟩
    else
      ⟨(eR 0).1, Digraph.LocalConfiguration.R_subset_A (G := G) C (eR 0).2⟩
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
          show i.val + 1 ≤ 6 by omega] using congrArg Subtype.val hi
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hva1).symm
    · obtain ⟨i, hi⟩ := eR.surjective ⟨v, hvR⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      refine ⟨7, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
  · simpa using hACard.symm

@[simp] theorem aLabelEquiv_zero (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 6 ≃ {v : V // v ∈ C.H})
    (eR : Fin 1 ≃ {v : V // v ∈ C.R}) :
    (aLabelEquiv G C hACard h eR 0).1 = C.a1 := by rfl

@[simp] theorem aLabelEquiv_h (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 6 ≃ {v : V // v ∈ C.H})
    (eR : Fin 1 ≃ {v : V // v ∈ C.R}) (i : Fin 6) :
    (aLabelEquiv G C hACard h eR ⟨i.val + 1, by omega⟩).1 = (h i).1 := by
  simp [aLabelEquiv,
    show i.val + 1 ≤ 6 by omega]

@[simp] theorem aLabelEquiv_r (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (h : Fin 6 ≃ {v : V // v ∈ C.H})
    (eR : Fin 1 ≃ {v : V // v ∈ C.R}) :
    (aLabelEquiv G C hACard h eR 7).1 = (eR 0).1 := by
  simp [aLabelEquiv]

def pKey (C : G.LocalConfiguration) (v : V) : Nat :=
  4096 * directCount G C.Z v + 256 * G.outdegree v +
    16 * directCount G C.P v + directCount G C.H v

def pSortPermutation (C : G.LocalConfiguration) (p : Fin 7 → V) :
    Equiv.Perm (Fin 7) :=
  Tuple.sort fun i => OrderDual.toDual (pKey G C (p i))

noncomputable def sortedPFinsetEquiv (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P}) :
    Fin 7 ≃ {v : V // v ∈ C.P} :=
  (pSortPermutation G C (fun i => (eP i).1)).trans eP

theorem sortedP_key_anti (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P}) {i j : Fin 7} (hij : i ≤ j) :
    pKey G C (sortedPFinsetEquiv G C eP i).1 ≥
      pKey G C (sortedPFinsetEquiv G C eP j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (pKey G C (eP q).1)) hij

def zColumnDegree (p : Fin 7 → V) (v : V) : Nat :=
  ∑ i, if G.Adj (p i) v then 1 else 0

/-- Full incoming `P` incidence vector, used only to break equal-degree ties. -/
def zIncidenceCode (p : Fin 7 → V) (v : V) : BitVec 7 :=
  (if G.Adj (p 0) v then 1 else 0) +
  (if G.Adj (p 1) v then 2 else 0) +
  (if G.Adj (p 2) v then 4 else 0) +
  (if G.Adj (p 3) v then 8 else 0) +
  (if G.Adj (p 4) v then 16 else 0) +
  (if G.Adj (p 5) v then 32 else 0) +
  (if G.Adj (p 6) v then 64 else 0)

def zColumnKey (p : Fin 7 → V) (v : V) : Nat :=
  128 * zColumnDegree G p v + (zIncidenceCode G p v).toNat

def zSortPermutation (p : Fin 7 → V) (z : Fin 4 → V) :
    Equiv.Perm (Fin 4) :=
  Tuple.sort fun i => OrderDual.toDual (zColumnKey G p (z i))

noncomputable def sortedZFinsetEquiv (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eZ : Fin 4 ≃ {v : V // v ∈ C.Z}) :
    Fin 4 ≃ {v : V // v ∈ C.Z} :=
  (zSortPermutation G p (fun i => (eZ i).1)).trans eZ

theorem sortedZ_degree_anti (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eZ : Fin 4 ≃ {v : V // v ∈ C.Z}) {i j : Fin 4} (hij : i ≤ j) :
    zColumnDegree G p (sortedZFinsetEquiv G p C eZ i).1 ≥
      zColumnDegree G p (sortedZFinsetEquiv G p C eZ j).1 := by
  have hKey := Tuple.monotone_sort
    (fun q => OrderDual.toDual (zColumnKey G p (eZ q).1)) hij
  change zColumnKey G p (sortedZFinsetEquiv G p C eZ i).1 ≥
    zColumnKey G p (sortedZFinsetEquiv G p C eZ j).1 at hKey
  have hi : (zIncidenceCode G p
      (sortedZFinsetEquiv G p C eZ i).1).toNat < 128 := by
    exact (zIncidenceCode G p
      (sortedZFinsetEquiv G p C eZ i).1).toFin.isLt
  have hj : (zIncidenceCode G p
      (sortedZFinsetEquiv G p C eZ j).1).toNat < 128 := by
    exact (zIncidenceCode G p
      (sortedZFinsetEquiv G p C eZ j).1).toFin.isLt
  simp only [zColumnKey] at hKey
  omega

theorem sortedZ_key_anti (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eZ : Fin 4 ≃ {v : V // v ∈ C.Z}) {i j : Fin 4} (hij : i ≤ j) :
    zColumnKey G p (sortedZFinsetEquiv G p C eZ i).1 ≥
      zColumnKey G p (sortedZFinsetEquiv G p C eZ j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (zColumnKey G p (eZ q).1)) hij

/-- A label-invariant key for the interchangeable vertices inside `A1` and
`X`: outgoing incidences to `P`, followed by incoming incidences from `P`. -/
def hDegreeKey (C : G.LocalConfiguration) (v : V) : Nat :=
  16 * directCount G C.P v + ∑ p ∈ C.P, if G.Adj p v then 1 else 0

def hSortPermutation {n : Nat} (C : G.LocalConfiguration) (h : Fin n → V) :
    Equiv.Perm (Fin n) :=
  Tuple.sort fun i => OrderDual.toDual (hDegreeKey G C (h i))

noncomputable def sortedHFinsetEquiv {n : Nat} (C : G.LocalConfiguration)
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S}) :
    Fin n ≃ {v : V // v ∈ S} :=
  (hSortPermutation G C (fun i => (e i).1)).trans e

theorem sortedH_key_anti {n : Nat} (C : G.LocalConfiguration)
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S})
    {i j : Fin n} (hij : i ≤ j) :
    hDegreeKey G C (sortedHFinsetEquiv G C S e i).1 ≥
      hDegreeKey G C (sortedHFinsetEquiv G C S e j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (hDegreeKey G C (e q).1)) hij

noncomputable def canonicalLabels (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 4) : Labels G C := by
  let eP : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let p := sortedPFinsetEquiv G C eP
  let eA1Raw : Fin 2 ≃ {v : V // v ∈ C.A1} :=
    finsetEquivFin C.A1 hA1Card
  let eA1 : Fin 2 ≃ {v : V // v ∈ C.A1} :=
    sortedHFinsetEquiv G C C.A1 eA1Raw
  let eXRaw : Fin 4 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let eX : Fin 4 ≃ {v : V // v ∈ C.X} :=
    sortedHFinsetEquiv G C C.X eXRaw
  let h := hLabelEquiv G C hHCard eA1 eX
  let eR : Fin 1 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a := aLabelEquiv G C hACard h eR
  let eZ : Fin 4 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let z := sortedZFinsetEquiv G (fun i => (p i).1) C eZ
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
    rw [show (a ⟨i.val + 1, by omega⟩).1 = (h ⟨i.val, by omega⟩).1 by
      exact aLabelEquiv_h G C hACard h eR ⟨i.val, by omega⟩]
    rw [show (h ⟨i.val, by omega⟩).1 = (eA1 i).1 by
      exact hLabelEquiv_aOne G C hHCard eA1 eX i]
    exact (eA1 i).2
  · intro i
    rw [show (a ⟨i.val + 3, by omega⟩).1 =
        (h ⟨i.val + 2, by omega⟩).1 by
      simpa only [show i.val + 2 + 1 = i.val + 3 by omega] using
        aLabelEquiv_h G C hACard h eR ⟨i.val + 2, by omega⟩]
    rw [show (h ⟨i.val + 2, by omega⟩).1 = (eX i).1 by
      exact hLabelEquiv_x G C hHCard eA1 eX i]
    exact (eX i).2
  · rw [show (a 7).1 = (eR 0).1 by exact aLabelEquiv_r G C hACard h eR]
    exact (eR 0).2

theorem canonicalLabels_p_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 4) (q : Nat) (hq : q < 6) :
    pKey G C ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
      hHCard hZCard).p ⟨q + 1, by omega⟩).1 ≤
    pKey G C ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
      hHCard hZCard).p ⟨q, by omega⟩).1 := by
  exact sortedP_key_anti G C (finsetEquivFin C.P hPCard)
    (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_z_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 4) (q : Nat) (hq : q < 3) :
    zColumnDegree G
      (fun i => ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
        hHCard hZCard).p i).1)
      ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard hHCard
        hZCard).z ⟨q + 1, by omega⟩).1 ≤
    zColumnDegree G
      (fun i => ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
        hHCard hZCard).p i).1)
      ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard hHCard
        hZCard).z ⟨q, by omega⟩).1 := by
  exact sortedZ_degree_anti G
    (fun i => (sortedPFinsetEquiv G C (finsetEquivFin C.P hPCard) i).1)
    C (finsetEquivFin C.Z hZCard) (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_z_key_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 4) (q : Nat) (hq : q < 3) :
    zColumnKey G
      (fun i => ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
        hHCard hZCard).p i).1)
      ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard hHCard
        hZCard).z ⟨q + 1, by omega⟩).1 ≤
    zColumnKey G
      (fun i => ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
        hHCard hZCard).p i).1)
      ((canonicalLabels G C hPCard hACard hA1Card hXCard hRCard hHCard
        hZCard).z ⟨q, by omega⟩).1 := by
  exact sortedZ_key_anti G
    (fun i => (sortedPFinsetEquiv G C (finsetEquivFin C.P hPCard) i).1)
    C (finsetEquivFin C.Z hZCard) (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_aOne_key_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 4) :
    hDegreeKey G C ((canonicalLabels G C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard).a 2).1 ≤
    hDegreeKey G C ((canonicalLabels G C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard).a 1).1 := by
  change hDegreeKey G C
      (sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hA1Card) 1).1 ≤
    hDegreeKey G C
      (sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hA1Card) 0).1
  exact sortedH_key_anti G C C.A1 (finsetEquivFin C.A1 hA1Card)
    (Fin.mk_le_mk.mpr (by decide))

theorem canonicalLabels_x_key_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : C.Z.card = 4) (q : Nat) (hq : q < 3) :
    hDegreeKey G C ((canonicalLabels G C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard).a ⟨q + 4, by omega⟩).1 ≤
    hDegreeKey G C ((canonicalLabels G C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard).a ⟨q + 3, by omega⟩).1 := by
  have hKey := sortedH_key_anti G C C.X (finsetEquivFin C.X hXCard)
    (i := ⟨q, by omega⟩) (j := ⟨q + 1, by omega⟩)
    (Fin.mk_le_mk.mpr (by omega))
  change hDegreeKey G C
      ((aLabelEquiv G C hACard
        (hLabelEquiv G C hHCard
          (sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hA1Card))
          (sortedHFinsetEquiv G C C.X (finsetEquivFin C.X hXCard)))
        (finsetEquivFin C.R hRCard)) ⟨q + 4, by omega⟩).1 ≤
    hDegreeKey G C
      ((aLabelEquiv G C hACard
        (hLabelEquiv G C hHCard
          (sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hA1Card))
          (sortedHFinsetEquiv G C C.X (finsetEquivFin C.X hXCard)))
        (finsetEquivFin C.R hRCard)) ⟨q + 3, by omega⟩).1
  simpa [aLabelEquiv, hLabelEquiv, show q + 4 ≠ 0 by omega,
    show q + 4 ≤ 6 by omega, show q + 3 ≠ 0 by omega,
    show q + 3 ≤ 6 by omega, show ¬q + 3 - 1 < 2 by omega,
    show ¬q + 4 - 1 < 2 by omega, show ¬q + 3 < 2 by omega] using hKey

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLabels
