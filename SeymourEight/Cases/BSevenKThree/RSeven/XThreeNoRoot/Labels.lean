import SeymourEight.Cases.BSevenKThree.Basic
import SeymourEight.Cases.BSixKThree.CoreGraphBridge
import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.SymmetryDefs
import SeymourEight.Shared.CertificateLabels
import SeymourEight.Shared.FinsetBridge
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

/-!
# Canonical labels for the no-root `r = 7`, `x = 3` core

The fixed `A` layout is `a1, A1[3], X[3], R[1]`.  The classes on which
the finite predicate has permutation symmetry are sorted by the exact keys
used in the certificate.
-/

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Labels

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (zCount : Nat) (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin zCount ≃ {v : V // v ∈ externalTargets G C}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 3, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 3, (a ⟨i.val + 4, by omega⟩).1 ∈ C.X
  a_r : (a 7).1 ∈ C.R

def incomingCount (S : Finset V) (v : V) : Nat :=
  ∑ u ∈ S, if G.Adj u v then 1 else 0

def pInvariantKey (C : G.LocalConfiguration) (v : V) : Nat :=
  ((((((directCount G C.P v + directCount G C.H v +
      directCount G (externalTargets G C) v) * 8 +
    directCount G (externalTargets G C) v) * 8 +
    directCount G C.H v) * 8 + directCount G C.P v) * 8 +
    incomingCount G C.P v) * 8 + incomingCount G C.H v)

def sortPermutation {n : Nat} {α : Type*} [LinearOrder α]
    (key : Fin n → α) : Equiv.Perm (Fin n) :=
  Tuple.sort fun i => OrderDual.toDual (key i)

noncomputable def sortedFinsetEquiv {n : Nat} {α : Type*} [LinearOrder α]
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S}) (key : V → α) :
    Fin n ≃ {v : V // v ∈ S} :=
  (sortPermutation fun i => key (e i).1).trans e

omit [Fintype V] [DecidableEq V] in
theorem sortedFinsetEquiv_key_anti {n : Nat} {α : Type*} [LinearOrder α]
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S}) (key : V → α)
    {i j : Fin n} (hij : i ≤ j) :
    key (sortedFinsetEquiv S e key i).1 ≥
      key (sortedFinsetEquiv S e key j).1 := by
  classical
  exact Tuple.monotone_sort (fun q => OrderDual.toDual (key (e q).1)) hij

def hIncidenceCode (p : Fin 7 → V) (v : V) : BitVec 14 :=
  BitVec.ofFnLE fun i : Fin 14 =>
    if hi : i.val < 7 then decide (G.Adj v (p ⟨i.val, hi⟩))
    else decide (G.Adj (p ⟨i.val - 7, by omega⟩) v)

def hInvariantKey (C : G.LocalConfiguration) (p : Fin 7 → V)
    (v : V) : BitVec 32 :=
  (((BitVec.ofNat 8 (directCount G C.P v)).zeroExtend 32 * 8 +
      (BitVec.ofNat 8 (directCount G C.A v)).zeroExtend 32) * 16384) +
    (hIncidenceCode G p v).zeroExtend 32

def zIncidenceCode (p : Fin 7 → V) (v : V) : BitVec 7 :=
  BitVec.ofFnLE fun i : Fin 7 => decide (G.Adj (p i) v)

noncomputable def canonicalLabels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) : Labels G zCount C := by
  let ePRaw := finsetEquivFin C.P hPCard
  let p := sortedFinsetEquiv C.P ePRaw (pInvariantKey G C)
  let eA1Raw := finsetEquivFin C.A1 hA1Card
  let eA1 := sortedFinsetEquiv C.A1 eA1Raw
    (fun v => (hInvariantKey G C (fun i => (p i).1) v).toNat)
  let eXRaw := finsetEquivFin C.X hXCard
  let eX := sortedFinsetEquiv C.X eXRaw
    (fun v => (hInvariantKey G C (fun i => (p i).1) v).toNat)
  let eR := finsetEquivFin C.R hRCard
  let a := BSixKThreeCoreGraphBridge.aLabelEquiv G C (by omega : 3 ≤ 4)
    hACard eA1 eX eR
  let eZRaw := finsetEquivFin (externalTargets G C) hZCard
  let z := sortedFinsetEquiv (externalTargets G C) eZRaw
    (fun v => (zIncidenceCode G (fun i => (p i).1) v).toNat)
  refine {
    p := p
    a := a
    z := z
    a_zero := ?_
    a_aOne := ?_
    a_x := ?_
    a_r := ?_ }
  · simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel,       show i.val ≤ 2 by omega]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel,       show i.val + 4 < 7 by omega]
  · simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel]

theorem canonicalLabels_p_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 6) :
    pInvariantKey G C
        ((canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard).p
          ⟨q.val + 1, by omega⟩).1 ≤
      pInvariantKey G C
        ((canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard).p
          ⟨q.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti C.P (finsetEquivFin C.P hPCard)
    (pInvariantKey G C) (i := ⟨q.val, by omega⟩)
      (j := ⟨q.val + 1, by omega⟩) (Fin.mk_le_mk.mpr (by omega))

@[simp] theorem canonicalLabels_aOne (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) (i : Fin 3) :
    ((canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard).a
      ⟨i.val + 1, by omega⟩).1 =
    (sortedFinsetEquiv C.A1 (finsetEquivFin C.A1 hA1Card)
      (fun v => (hInvariantKey G C (fun j =>
        ((sortedFinsetEquiv C.P (finsetEquivFin C.P hPCard)
          (pInvariantKey G C)) j).1) v).toNat) i).1 := by
  simp [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, show i.val ≤ 2 by omega]

@[simp] theorem canonicalLabels_x (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) (i : Fin 3) :
    ((canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard).a
      ⟨i.val + 4, by omega⟩).1 =
    (sortedFinsetEquiv C.X (finsetEquivFin C.X hXCard)
      (fun v => (hInvariantKey G C (fun j =>
        ((sortedFinsetEquiv C.P (finsetEquivFin C.P hPCard)
          (pInvariantKey G C)) j).1) v).toNat) i).1 := by
  simp [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel]

theorem canonicalLabels_aOne_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard
    (hInvariantKey G C (fun i => (L.p i).1)
      (L.a ⟨q.val + 2, by omega⟩).1).toNat ≤
      (hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 1, by omega⟩).1).toNat := by
  dsimp only
  have hFin : (⟨q.val + 2, by omega⟩ : Fin 8) =
      ⟨(q.val + 1) + 1, by omega⟩ :=
    Fin.ext (show q.val + 2 = (q.val + 1) + 1 by omega)
  rw [hFin, canonicalLabels_aOne G zCount C hPCard hACard hA1Card hXCard
      hRCard hZCard ⟨q.val + 1, by omega⟩,
    canonicalLabels_aOne G zCount C hPCard hACard hA1Card hXCard
      hRCard hZCard ⟨q.val, by omega⟩]
  exact sortedFinsetEquiv_key_anti C.A1 (finsetEquivFin C.A1 hA1Card)
    (fun v => (hInvariantKey G C (fun j =>
      ((sortedFinsetEquiv C.P (finsetEquivFin C.P hPCard)
        (pInvariantKey G C)) j).1) v).toNat)
    (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_x_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard
    (hInvariantKey G C (fun i => (L.p i).1)
      (L.a ⟨q.val + 5, by omega⟩).1).toNat ≤
      (hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 4, by omega⟩).1).toNat := by
  dsimp only
  have hFin : (⟨q.val + 5, by omega⟩ : Fin 8) =
      ⟨(q.val + 1) + 4, by omega⟩ :=
    Fin.ext (show q.val + 5 = (q.val + 1) + 4 by omega)
  rw [hFin, canonicalLabels_x G zCount C hPCard hACard hA1Card hXCard
      hRCard hZCard ⟨q.val + 1, by omega⟩,
    canonicalLabels_x G zCount C hPCard hACard hA1Card hXCard
      hRCard hZCard ⟨q.val, by omega⟩]
  exact sortedFinsetEquiv_key_anti C.X (finsetEquivFin C.X hXCard)
    (fun v => (hInvariantKey G C (fun j =>
      ((sortedFinsetEquiv C.P (finsetEquivFin C.P hPCard)
        (pInvariantKey G C)) j).1) v).toNat)
    (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_z_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1)
    (hZCard : (externalTargets G C).card = zCount) (q : Fin (zCount - 1)) :
    let L := canonicalLabels G zCount C hPCard hACard hA1Card hXCard hRCard hZCard
    (zIncidenceCode G (fun i => (L.p i).1)
      (L.z ⟨q.val + 1, by omega⟩).1).toNat ≤
      (zIncidenceCode G (fun i => (L.p i).1)
        (L.z ⟨q.val, by omega⟩).1).toNat := by
  dsimp only
  exact sortedFinsetEquiv_key_anti (externalTargets G C)
    (finsetEquivFin (externalTargets G C) hZCard)
    (fun v => (zIncidenceCode G (fun j =>
      ((sortedFinsetEquiv C.P (finsetEquivFin C.P hPCard)
        (pInvariantKey G C)) j).1) v).toNat)
    (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Labels
