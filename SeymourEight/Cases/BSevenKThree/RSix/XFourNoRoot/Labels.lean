import SeymourEight.Cases.BSevenKThree.Basic
import SeymourEight.Cases.BSixKThree.CoreGraphBridge
import SeymourEight.Shared.CertificateLabels
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Labels

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (zCount : Nat) (C : G.LocalConfiguration) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  q : Fin 1 ≃ {v : V // v ∈ C.Q}
  z : Fin zCount ≃ {v : V // v ∈ externalTargets G C}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 3, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 4, (a ⟨i.val + 4, by omega⟩).1 ∈ C.X

def sortPermutation {n : Nat} {alpha : Type*} [LinearOrder alpha]
    (key : Fin n → alpha) : Equiv.Perm (Fin n) :=
  Tuple.sort fun i ↦ OrderDual.toDual (key i)

noncomputable def sortedFinsetEquiv {n : Nat} {alpha : Type*} [LinearOrder alpha]
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S}) (key : V → alpha) :
    Fin n ≃ {v : V // v ∈ S} :=
  (sortPermutation fun i ↦ key (e i).1).trans e

omit [Fintype V] [DecidableEq V] in
theorem sortedFinsetEquiv_key_anti {n : Nat} {alpha : Type*} [LinearOrder alpha]
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S}) (key : V → alpha)
    {i j : Fin n} (hij : i ≤ j) :
    key (sortedFinsetEquiv S e key i).1 ≥
      key (sortedFinsetEquiv S e key j).1 := by
  classical
  exact Tuple.monotone_sort (fun k ↦ OrderDual.toDual (key (e k).1)) hij

def pInvariantKey (C : G.LocalConfiguration) (q : V) (v : V) : Nat :=
  (directCount G C.P v + directCount G C.H v +
      directCount G (externalTargets G C) v +
      (if G.Adj v q then 1 else 0)) * 65536 +
    directCount G (externalTargets G C) v * 4096 +
      (if G.Adj v q then 1 else 0) * 2048 +
    directCount G C.A1 v * 256 + directCount G C.X v * 16 +
    directCount G C.P v

def aInvariantKey (C : G.LocalConfiguration) (v : V) : Nat :=
  directCount G C.B v

def zInvariantKey (C : G.LocalConfiguration) (v : V) : Nat :=
  edgeCount G C.P {v}

noncomputable def canonicalLabels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) : Labels G zCount C := by
  let q := finsetEquivFin C.Q hQCard
  let pRaw := finsetEquivFin C.P hPCard
  let p := sortedFinsetEquiv C.P pRaw (pInvariantKey G C (q 0).1)
  let aOneRaw := finsetEquivFin C.A1 hA1Card
  let aOne := sortedFinsetEquiv C.A1 aOneRaw (aInvariantKey G C)
  let xRaw := finsetEquivFin C.X hXCard
  let x := sortedFinsetEquiv C.X xRaw (aInvariantKey G C)
  let r := finsetEquivFin C.R hRCard
  let a := BSixKThreeCoreGraphBridge.aLabelEquiv G C (by omega : 4 ≤ 4)
    hACard aOne x r
  let zRaw := finsetEquivFin (externalTargets G C) hZCard
  let z := sortedFinsetEquiv (externalTargets G C) zRaw (zInvariantKey G C)
  refine ⟨p, a, q, z, ?_, ?_, ?_⟩
  · simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel,       show i.val ≤ 2 by omega]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel,       show i.val + 4 < 8 by omega]

theorem canonicalLabels_p_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (q : Fin 5) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    pInvariantKey G C (L.q 0).1 (L.p ⟨q.val + 1, by omega⟩).1 ≤
      pInvariantKey G C (L.q 0).1 (L.p ⟨q.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti C.P (finsetEquivFin C.P hPCard)
    (pInvariantKey G C
      ((finsetEquivFin C.Q hQCard) 0).1)
    (i := ⟨q.val, by omega⟩) (j := ⟨q.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

@[simp] theorem canonicalLabels_aOne (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (i : Fin 3) :
    ((canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard).a ⟨i.val + 1, by omega⟩).1 =
      (sortedFinsetEquiv C.A1 (finsetEquivFin C.A1 hA1Card)
        (aInvariantKey G C) i).1 := by
  simp [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, show i.val ≤ 2 by omega]

@[simp] theorem canonicalLabels_x (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (i : Fin 4) :
    ((canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard).a ⟨i.val + 4, by omega⟩).1 =
      (sortedFinsetEquiv C.X (finsetEquivFin C.X hXCard)
        (aInvariantKey G C) i).1 := by
  simp [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, show i.val + 4 < 8 by omega]

theorem canonicalLabels_aOne_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (q : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
      aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1 := by
  dsimp only
  have hFin : (⟨q.val + 2, by omega⟩ : Fin 8) =
      ⟨(q.val + 1) + 1, by omega⟩ := Fin.ext (by simp)
  rw [hFin, canonicalLabels_aOne G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨q.val + 1, by omega⟩,
    canonicalLabels_aOne G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨q.val, by omega⟩]
  exact sortedFinsetEquiv_key_anti C.A1 (finsetEquivFin C.A1 hA1Card)
    (aInvariantKey G C) (i := ⟨q.val, by omega⟩)
      (j := ⟨q.val + 1, by omega⟩) (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_x_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (q : Fin 3) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
      aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1 := by
  dsimp only
  have hFin : (⟨q.val + 5, by omega⟩ : Fin 8) =
      ⟨(q.val + 1) + 4, by omega⟩ := Fin.ext (by simp)
  rw [hFin, canonicalLabels_x G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨q.val + 1, by omega⟩,
    canonicalLabels_x G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨q.val, by omega⟩]
  exact sortedFinsetEquiv_key_anti C.X (finsetEquivFin C.X hXCard)
    (aInvariantKey G C) (i := ⟨q.val, by omega⟩)
      (j := ⟨q.val + 1, by omega⟩) (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_z_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (q : Fin (zCount - 1)) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    zInvariantKey G C (L.z ⟨q.val + 1, by omega⟩).1 ≤
      zInvariantKey G C (L.z ⟨q.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti (externalTargets G C)
    (finsetEquivFin (externalTargets G C) hZCard)
    (zInvariantKey G C) (i := ⟨q.val, by omega⟩)
      (j := ⟨q.val + 1, by omega⟩) (Fin.mk_le_mk.mpr (by omega))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Labels
