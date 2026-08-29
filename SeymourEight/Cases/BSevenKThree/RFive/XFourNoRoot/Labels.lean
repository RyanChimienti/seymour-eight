import SeymourEight.Cases.BSevenKThree.Basic
import SeymourEight.Cases.BSixKThree.CoreGraphBridge
import SeymourEight.Shared.CertificateLabels
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (zCount : Nat) (C : G.LocalConfiguration) where
  p : Fin 5 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  q : Fin 2 ≃ {v : V // v ∈ C.Q}
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
    key (sortedFinsetEquiv S e key i).1 ≥ key (sortedFinsetEquiv S e key j).1 := by
  classical
  exact Tuple.monotone_sort (fun k ↦ OrderDual.toDual (key (e k).1)) hij

def pInvariantKey (C : G.LocalConfiguration) (v : V) : Nat :=
  (directCount G C.P v + directCount G C.H v + directCount G C.Q v +
      directCount G (externalTargets G C) v) * 65536 +
    directCount G (externalTargets G C) v * 4096 + directCount G C.Q v * 512 +
    directCount G C.A1 v * 64 + directCount G C.X v * 8 + directCount G C.P v

def aInvariantKey (C : G.LocalConfiguration) (v : V) : Nat := directCount G C.B v
def qInvariantKey (C : G.LocalConfiguration) (v : V) : Nat :=
  edgeCount G (C.A ∪ C.P) {v}
def zInvariantKey (C : G.LocalConfiguration) (v : V) : Nat := edgeCount G C.P {v}

noncomputable def canonicalLabels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8) (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hRCard : C.R.card = 0) :
    Labels G zCount C := by
  let p := sortedFinsetEquiv C.P (finsetEquivFin C.P hPCard) (pInvariantKey G C)
  let q := sortedFinsetEquiv C.Q (finsetEquivFin C.Q hQCard) (qInvariantKey G C)
  let aOne := sortedFinsetEquiv C.A1 (finsetEquivFin C.A1 hA1Card) (aInvariantKey G C)
  let x := sortedFinsetEquiv C.X (finsetEquivFin C.X hXCard) (aInvariantKey G C)
  let r := finsetEquivFin C.R hRCard
  let a := BSixKThreeCoreGraphBridge.aLabelEquiv G C (by omega : 4 ≤ 4)
    hACard aOne x r
  let z := sortedFinsetEquiv (externalTargets G C)
    (finsetEquivFin (externalTargets G C) hZCard) (zInvariantKey G C)
  refine ⟨p, a, q, z, ?_, ?_, ?_⟩
  · simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel, show i.val ≤ 2 by omega]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel, show i.val + 4 < 8 by omega]

theorem canonicalLabels_p_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8) (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hRCard : C.R.card = 0)
    (i : Fin 4) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard hA1Card hXCard hRCard
    pInvariantKey G C (L.p ⟨i.val + 1, by omega⟩).1 ≤
      pInvariantKey G C (L.p ⟨i.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti C.P (finsetEquivFin C.P hPCard)
    (pInvariantKey G C) (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_q_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8) (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hRCard : C.R.card = 0) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard hA1Card hXCard hRCard
    qInvariantKey G C (L.q 1).1 ≤ qInvariantKey G C (L.q 0).1 := by
  exact sortedFinsetEquiv_key_anti C.Q (finsetEquivFin C.Q hQCard)
    (qInvariantKey G C) (i := 0) (j := 1) (by omega)

theorem canonicalLabels_aOne_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8) (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hRCard : C.R.card = 0)
    (i : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard hA1Card hXCard hRCard
    aInvariantKey G C (L.a ⟨i.val + 2, by omega⟩).1 ≤
      aInvariantKey G C (L.a ⟨i.val + 1, by omega⟩).1 := by
  have h := sortedFinsetEquiv_key_anti C.A1 (finsetEquivFin C.A1 hA1Card)
    (aInvariantKey G C) (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))
  simpa [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, Nat.add_comm, show i.val ≤ 1 by omega,
    show i.val + 1 ≤ 2 by omega] using h

theorem canonicalLabels_x_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8) (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hRCard : C.R.card = 0)
    (i : Fin 3) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard hA1Card hXCard hRCard
    aInvariantKey G C (L.a ⟨i.val + 5, by omega⟩).1 ≤
      aInvariantKey G C (L.a ⟨i.val + 4, by omega⟩).1 := by
  have h := sortedFinsetEquiv_key_anti C.X (finsetEquivFin C.X hXCard)
    (aInvariantKey G C) (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))
  simpa [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, Nat.add_comm,
    show ¬(i.val + 4 < 4) by omega, show ¬(i.val + 5 < 4) by omega,
    show i.val + 4 < 8 by omega, show i.val + 5 < 8 by omega] using h

theorem canonicalLabels_z_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8) (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4) (hRCard : C.R.card = 0)
    (i : Fin (zCount - 1)) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard hA1Card hXCard hRCard
    zInvariantKey G C (L.z ⟨i.val + 1, by omega⟩).1 ≤
      zInvariantKey G C (L.z ⟨i.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti (externalTargets G C)
    (finsetEquivFin (externalTargets G C) hZCard) (zInvariantKey G C)
    (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels
