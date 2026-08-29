import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.Labels

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels

open Shared CertificateBridge
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (zCount : Nat) (C : G.LocalConfiguration) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  q : Fin 1 ≃ {v : V // v ∈ C.Q}
  z : Fin zCount ≃ {v : V // v ∈ externalTargets G C}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 3, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 3, (a ⟨i.val + 4, by omega⟩).1 ∈ C.X
  a_r : (a 7).1 ∈ C.R

noncomputable def canonicalLabels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) : Labels G zCount C := by
  let q := finsetEquivFin C.Q hQCard
  let pRaw := finsetEquivFin C.P hPCard
  let p := sortedFinsetEquiv C.P pRaw (pInvariantKey G C (q 0).1)
  let aOneRaw := finsetEquivFin C.A1 hA1Card
  let aOne := sortedFinsetEquiv C.A1 aOneRaw (aInvariantKey G C)
  let xRaw := finsetEquivFin C.X hXCard
  let x := sortedFinsetEquiv C.X xRaw (aInvariantKey G C)
  let r := finsetEquivFin C.R hRCard
  let a := BSixKThreeCoreGraphBridge.aLabelEquiv G C (by omega : 3 ≤ 4)
    hACard aOne x r
  let zRaw := finsetEquivFin (externalTargets G C) hZCard
  let z := sortedFinsetEquiv (externalTargets G C) zRaw (zInvariantKey G C)
  refine ⟨p, a, q, z, ?_, ?_, ?_, ?_⟩
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
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (i : Fin 5) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    pInvariantKey G C (L.q 0).1 (L.p ⟨i.val + 1, by omega⟩).1 ≤
      pInvariantKey G C (L.q 0).1 (L.p ⟨i.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti C.P (finsetEquivFin C.P hPCard)
    (pInvariantKey G C ((finsetEquivFin C.Q hQCard) 0).1)
    (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega))

@[simp] theorem canonicalLabels_aOne (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (i : Fin 3) :
    ((canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard).a ⟨i.val + 1, by omega⟩).1 =
      (sortedFinsetEquiv C.A1 (finsetEquivFin C.A1 hA1Card)
        (aInvariantKey G C) i).1 := by
  simp [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, show i.val ≤ 2 by omega]

@[simp] theorem canonicalLabels_x (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (i : Fin 3) :
    ((canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard).a ⟨i.val + 4, by omega⟩).1 =
      (sortedFinsetEquiv C.X (finsetEquivFin C.X hXCard)
        (aInvariantKey G C) i).1 := by
  simp [canonicalLabels, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
    BSixKThreeCoreGraphBridge.aLabel, show i.val + 4 < 7 by omega]

theorem canonicalLabels_aOne_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (i : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    aInvariantKey G C (L.a ⟨i.val + 2, by omega⟩).1 ≤
      aInvariantKey G C (L.a ⟨i.val + 1, by omega⟩).1 := by
  dsimp only
  rw [canonicalLabels_aOne G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨i.val + 1, by omega⟩,
    canonicalLabels_aOne G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨i.val, by omega⟩]
  exact sortedFinsetEquiv_key_anti C.A1 (finsetEquivFin C.A1 hA1Card)
    (aInvariantKey G C) (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_x_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (i : Fin 2) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    aInvariantKey G C (L.a ⟨i.val + 5, by omega⟩).1 ≤
      aInvariantKey G C (L.a ⟨i.val + 4, by omega⟩).1 := by
  dsimp only
  rw [canonicalLabels_x G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨i.val + 1, by omega⟩,
    canonicalLabels_x G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard ⟨i.val, by omega⟩]
  exact sortedFinsetEquiv_key_anti C.X (finsetEquivFin C.X hXCard)
    (aInvariantKey G C) (Fin.mk_le_mk.mpr (by omega))

theorem canonicalLabels_z_order (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (i : Fin (zCount - 1)) :
    let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
      hA1Card hXCard hRCard
    zInvariantKey G C (L.z ⟨i.val + 1, by omega⟩).1 ≤
      zInvariantKey G C (L.z ⟨i.val, by omega⟩).1 := by
  exact sortedFinsetEquiv_key_anti (externalTargets G C)
    (finsetEquivFin (externalTargets G C) hZCard) (zInvariantKey G C)
    (Fin.mk_le_mk.mpr (by omega))

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Labels
