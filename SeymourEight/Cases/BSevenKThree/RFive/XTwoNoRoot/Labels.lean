import SeymourEight.Cases.BSevenKThree.Basic
import SeymourEight.Cases.BSixKThree.CoreGraphBridge
import SeymourEight.Shared.CertificateLabels

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Labels

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
  a_x : ∀ i : Fin 2, (a ⟨i.val + 4, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 2, (a ⟨i.val + 6, by omega⟩).1 ∈ C.R

noncomputable def labels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 5) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 2)
    (hZCard : (externalTargets G C).card = zCount)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 2)
    (hRCard : C.R.card = 2) : Labels G zCount C := by
  let p := finsetEquivFin C.P hPCard
  let q := finsetEquivFin C.Q hQCard
  let aOne := finsetEquivFin C.A1 hA1Card
  let x := finsetEquivFin C.X hXCard
  let r := finsetEquivFin C.R hRCard
  let a := BSixKThreeCoreGraphBridge.aLabelEquiv G C (by omega : 2 ≤ 4)
    hACard aOne x r
  let z := finsetEquivFin (externalTargets G C) hZCard
  refine ⟨p, a, q, z, ?_, ?_, ?_, ?_⟩
  · simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel,       show i.val ≤ 2 by omega]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel,       show i.val + 4 < 6 by omega]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel, Nat.add_comm]

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Labels
