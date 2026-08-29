import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Structure
import SeymourEight.Cases.BSixKThree.CoreGraphBridge
import SeymourEight.Certificates.BSevenKThree.RSeven.XTwo.CoreDefs
import SeymourEight.Shared.FinsetBridge

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Labels

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (zCount : Nat) (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin zCount ≃ {v : V // v ∈ externalTargets G C}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 3, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 2, (a ⟨i.val + 4, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 2, (a ⟨i.val + 6, by omega⟩).1 ∈ C.R

noncomputable def arbitraryLabels (zCount : Nat) (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 2)
    (hRCard : C.R.card = 2)
    (hZCard : (externalTargets G C).card = zCount) : Labels G zCount C := by
  let p := finsetEquivFin C.P hPCard
  let eA1 := finsetEquivFin C.A1 hA1Card
  let eX := finsetEquivFin C.X hXCard
  let eR := finsetEquivFin C.R hRCard
  let a := BSixKThreeCoreGraphBridge.aLabelEquiv G C (by omega : 2 ≤ 4)
    hACard eA1 eX eR
  let z := finsetEquivFin (externalTargets G C) hZCard
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
      BSixKThreeCoreGraphBridge.aLabel,       show i.val + 4 < 6 by omega]
  · intro i
    simp [a, BSixKThreeCoreGraphBridge.aLabelEquiv_apply,
      BSixKThreeCoreGraphBridge.aLabel, Nat.add_comm,
      show ¬i.val + 6 < 6 by omega]

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Labels
