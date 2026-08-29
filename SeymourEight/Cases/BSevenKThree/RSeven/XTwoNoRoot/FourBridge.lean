import SeymourEight.Cases.BSevenKThree.RSeven.XTwoNoRoot.Structure
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.GraphFacts
import SeymourEight.Reduction

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.FourBridge

open Shared Structure

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- With only four external targets, the seven vertices of `P` would have to
expand into the six-element set `X ∪ externalTargets`, contradicting the
degree-seven case. -/
theorem contradiction (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hPB : C.P = C.B)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 7)
    (hx : C.x = 2) (hExternal : (externalTargets G C).card = 4)
    (hNoSeymour : ¬G.HasSeymourVertex) : False := by
  let E := G.outNeighborFinsetOf C.P \ (C.P ∪ {C.a1})
  have hPCard : C.P.card = 7 := by simpa [hPB] using hBCard
  have hPSubset : (C.P : Set V) ⊆ G.outNeighborSet C.a1 := fun _ hp ↦
    (Finset.mem_filter.mp hp).2
  have hExpansion : 7 ≤ E.card := by
    simpa [E, hPCard] using
      Digraph.oneVertexReduction G hBound hG hNoSeymour hPSubset (by omega)
  have hESubset : E ⊆ C.X ∪ externalTargets G C := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp (Finset.mem_sdiff.mp hv).1
    have hcap := outgoingCaptured_of_p_eq_B G C hG hPB p hp
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
    simp only [Finset.mem_union, Finset.mem_singleton] at hcap
    rcases hcap with ((hvZ | hvs) | hvH) | hvP
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hvZ)
    · subst v
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      simp [rootSecondFinset, show ∃ q ∈ C.P, G.Adj q C.s from ⟨p, hp, hpv⟩]
    · rcases Finset.mem_union.mp hvH with hvA1 | hvX
      · exact False.elim
          (P_not_adj_A1 G C hG hPivot hBCard hk hr hx p v hp hvA1 hpv)
      · exact Finset.mem_union_left _ hvX
    · exact False.elim ((Finset.mem_sdiff.mp hv).2
        (Finset.mem_union_left _ hvP))
  have hUpper : E.card ≤ 6 := by
    have hCard := Finset.card_le_card hESubset
    have hUnion := Finset.card_union_le C.X (externalTargets G C)
    have hXCard : C.X.card = 2 := hx
    omega
  omega

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.FourBridge
