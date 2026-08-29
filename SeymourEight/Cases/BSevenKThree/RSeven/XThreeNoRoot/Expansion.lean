import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.GraphFacts
import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.ExpansionDefs
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Expansion

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The seven retained `P` outneighbors of `a₁` expand to at least seven
vertices by the already known degree-seven case. -/
theorem pUnionExpansion_true {zCount : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hZLe : zCount ≤ 6)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    pUnionExpansion zCount (graphBits G L) = true := by
  let E := G.outNeighborFinsetOf C.P \ (C.P ∪ {C.a1})
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr L.p).symm
  have hPSubset : (C.P : Set V) ⊆ G.outNeighborSet C.a1 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hExpansion : 7 ≤ E.card := by
    simpa [E, hPCard] using
      Digraph.oneVertexReduction G hBound hG hNoSeymour hPSubset (by omega)
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp (Finset.mem_sdiff.mp hv).1
    exact P_outgoingCaptured_retained G C hG hPB p hp
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
  have hCount : E.card ≤
      (count (15 + zCount) (pUnionTarget zCount (graphBits G L))).toNat := by
    have hFilter := filterCard_le_count (V := V)
      (retainedVertexSet G C) (retainedLabelEquiv G C L hG)
      (pUnionTarget zCount (graphBits G L)) (fun v ↦ v ∈ E) (by omega) (by
        intro target htE
        have htE' : labelledVertex G L target.val ∈ E := by
          rw [retainedLabelEquiv_val G C L hG] at htE
          exact htE
        have htNot : labelledVertex G L target.val ∉ C.P ∪ {C.a1} :=
          (Finset.mem_sdiff.mp htE').2
        have htZero : target.val ≠ 0 := by
          intro ht
          have htFin : target = 0 := Fin.ext ht
          subst target
          exact htNot (Finset.mem_union_right C.P (by simp [labelledVertex, L.a_zero]))
        have htClass : target.val < 8 ∨ 15 ≤ target.val := by
          by_contra h
          have htP : labelledVertex G L target.val ∈ C.P := by
            simp only [not_or, not_le] at h
            simp [labelledVertex, show ¬target.val < 8 by omega,
              show target.val < 15 by omega, (L.p ⟨target.val - 8, by omega⟩).2]
          exact htNot (Finset.mem_union_left _ htP)
        obtain ⟨p, hp, hpv⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp
            (Finset.mem_sdiff.mp htE').1
        obtain ⟨pi, hpi⟩ := L.p.surjective ⟨p, hp⟩
        rw [pUnionTarget, Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · simp [htZero, htClass]
        · rw [any_eq_true_iff]
          refine ⟨pi, pi.isLt, ?_⟩
          rw [coreArc_graphBits G C L hG hZLe (8 + pi.val) target.val
            (by omega) target.isLt]
          simpa [labelledVertex, show ¬8 + pi.val < 8 by omega,
            show 8 + pi.val < 15 by omega, congrArg Subtype.val hpi] using hpv)
    have hFilterEq :
        ((retainedVertexSet G C).filter fun v ↦ v ∈ E).card = E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hv ↦ ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    exact hFilter
  unfold pUnionExpansion
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  exact hExpansion.trans hCount

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Expansion
