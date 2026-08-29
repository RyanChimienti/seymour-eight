import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.HighDefect.Encoding
import SeymourEight.Shared.LocalDegree

set_option linter.style.header false

namespace SeymourEight.FiveZHighDefectGraphBridge

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every outgoing arc of a root outneighbor lands in `A ∪ B`. -/
theorem A_outgoingCaptured (C : G.LocalConfiguration) (hG : G.IsOriented)
    (u : V) (huA : u ∈ C.A) :
    G.outNeighborFinset u ⊆ C.A ∪ C.B := by
  intro v huvOut
  have huv : G.Adj u v :=
    (Digraph.mem_outNeighborFinset (G := G)).mp huvOut
  by_cases hvA : v ∈ C.A
  · exact Finset.mem_union_left C.B hvA
  have hsu : G.Adj C.s u :=
    (Digraph.mem_outNeighborFinset (G := G)).mp huA
  have hvs : v ≠ C.s := by
    intro h
    subst v
    exact hG.2 hsu huv
  have hvB : v ∈ C.B := by
    rw [Digraph.LocalConfiguration.B,
      Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨u, hsu, huv⟩,
      fun hsv ↦ hvA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv), hvs⟩
  exact Finset.mem_union_right C.A hvB

/-- If `P = B`, an `A`-vertex's represented degree is its actual degree. -/
theorem A_outdegree_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (u : V) (huA : u ∈ C.A) :
    G.outdegree u = directCount G C.A u + directCount G C.P u := by
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hEq : G.outNeighborFinset u =
      (C.A ∪ C.P).filter fun v ↦ G.Adj u v := by
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro huv
      have hvCaptured := A_outgoingCaptured G C hG u huA
        ((Digraph.mem_outNeighborFinset (G := G)).mpr huv)
      exact ⟨by simpa [hPB] using hvCaptured, huv⟩
    · exact fun hv ↦ hv.2
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  rw [hEq, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (p := fun v ↦ G.Adj u v)
        (q := fun v ↦ G.Adj u v) hAP)]

theorem P_not_adj_R (C : G.LocalConfiguration)
    (p r : V) (hp : p ∈ C.P) (hr : r ∈ C.R) : ¬G.Adj p r := by
  intro hpr
  have hrX : r ∈ C.X := by
    apply Finset.mem_inter.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨p, Finset.mem_union_right C.A1 hp, hpr⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
      intro hParts
      apply (Finset.mem_sdiff.mp hr).2
      rcases Finset.mem_union.mp hParts with hrA1 | hra1
      · exact Finset.mem_union_left {C.a1}
          (Finset.mem_union_left C.X hrA1)
      · exact Finset.mem_union_right (C.A1 ∪ C.X) hra1
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))

theorem A_not_adj_Z (C : G.LocalConfiguration) (_hG : G.IsOriented)
    (a z : V) (ha : a ∈ C.A) (hz : z ∈ C.Z) : ¬G.Adj a z := by
  intro haz
  have hsa : G.Adj C.s a :=
    (Digraph.mem_outNeighborFinset (G := G)).mp ha
  have hzNotA : z ∉ C.A := by
    intro hzA
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
        (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hzA))
  have hzNotS : z ≠ C.s := by
    intro h
    subst z
    exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hz
  have hzB : z ∈ C.B := by
    rw [Digraph.LocalConfiguration.B,
      Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨a, hsa, haz⟩,
      fun hsz ↦ hzNotA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsz),
      hzNotS⟩
  exact (Finset.disjoint_left.mp
    (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
      (Finset.mem_union_right ({C.s} ∪ C.A) hzB)

end SeymourEight.FiveZHighDefectGraphBridge
