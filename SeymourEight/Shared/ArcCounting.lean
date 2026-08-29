import SeymourEight.Shared.Neighborhood
import SeymourEight.Shared.InternalNeighborhood
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option linter.style.header false

/-!
# Shared arc counting

Generic finite-set identities and capacity bounds for directed arc counts.
-/

namespace SeymourEight.Shared

open CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- `e_p` is one exactly when `p → s`. -/
def epsilonAt (p s : V) : Nat :=
  if G.Adj p s then 1 else 0

/-- The number of direct outneighbors of `p` lying in `S`. -/
def directCount (S : Finset V) (p : V) : Nat :=
  (internalFirstNeighbors G S p).card

/-- Number of directed arcs from `S` to `T`. -/
def edgeCount (S T : Finset V) : Nat :=
  ∑ u ∈ S, directCount G T u

/-- Number of arcs from `S` entering `v`. -/
def internalInDegree (S : Finset V) (v : V) : Nat :=
  (S.filter fun u ↦ G.Adj u v).card

omit [DecidableEq V] in
/-- If a finite set captures every outgoing arc, its direct count is the
whole outdegree. -/
theorem outdegree_eq_directCount_of_captured (S : Finset V) (p : V)
    (hCaptured : G.outNeighborFinset p ⊆ S) :
    G.outdegree p = directCount G S p := by
  unfold Digraph.outdegree directCount internalFirstNeighbors
  congr 1
  ext v
  simp only [Finset.mem_filter, Digraph.mem_outNeighborFinset]
  constructor
  · intro hpv
    exact ⟨hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv), hpv⟩
  · exact fun hv ↦ hv.2

omit [Fintype V] [DecidableEq V] in
/-- Double-counting internal arcs by tails or by heads gives the same result. -/
theorem edgeCount_eq_sum_internalInDegree (S : Finset V) :
    edgeCount G S S = ∑ v ∈ S, internalInDegree G S v := by
  classical
  simpa [edgeCount, directCount, internalFirstNeighbors, internalInDegree,
    Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := S) (t := S) G.Adj)

omit [Fintype V] [DecidableEq V] in
/-- Double-counting arcs from `S` to `T` by their heads. -/
theorem edgeCount_eq_sum_incoming (S T : Finset V) :
    edgeCount G S T = ∑ v ∈ T, internalInDegree G S v := by
  classical
  simpa [edgeCount, directCount, CertificateBridge.internalFirstNeighbors,
    internalInDegree, Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := S) (t := T) G.Adj)

omit [Fintype V] [DecidableEq V] in
/-- In an oriented graph, the internal in- and outneighbors of `v` are disjoint. -/
theorem disjoint_internal_out_in (S : Finset V) (v : V)
    (hG : G.IsOriented) :
    Disjoint (internalFirstNeighbors G S v) (S.filter fun u ↦ G.Adj u v) := by
  classical
  rw [Finset.disjoint_left]
  intro u huOut huIn
  exact hG.2 (Finset.mem_filter.mp huOut).2 (Finset.mem_filter.mp huIn).2

omit [Fintype V] in
/-- Every internal neighbor incident with `v` lies in `S.erase v`. -/
theorem internal_incident_subset_erase (S : Finset V) (v : V)
    (hG : G.IsOriented) :
    internalFirstNeighbors G S v ∪ (S.filter fun u ↦ G.Adj u v) ⊆ S.erase v := by
  intro u hu
  apply Finset.mem_erase.mpr
  rcases Finset.mem_union.mp hu with huOut | huIn
  · refine ⟨?_, (Finset.mem_filter.mp huOut).1⟩
    intro huv
    subst u
    exact hG.1 v (Finset.mem_filter.mp huOut).2
  · refine ⟨?_, (Finset.mem_filter.mp huIn).1⟩
    intro huv
    subst u
    exact hG.1 v (Finset.mem_filter.mp huIn).2

omit [Fintype V] [DecidableEq V] in
/-- A bipartite arc count is at most the number of possible ordered pairs. -/
theorem edgeCount_le_card_mul_card (S T : Finset V) :
    edgeCount G S T ≤ S.card * T.card := by
  classical
  unfold edgeCount directCount CertificateBridge.internalFirstNeighbors
  calc
    (∑ u ∈ S, (T.filter fun v ↦ G.Adj u v).card) ≤
        ∑ _u ∈ S, T.card := by
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = S.card * T.card := by simp

omit [Fintype V] [DecidableEq V] in
/-- Across disjoint classes, an oriented graph uses at most one direction per pair. -/
theorem cross_edgeCount_add_reverse_le (S T : Finset V)
    (hG : G.IsOriented) :
    edgeCount G S T + edgeCount G T S ≤ S.card * T.card := by
  classical
  have hIncident : ∀ v ∈ T,
      directCount G S v + internalInDegree G S v ≤ S.card := by
    intro v hv
    have hDisjoint : Disjoint
        (CertificateBridge.internalFirstNeighbors G S v)
        (S.filter fun u ↦ G.Adj u v) := by
      rw [Finset.disjoint_left]
      intro u huOut huIn
      exact hG.2 (Finset.mem_filter.mp huOut).2
        (Finset.mem_filter.mp huIn).2
    calc
      directCount G S v + internalInDegree G S v =
          (CertificateBridge.internalFirstNeighbors G S v ∪
            (S.filter fun u ↦ G.Adj u v)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
        rfl
      _ ≤ S.card := Finset.card_le_card (by
        intro u hu
        rcases Finset.mem_union.mp hu with huOut | huIn
        · exact (Finset.mem_filter.mp huOut).1
        · exact (Finset.mem_filter.mp huIn).1)
  calc
    edgeCount G S T + edgeCount G T S =
        ∑ v ∈ T, (internalInDegree G S v + directCount G S v) := by
      rw [edgeCount_eq_sum_incoming G S T]
      unfold edgeCount
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ _v ∈ T, S.card := by
      apply Finset.sum_le_sum
      intro v hv
      simpa [Nat.add_comm] using hIncident v hv
    _ = S.card * T.card := by
      simp [Nat.mul_comm]

omit [Fintype V] [DecidableEq V] in
/-- An oriented graph has at most `choose |S| 2` internal arcs on `S`. -/
theorem internal_edgeCount_le_choose_two (S : Finset V)
    (hG : G.IsOriented) :
    edgeCount G S S ≤ S.card.choose 2 := by
  classical
  have hIncident : ∀ v ∈ S,
      directCount G S v + internalInDegree G S v ≤ S.card - 1 := by
    intro v hv
    have hDisjoint := disjoint_internal_out_in G S v hG
    have hSubset := internal_incident_subset_erase G S v hG
    calc
      directCount G S v + internalInDegree G S v =
          (CertificateBridge.internalFirstNeighbors G S v ∪
            (S.filter fun u ↦ G.Adj u v)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
        rfl
      _ ≤ (S.erase v).card := Finset.card_le_card hSubset
      _ = S.card - 1 := Finset.card_erase_of_mem hv
  have hSumLe :
      ∑ v ∈ S, (directCount G S v + internalInDegree G S v) ≤
        S.card * (S.card - 1) := by
    calc
      (∑ v ∈ S, (directCount G S v + internalInDegree G S v)) ≤
          ∑ _v ∈ S, (S.card - 1) := by
        apply Finset.sum_le_sum
        exact hIncident
      _ = S.card * (S.card - 1) := by simp
  rw [Finset.sum_add_distrib, ← edgeCount,
    ← edgeCount_eq_sum_internalInDegree (G := G)] at hSumLe
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  omega

omit [Fintype V] in
/-- Direct-neighbor counts add across disjoint target sets. -/
theorem directCount_union_of_disjoint (S T : Finset V) (p : V)
    (hST : Disjoint S T) :
    directCount G (S ∪ T) p = directCount G S p + directCount G T p := by
  unfold directCount CertificateBridge.internalFirstNeighbors
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hST)]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem directCount_singleton (s p : V) :
    directCount G {s} p = epsilonAt G p s := by
  classical
  simp only [directCount, CertificateBridge.internalFirstNeighbors,
    Finset.filter_singleton, epsilonAt]
  split <;> simp

omit [Fintype V] in
/-- Arc counts add across disjoint target sets. -/
theorem edgeCount_union_of_disjoint (P S T : Finset V)
    (hST : Disjoint S T) :
    edgeCount G P (S ∪ T) = edgeCount G P S + edgeCount G P T := by
  unfold edgeCount
  simp_rw [directCount_union_of_disjoint (G := G) S T _ hST]
  simp only [Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
/-- Counting arcs from `P` to the singleton root gives the sum of `e_p`. -/
theorem edgeCount_singleton (P : Finset V) (s : V) :
    edgeCount G P {s} = ∑ p ∈ P, epsilonAt G p s := by
  classical
  unfold edgeCount
  simp_rw [directCount_singleton (G := G)]

end SeymourEight.Shared
