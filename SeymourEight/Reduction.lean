import SeymourEight.Definitions

set_option linter.style.header false

/-!
# Restricting the arcs from one vertex

The one-vertex reduction in the degree-eight argument replaces all outgoing
arcs from a chosen vertex `v` except those aimed into a retained set `S`.
This file defines that operation and proves the neighborhood facts needed by
the reduction.
-/

namespace Digraph

variable {V : Type*} (G : Digraph V)

/-- Keep all arcs except that arcs with tail `v` are retained only when their head lies in `S`. -/
def restrictOutgoing (v : V) (S : Set V) : Digraph V where
  Adj x y := G.Adj x y ∧ (x = v → y ∈ S)

@[simp]
theorem restrictOutgoing_adj {v x y : V} {S : Set V} :
    (G.restrictOutgoing v S).Adj x y ↔ G.Adj x y ∧ (x = v → y ∈ S) :=
  Iff.rfl

instance {v : V} {S : Set V} [DecidableEq V] [DecidableRel G.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (G.restrictOutgoing v S).Adj := by
  intro x y
  change Decidable (G.Adj x y ∧ (x = v → y ∈ S))
  infer_instance

/-- Restricting arcs only deletes arcs. -/
theorem restrictOutgoing_le (v : V) (S : Set V) :
    G.restrictOutgoing v S ≤ G := by
  intro x y hxy
  exact hxy.1

@[simp]
theorem restrictOutgoing_adj_source {v w : V} {S : Set V} :
    (G.restrictOutgoing v S).Adj v w ↔ G.Adj v w ∧ w ∈ S := by
  simp [restrictOutgoing]

theorem restrictOutgoing_adj_of_ne {v x y : V} {S : Set V} (hx : x ≠ v) :
    (G.restrictOutgoing v S).Adj x y ↔ G.Adj x y := by
  simp [restrictOutgoing, hx]

/-- Away from the modified tail, first outneighborhoods are unchanged. -/
theorem outNeighborSet_restrictOutgoing_of_ne {v x : V} {S : Set V} (hx : x ≠ v) :
    (G.restrictOutgoing v S).outNeighborSet x = G.outNeighborSet x := by
  ext y
  exact restrictOutgoing_adj_of_ne G hx

/-- If `S` consists of original outneighbors of `v`, it is exactly the
outneighborhood of `v` after restriction. -/
theorem outNeighborSet_restrictOutgoing {v : V} {S : Set V}
    (hS : S ⊆ G.outNeighborSet v) :
    (G.restrictOutgoing v S).outNeighborSet v = S := by
  ext w
  simp only [mem_outNeighborSet, restrictOutgoing_adj_source]
  exact ⟨And.right, fun hw ↦ ⟨hS hw, hw⟩⟩

/-- If `v ∉ S`, restricting arcs from `v` does not change the arcs leaving members of `S`. -/
theorem outNeighborSetOf_restrictOutgoing {v : V} {S : Set V} (hv : v ∉ S) :
    (G.restrictOutgoing v S).outNeighborSetOf S = G.outNeighborSetOf S := by
  ext w
  constructor
  · rintro ⟨u, huS, huw⟩
    exact ⟨u, huS, (G.restrictOutgoing_le v S) huw⟩
  · rintro ⟨u, huS, huw⟩
    have huv : u ≠ v := by
      intro h
      subst u
      exact hv huS
    exact ⟨u, huS, (restrictOutgoing_adj_of_ne G huv).2 huw⟩

/-- The exact strict second neighborhood of the modified vertex. -/
theorem secondOutNeighborSet_restrictOutgoing {v : V} {S : Set V}
    (hS : S ⊆ G.outNeighborSet v) (hv : v ∉ S) :
    (G.restrictOutgoing v S).secondOutNeighborSet v =
      G.outNeighborSetOf S \ (S ∪ {v}) := by
  rw [secondOutNeighborSet, outNeighborSet_restrictOutgoing G hS,
    outNeighborSetOf_restrictOutgoing G hv]

/-- Restoring the deleted arcs can only enlarge the strict second neighborhood of another vertex. -/
theorem secondOutNeighborSet_restrictOutgoing_subset {v x : V} {S : Set V}
    (hx : x ≠ v) :
    (G.restrictOutgoing v S).secondOutNeighborSet x ⊆ G.secondOutNeighborSet x := by
  intro w hw
  rw [mem_secondOutNeighborSet] at hw ⊢
  obtain ⟨⟨u, hxu, huw⟩, hxw, hwx⟩ := hw
  refine ⟨⟨u, (G.restrictOutgoing_le v S) hxu,
    (G.restrictOutgoing_le v S) huw⟩, ?_, hwx⟩
  intro h
  exact hxw ((restrictOutgoing_adj_of_ne G hx).2 h)

/-- Restricting outgoing arcs preserves orientedness. -/
theorem IsOriented.restrictOutgoing {v : V} {S : Set V} (hG : G.IsOriented) :
    (G.restrictOutgoing v S).IsOriented := by
  constructor
  · intro x hxx
    exact hG.1 x ((G.restrictOutgoing_le v S) hxx)
  · intro x y hxy hyx
    exact hG.2 ((G.restrictOutgoing_le v S) hxy) ((G.restrictOutgoing_le v S) hyx)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The retained finite set is exactly the modified vertex's first outneighborhood. -/
theorem outNeighborFinset_restrictOutgoing {v : V} {S : Finset V}
    (hS : (S : Set V) ⊆ G.outNeighborSet v) :
    (G.restrictOutgoing v S).outNeighborFinset v = S := by
  ext w
  simp only [mem_outNeighborFinset, restrictOutgoing_adj_source, Finset.mem_coe]
  exact ⟨And.right, fun hw ↦ ⟨hS hw, hw⟩⟩

/-- The modified vertex has outdegree `|S|`. -/
theorem outdegree_restrictOutgoing {v : V} {S : Finset V}
    (hS : (S : Set V) ⊆ G.outNeighborSet v) :
    (G.restrictOutgoing v S).outdegree v = S.card := by
  unfold outdegree
  rw [outNeighborFinset_restrictOutgoing G hS]

/-- First outdegrees away from the modified tail are unchanged. -/
theorem outdegree_restrictOutgoing_of_ne {v x : V} {S : Finset V} (hx : x ≠ v) :
    (G.restrictOutgoing v S).outdegree x = G.outdegree x := by
  unfold outdegree
  congr 1
  ext w
  simp only [mem_outNeighborFinset]
  exact restrictOutgoing_adj_of_ne G hx

/-- Strict second outneighborhoods away from the modified tail only shrink. -/
theorem secondOutNeighborFinset_restrictOutgoing_subset {v x : V} {S : Finset V}
    (hx : x ≠ v) :
    (G.restrictOutgoing v S).secondOutNeighborFinset x ⊆
      G.secondOutNeighborFinset x := by
  intro w hw
  simp only [mem_secondOutNeighborFinset] at hw ⊢
  exact secondOutNeighborSet_restrictOutgoing_subset G hx hw

/-- Strict second outdegrees away from the modified tail only shrink. -/
theorem secondOutdegree_restrictOutgoing_le {v x : V} {S : Finset V} (hx : x ≠ v) :
    (G.restrictOutgoing v S).secondOutdegree x ≤ G.secondOutdegree x := by
  unfold secondOutdegree
  exact Finset.card_le_card (secondOutNeighborFinset_restrictOutgoing_subset G hx)

/-- A Seymour vertex away from the modified tail remains Seymour when deleted arcs are restored. -/
theorem IsSeymourVertex.of_restrictOutgoing {v x : V} {S : Finset V} (hx : x ≠ v)
    (hSeymour : (G.restrictOutgoing v S).IsSeymourVertex x) :
    G.IsSeymourVertex x := by
  unfold IsSeymourVertex at hSeymour ⊢
  rw [outdegree_restrictOutgoing_of_ne G hx] at hSeymour
  exact hSeymour.trans (secondOutdegree_restrictOutgoing_le G hx)

/-- The exact finite strict second neighborhood of the modified vertex. -/
theorem secondOutNeighborFinset_restrictOutgoing {v : V} {S : Finset V}
    (hS : (S : Set V) ⊆ G.outNeighborSet v) (hv : v ∉ S) :
    (G.restrictOutgoing v S).secondOutNeighborFinset v =
      G.outNeighborFinsetOf S \ (S ∪ {v}) := by
  ext w
  simp only [mem_secondOutNeighborFinset, Finset.mem_sdiff, mem_outNeighborFinsetOf,
    Finset.mem_union, Finset.mem_singleton]
  rw [secondOutNeighborSet_restrictOutgoing G hS (by simpa using hv)]
  aesop

/-- The exact strict second outdegree of the modified vertex. -/
theorem secondOutdegree_restrictOutgoing {v : V} {S : Finset V}
    (hS : (S : Set V) ⊆ G.outNeighborSet v) (hv : v ∉ S) :
    (G.restrictOutgoing v S).secondOutdegree v =
      (G.outNeighborFinsetOf S \ (S ∪ {v})).card := by
  unfold secondOutdegree
  rw [secondOutNeighborFinset_restrictOutgoing G hS hv]

/--
Logical core of the one-vertex reduction: if the original graph has no
Seymour vertex but the restricted graph does, the restricted vertex must be
Seymour and the retained set expands by at least its own cardinality.
-/
theorem oneVertexExpansion_of_hasSeymour {v : V} {S : Finset V}
    (hS : (S : Set V) ⊆ G.outNeighborSet v) (hv : v ∉ S)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRestricted : (G.restrictOutgoing v S).HasSeymourVertex) :
    S.card ≤ (G.outNeighborFinsetOf S \ (S ∪ {v})).card := by
  obtain ⟨w, hw⟩ := hRestricted
  have hwv : w = v := by
    by_contra hn
    exact hNoSeymour ⟨w, hw.of_restrictOutgoing G hn⟩
  subst w
  unfold IsSeymourVertex at hw
  rw [outdegree_restrictOutgoing G hS,
    secondOutdegree_restrictOutgoing G hS hv] at hw
  exact hw

/--
Oriented-graph form of the one-vertex expansion inequality.  Orientedness
automatically guarantees that the retained outneighbor set does not contain
the modified vertex.
-/
theorem oneVertexExpansion {v : V} {S : Finset V}
    (hG : G.IsOriented) (hS : (S : Set V) ⊆ G.outNeighborSet v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRestricted : (G.restrictOutgoing v S).HasSeymourVertex) :
    S.card ≤ (G.outNeighborFinsetOf S \ (S ∪ {v})).card := by
  apply oneVertexExpansion_of_hasSeymour G hS
  · intro hv
    exact hG.1 v (hS hv)
  · exact hNoSeymour
  · exact hRestricted

/--
The one-vertex reduction lemma.  If the Seymour conjecture is known through
minimum outdegree `h`, every retained set `S` of at most `h` outneighbors in a
counterexample expands to at least `|S|` vertices outside `S ∪ {v}`.
-/
theorem oneVertexReduction {h : ℕ} {v : V} {S : Finset V}
    (hBound : LimitedSeymourConjectureOn V h) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hS : (S : Set V) ⊆ G.outNeighborSet v) (hCard : S.card ≤ h) :
    S.card ≤ (G.outNeighborFinsetOf S \ (S ∪ {v})).card := by
  have hRestrictedOriented : (G.restrictOutgoing v S).IsOriented :=
    hG.restrictOutgoing
  have hRestrictedLowDegree :
      (G.restrictOutgoing v S).HasVertexWithOutdegreeAtMost h := by
    refine ⟨v, ?_⟩
    rw [outdegree_restrictOutgoing G hS]
    exact hCard
  have hRestrictedSeymour :
      (G.restrictOutgoing v S).HasSeymourVertex :=
    hBound (G.restrictOutgoing v S) hRestrictedOriented hRestrictedLowDegree
  exact oneVertexExpansion G hG hS hNoSeymour hRestrictedSeymour

/--
The exact one-arc deletion consequence used in the tight degree-eight rows.
Deleting `v → u` leaves the other seven outneighbors of a degree-eight
vertex, and the degree-seven theorem forces that retained set to expand to at
least seven strict second neighbors.
-/
theorem oneArcDeletionExpansion {v u : V}
    (hBound : LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree v = 8) (hu : G.Adj v u) :
    7 ≤
      (G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase u) \
        ((G.outNeighborFinset v |>.erase u) ∪ {v})).card := by
  let S := G.outNeighborFinset v |>.erase u
  have huMem : u ∈ G.outNeighborFinset v :=
    (mem_outNeighborFinset (G := G)).mpr hu
  have hS : (S : Set V) ⊆ G.outNeighborSet v := by
    intro w hw
    have hwOut : w ∈ G.outNeighborFinset v := Finset.mem_of_mem_erase hw
    exact (mem_outNeighborFinset (G := G)).mp hwOut
  have hCard : S.card = 7 := by
    rw [Finset.card_erase_of_mem huMem]
    change G.outdegree v - 1 = 7
    omega
  have hExpansion := oneVertexReduction G hBound hG hNoSeymour hS (by omega)
  simpa [S, hCard] using hExpansion

/--
Deleting one outgoing arc from an exact-degree-eight vertex loses at most one
of its original strict second neighbors.  The deleted head itself is the only
possible new strict second neighbor after the deletion.
-/
theorem oneArcDeletion_misses_at_most_one {v u : V}
    (hBound : LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree v = 8) (hu : G.Adj v u) :
    (G.secondOutNeighborFinset v \
      (G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase u) \
        ((G.outNeighborFinset v |>.erase u) ∪ {v}))).card ≤ 1 := by
  let U := G.outNeighborFinset v
  let S := U.erase u
  let E := G.outNeighborFinsetOf S \ (S ∪ {v})
  let T := G.secondOutNeighborFinset v
  have hECard : 7 ≤ E.card := by
    simpa [U, S, E] using
      oneArcDeletionExpansion G hBound hG hNoSeymour hDegree hu
  have hTCard : T.card ≤ 7 := by
    have hNotSeymour : ¬G.IsSeymourVertex v := by
      intro hv
      exact hNoSeymour ⟨v, hv⟩
    unfold IsSeymourVertex secondOutdegree at hNotSeymour
    change ¬G.outdegree v ≤ T.card at hNotSeymour
    omega
  have hEraseSubset : E.erase u ⊆ T := by
    intro w hw
    have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
    have hwE : w ∈ E := Finset.mem_of_mem_erase hw
    rcases Finset.mem_sdiff.mp hwE with ⟨hwReach, hwOutside⟩
    obtain ⟨middle, hmS, hmw⟩ :=
      (mem_outNeighborFinsetOf (G := G)).mp hwReach
    have hvm : G.Adj v middle := by
      apply (mem_outNeighborFinset (G := G)).mp
      exact Finset.mem_of_mem_erase hmS
    have hwNotS : w ∉ S := by
      intro hwS
      exact hwOutside (Finset.mem_union_left _ hwS)
    have hwNeV : w ≠ v := by
      intro hwv
      subst w
      exact hwOutside (Finset.mem_union_right _ (Finset.mem_singleton_self v))
    have hvw : ¬G.Adj v w := by
      intro hvw
      have hwU : w ∈ U := (mem_outNeighborFinset (G := G)).mpr hvw
      exact hwNotS (Finset.mem_erase.mpr ⟨hwu, hwU⟩)
    rw [mem_secondOutNeighborFinset, mem_secondOutNeighborSet]
    exact ⟨⟨middle, hvm, hmw⟩, hvw, hwNeV⟩
  have hEraseCard : 6 ≤ (E.erase u).card := by
    by_cases huE : u ∈ E
    · have hCardEq := Finset.card_erase_add_one huE
      omega
    · rw [Finset.erase_eq_of_notMem huE]
      omega
  have hDiffSubset : T \ E ⊆ T \ E.erase u := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hwT, hwNotE⟩
    apply Finset.mem_sdiff.mpr
    exact ⟨hwT, fun hwErase ↦ hwNotE (Finset.mem_of_mem_erase hwErase)⟩
  have hDiffCard := Finset.card_le_card hDiffSubset
  have hLargeDiffCard : (T \ E.erase u).card = T.card - (E.erase u).card := by
    exact Finset.card_sdiff_of_subset hEraseSubset
  change (T \ E).card ≤ 1
  rw [hLargeDiffCard] at hDiffCard
  omega

/--
Subset form of `oneArcDeletion_misses_at_most_one`: all but at most one member
of any chosen family of original strict second neighbors remains reachable
after the deletion.
-/
theorem oneArcDeletion_reaches_all_but_one {v u : V} (K : Finset V)
    (hBound : LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree v = 8) (hu : G.Adj v u)
    (hK : K ⊆ G.secondOutNeighborFinset v) :
    K.card ≤
      (K ∩ (G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase u) \
        ((G.outNeighborFinset v |>.erase u) ∪ {v}))).card + 1 := by
  let E := G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase u) \
    ((G.outNeighborFinset v |>.erase u) ∪ {v})
  let T := G.secondOutNeighborFinset v
  have hMiss : (T \ E).card ≤ 1 := by
    simpa [E, T] using oneArcDeletion_misses_at_most_one G hBound hG
      hNoSeymour hDegree hu
  have hSubset : K \ E ⊆ T \ E := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hwK, hwNotE⟩
    exact Finset.mem_sdiff.mpr ⟨hK hwK, hwNotE⟩
  have hKMiss : (K \ E).card ≤ 1 :=
    (Finset.card_le_card hSubset).trans hMiss
  have hSplit := Finset.card_sdiff_add_card_inter K E
  change K.card ≤ (K ∩ E).card + 1
  omega

end Finite

end Digraph
