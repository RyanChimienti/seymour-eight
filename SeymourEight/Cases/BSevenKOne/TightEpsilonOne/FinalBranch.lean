import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.TerminalAlphaBeta

set_option linter.style.header false

/-!
# Integration of the final `(alpha, beta) = (2, 0)` branch

This file packages the graph-theoretic assumptions of the final branch in the
typed local vocabulary and derives the common-`Z` interface required by the
terminal theorem.
-/

namespace SeymourEight.FinalBranch

open CertificateBridge Shared TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In an oriented graph, a two-element set has a vertex with no arc into the set. -/
theorem exists_sink_in_pair (Z : Finset V) (hZCard : Z.card = 2)
    (hG : G.IsOriented) :
    ∃ z0 ∈ Z, ∀ z ∈ Z, ¬G.Adj z0 z := by
  classical
  obtain ⟨z0, z1, hz01, hZ⟩ := Finset.card_eq_two.mp hZCard
  rw [hZ]
  by_cases hArc : G.Adj z0 z1
  · refine ⟨z1, by simp, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · simpa [hz] using hG.2 hArc
    · simpa [hz] using hG.1 z1
  · refine ⟨z0, by simp, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · simpa [hz] using hG.1 z0
    · simpa [hz] using hArc

/-- The possible root arc from `p`, represented as a zero- or one-element finset. -/
def rootArcFinset (C : G.LocalConfiguration) (p : V) : Finset V :=
  if G.Adj p C.s then {C.s} else ∅

omit [DecidableEq V] in
@[simp]
theorem card_rootArcFinset (C : G.LocalConfiguration) (p : V) :
    (rootArcFinset G C p).card = epsilonAt G p C.s := by
  by_cases h : G.Adj p C.s <;> simp [rootArcFinset, epsilonAt, h]

/--
The structural data retained in the final `z=2`, `beta=0` branch.  The last
field says that every outgoing arc of a `P`-vertex lands in one of the four
accounted local classes.
-/
structure AlphaBetaTwoZeroBranch (C : G.LocalConfiguration) : Prop where
  oriented : G.IsOriented
  minOutDegreeEight : ∀ v, 8 ≤ G.outdegree v
  noSeymour : ∀ v, ¬G.IsSeymourVertex v
  pCard : C.P.card = 7
  zCard : C.Z.card = 2
  pToZ : ∀ p ∈ C.P, ∀ z ∈ C.Z, G.Adj p z
  pTournament : ∀ {u : V}, u ∈ C.P → ∀ {v : V}, v ∈ C.P → u ≠ v →
    G.Adj u v ∨ G.Adj v u
  pOutDegreeEight : ∀ p ∈ C.P, G.outdegree p = 8
  outgoingCaptured : ∀ p ∈ C.P,
    G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P

namespace AlphaBetaTwoZeroBranch

variable {C : G.LocalConfiguration} (F : AlphaBetaTwoZeroBranch G C)

/-- The four disjoint classes which account for every outgoing arc of `p`. -/
def accountedOutneighbors (_F : AlphaBetaTwoZeroBranch G C) (p : V) : Finset V :=
  C.Z ∪ rootArcFinset G C p ∪ internalFirstNeighbors G C.H p ∪
    internalFirstNeighbors G C.P p

theorem outNeighborFinset_eq_accounted (p : V) (hp : p ∈ C.P) :
    G.outNeighborFinset p = accountedOutneighbors (G := G) F p := by
  ext v
  constructor
  · intro hvOut
    have hvCaptured := F.outgoingCaptured p hp hvOut
    simp only [accountedOutneighbors, Finset.mem_union, Finset.mem_singleton]
      at hvCaptured ⊢
    rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
    · exact Or.inl (Or.inl (Or.inl hvZ))
    · subst v
      have hps : G.Adj p C.s :=
        (Digraph.mem_outNeighborFinset (G := G)).mp hvOut
      exact Or.inl (Or.inl (Or.inr (by simp [rootArcFinset, hps])))
    · exact Or.inl (Or.inr
        (Finset.mem_filter.mpr
          ⟨hvH, (Digraph.mem_outNeighborFinset (G := G)).mp hvOut⟩))
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨hvP, (Digraph.mem_outNeighborFinset (G := G)).mp hvOut⟩)
  · intro hv
    simp only [accountedOutneighbors, Finset.mem_union] at hv
    apply (Digraph.mem_outNeighborFinset (G := G)).mpr
    rcases hv with ((hvZ | hvRoot) | hvH) | hvP
    · exact F.pToZ p hp v hvZ
    · by_cases hps : G.Adj p C.s
      · have hvEq : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
        subst v
        exact hps
      · simp [rootArcFinset, hps] at hvRoot
    · exact (Finset.mem_filter.mp hvH).2
    · exact (Finset.mem_filter.mp hvP).2

include F in
theorem outdegree_eq_accounted_counts (p : V) (hp : p ∈ C.P) :
    G.outdegree p =
      2 + epsilonAt G p C.s + directCount G C.H p + directCount G C.P p := by
  have hZRoot : Disjoint C.Z (rootArcFinset G C p) := by
    rw [Finset.disjoint_left]
    intro v hvZ hvRoot
    by_cases hps : G.Adj p C.s
    · have : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hvZ
    · simp [rootArcFinset, hps] at hvRoot
  have hZRootH : Disjoint
      (C.Z ∪ rootArcFinset G C p) (internalFirstNeighbors G C.H p) := by
    rw [Finset.disjoint_left]
    intro v hvZR hvH
    rcases Finset.mem_union.mp hvZR with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
        (Finset.mem_filter.mp hvH).1
    · by_cases hps : G.Adj p C.s
      · have : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_H (G := G) C F.oriented.1
          (Finset.mem_filter.mp hvH).1
      · simp [rootArcFinset, hps] at hvRoot
  have hAllP : Disjoint
      (C.Z ∪ rootArcFinset G C p ∪ internalFirstNeighbors G C.H p)
      (internalFirstNeighbors G C.P p) := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvP
    have hvP' := (Finset.mem_filter.mp hvP).1
    rcases Finset.mem_union.mp hvLeft with hvZR | hvH
    · rcases Finset.mem_union.mp hvZR with hvZ | hvRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP'
      · by_cases hps : G.Adj p C.s
        · have : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP'
        · simp [rootArcFinset, hps] at hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 hvP'
  unfold Digraph.outdegree directCount
  rw [outNeighborFinset_eq_accounted (G := G) F p hp, accountedOutneighbors,
    Finset.card_union_of_disjoint hAllP,
    Finset.card_union_of_disjoint hZRootH,
    Finset.card_union_of_disjoint hZRoot,
    F.zCard, card_rootArcFinset]

include F in
/-- Direct `W`-neighbors of `p` can only lie in `H` or be the root `s`. -/
theorem direct_W_bound (W : Finset V) (hWZ : Disjoint W C.Z)
    (hWP : Disjoint W C.P) (p : V) (hp : p ∈ C.P) :
    (W.filter (G.Adj p)).card ≤ directCount G C.H p + epsilonAt G p C.s := by
  have hSubset : W.filter (G.Adj p) ⊆
      internalFirstNeighbors G C.H p ∪ rootArcFinset G C p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvW, hpv⟩
    have hvOut : v ∈ G.outNeighborFinset p :=
      (Digraph.mem_outNeighborFinset (G := G)).mpr hpv
    have hvCaptured := F.outgoingCaptured p hp hvOut
    simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
    rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
    · exact ((Finset.disjoint_left.mp hWZ) hvW hvZ).elim
    · subst v
      exact Finset.mem_union_right _ (by simp [rootArcFinset, hpv])
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvH, hpv⟩)
    · exact ((Finset.disjoint_left.mp hWP) hvW hvP).elim
  calc
    (W.filter (G.Adj p)).card ≤
        (internalFirstNeighbors G C.H p ∪ rootArcFinset G C p).card :=
      Finset.card_le_card hSubset
    _ ≤ (internalFirstNeighbors G C.H p).card +
        (rootArcFinset G C p).card := Finset.card_union_le _ _
    _ = directCount G C.H p + epsilonAt G p C.s := by
      rw [card_rootArcFinset]
      rfl

include F in
/-- The fully packaged final branch is contradictory. -/
theorem impossible : False := by
  obtain ⟨z0, hz0Z, hz0Sink⟩ := exists_sink_in_pair G C.Z F.zCard F.oriented
  let W := G.outNeighborFinset z0
  have hz0W : ∀ w ∈ W, G.Adj z0 w := by
    intro w hw
    exact (Digraph.mem_outNeighborFinset (G := G)).mp hw
  have hWZ : Disjoint W C.Z := by
    rw [Finset.disjoint_left]
    intro w hwW hwZ
    exact hz0Sink w hwZ (hz0W w hwW)
  have hWP : Disjoint W C.P := by
    rw [Finset.disjoint_left]
    intro p hpW hpP
    exact F.oriented.2 (F.pToZ p hpP z0 hz0Z) (hz0W p hpW)
  have hWCard : 8 ≤ W.card := by
    change 8 ≤ G.outdegree z0
    exact F.minOutDegreeEight z0
  apply alphaBetaTwoZero_impossible_of_commonZ G C.P C.H W C.s z0
    F.pCard F.oriented F.pTournament
  · intro p hp
    exact F.pToZ p hp z0 hz0Z
  · exact hz0W
  · exact hWP
  · exact hWCard
  · intro p hp
    exact direct_W_bound (G := G) F W hWZ hWP p hp
  · intro p _hp
    exact F.noSeymour p
  · exact F.pOutDegreeEight
  · intro p hp
    exact outdegree_eq_accounted_counts (G := G) F p hp

end AlphaBetaTwoZeroBranch

end SeymourEight.FinalBranch
