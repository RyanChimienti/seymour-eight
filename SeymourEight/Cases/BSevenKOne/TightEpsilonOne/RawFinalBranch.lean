import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.FinalBranch
import SeymourEight.Shared.ArcCounting
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option linter.style.header false

/-!
# Raw edge counts for the final branch

This file converts the numerical `m`, `alpha`, and `beta` equalities into the
structural final-branch package.
-/

namespace SeymourEight.RawFinalBranch

open CertificateBridge FinalBranch Shared TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- With seven vertices and all 21 possible oriented pairs present, `S` is a tournament. -/
theorem tournament_of_edgeCount_eq_twentyOne (S : Finset V)
    (hCard : S.card = 7) (hG : G.IsOriented)
    (hEdges : edgeCount G S S = 21) :
    ∀ {u : V}, u ∈ S → ∀ {v : V}, v ∈ S → u ≠ v →
      G.Adj u v ∨ G.Adj v u := by
  classical
  have hIncidentLe : ∀ v ∈ S,
      directCount G S v + internalInDegree G S v ≤ 6 := by
    intro v hv
    have hDisjoint := disjoint_internal_out_in G S v hG
    have hSubset := internal_incident_subset_erase G S v hG
    calc
      directCount G S v + internalInDegree G S v =
          (internalFirstNeighbors G S v ∪
            (S.filter fun u ↦ G.Adj u v)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
        rfl
      _ ≤ (S.erase v).card := Finset.card_le_card hSubset
      _ = 6 := by rw [Finset.card_erase_of_mem hv, hCard]
  have hIncidentSum :
      ∑ v ∈ S, (directCount G S v + internalInDegree G S v) = 42 := by
    rw [Finset.sum_add_distrib, ← edgeCount,
      ← edgeCount_eq_sum_internalInDegree (G := G), hEdges]
  have hIncidentEq : ∀ v ∈ S,
      directCount G S v + internalInDegree G S v = 6 := by
    intro v hv
    apply Nat.le_antisymm (hIncidentLe v hv)
    by_contra hNot
    have hStrict : directCount G S v + internalInDegree G S v < 6 :=
      by omega
    have hSumStrict :
        (∑ w ∈ S, (directCount G S w + internalInDegree G S w)) <
          ∑ _w ∈ S, 6 := by
      apply Finset.sum_lt_sum
      · intro w hw
        exact hIncidentLe w hw
      · exact ⟨v, hv, hStrict⟩
    simp [hIncidentSum, hCard] at hSumStrict
  intro u hu v hv huv
  have hDisjoint := disjoint_internal_out_in G S u hG
  have hSubset := internal_incident_subset_erase G S u hG
  have hUnionCard :
      (internalFirstNeighbors G S u ∪ (S.filter fun w ↦ G.Adj w u)).card = 6 := by
    rw [Finset.card_union_of_disjoint hDisjoint]
    exact hIncidentEq u hu
  have hEraseCard : (S.erase u).card = 6 := by
    rw [Finset.card_erase_of_mem hu, hCard]
  have hUnionEq :
      internalFirstNeighbors G S u ∪ (S.filter fun w ↦ G.Adj w u) = S.erase u := by
    apply Finset.eq_of_subset_of_card_le hSubset
    rw [hUnionCard, hEraseCard]
  have hvErase : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hvUnion := hUnionEq.symm.subset hvErase
  rcases Finset.mem_union.mp hvUnion with huvOut | hvuIn
  · exact Or.inl (Finset.mem_filter.mp huvOut).2
  · exact Or.inr (Finset.mem_filter.mp hvuIn).2

omit [DecidableEq V] in
/-- A seven-element family with minimum degree eight and total degree 56 is pointwise tight. -/
theorem outdegree_eq_eight_of_sum_eq_fiftySix (S : Finset V)
    (hCard : S.card = 7) (hMin : ∀ v ∈ S, 8 ≤ G.outdegree v)
    (hSum : ∑ v ∈ S, G.outdegree v = 56) :
    ∀ v ∈ S, G.outdegree v = 8 := by
  intro v hv
  apply Nat.le_antisymm
  · by_contra hNot
    have hStrict : 8 < G.outdegree v := by omega
    have hSumStrict : (∑ _w ∈ S, 8) < ∑ w ∈ S, G.outdegree w := by
      apply Finset.sum_lt_sum
      · intro w hw
        exact hMin w hw
      · exact ⟨v, hv, hStrict⟩
    simp [hCard, hSum] at hSumStrict
  · exact hMin v hv

omit [DecidableEq V] in
/-- Zero total excess above eight gives total degree `7·8=56`. -/
theorem degreeSum_eq_fiftySix_of_excessSum_eq_zero (S : Finset V)
    (hCard : S.card = 7) (hMin : ∀ v ∈ S, 8 ≤ G.outdegree v)
    (hExcess : ∑ v ∈ S, (G.outdegree v - 8) = 0) :
    ∑ v ∈ S, G.outdegree v = 56 := by
  have hPointwise : ∀ v ∈ S,
      G.outdegree v = 8 + (G.outdegree v - 8) := by
    intro v hv
    have hvMin := hMin v hv
    omega
  calc
    (∑ v ∈ S, G.outdegree v) =
        ∑ v ∈ S, (8 + (G.outdegree v - 8)) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hPointwise v hv
    _ = 56 := by
      rw [Finset.sum_add_distrib, hExcess]
      simp [hCard]

/--
Raw numerical form of the final `(m, alpha, beta) = (1, 2, 0)` row.
The values `6`, `15`, `21`, and `56` are respectively
`e(P,{s})`, `e(P,H)`, `e(P,P)`, and the total `P`-outdegree.
-/
structure AlphaBetaTwoZeroCounts (C : G.LocalConfiguration) : Prop where
  oriented : G.IsOriented
  minOutDegreeEight : ∀ v, 8 ≤ G.outdegree v
  noSeymour : ∀ v, ¬G.IsSeymourVertex v
  pCard : C.P.card = 7
  zCard : C.Z.card = 2
  pToZCount : edgeCount G C.P C.Z = 14
  rootArcCount : ∑ p ∈ C.P, epsilonAt G p C.s = 6
  pToHCount : edgeCount G C.P C.H = 15
  pInternalCount : edgeCount G C.P C.P = 21
  pDegreeExcess : ∑ p ∈ C.P, (G.outdegree p - 8) = 0

namespace AlphaBetaTwoZeroCounts

variable {C : G.LocalConfiguration} (R : AlphaBetaTwoZeroCounts G C)

include R in
/-- At `(m, alpha, beta) = (1, 2, 0)`, the degree-excess identity forces total
degree 56. -/
theorem pDegreeSum : ∑ p ∈ C.P, G.outdegree p = 56 :=
  degreeSum_eq_fiftySix_of_excessSum_eq_zero G C.P R.pCard
    (fun p _hp ↦ R.minOutDegreeEight p) R.pDegreeExcess

include R in
/-- The maximal count `e(P,Z)=14` forces every one of the `7·2` possible arcs. -/
theorem pToZ : ∀ p ∈ C.P, ∀ z ∈ C.Z, G.Adj p z := by
  have hDirectLe : ∀ p ∈ C.P, directCount G C.Z p ≤ 2 := by
    intro p _hp
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq R.zCard
  have hDirectEq : ∀ p ∈ C.P, directCount G C.Z p = 2 := by
    intro p hp
    apply Nat.le_antisymm (hDirectLe p hp)
    by_contra hNot
    have hStrict : directCount G C.Z p < 2 := by omega
    have hSumStrict :
        (∑ q ∈ C.P, directCount G C.Z q) < ∑ _q ∈ C.P, 2 := by
      apply Finset.sum_lt_sum hDirectLe
      exact ⟨p, hp, hStrict⟩
    have hLeft : ∑ q ∈ C.P, directCount G C.Z q = 14 := by
      exact R.pToZCount
    simp [hLeft, R.pCard] at hSumStrict
  intro p hp z hz
  have hFilterEq : internalFirstNeighbors G C.Z p = C.Z := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    have hZCard := R.zCard
    have hFilterCard := hDirectEq p hp
    unfold directCount internalFirstNeighbors at hFilterCard
    omega
  have hzFilter : z ∈ internalFirstNeighbors G C.Z p := by
    rw [hFilterEq]
    exact hz
  exact (Finset.mem_filter.mp hzFilter).2

/-- The four locally accounted portions of a `P`-vertex's outneighborhood. -/
def countedOutneighbors (C : G.LocalConfiguration) (p : V) : Finset V :=
  C.Z ∪ rootArcFinset G C p ∪ internalFirstNeighbors G C.H p ∪
    internalFirstNeighbors G C.P p

include R in
theorem countedOutneighbors_subset_outNeighborFinset (p : V) (hp : p ∈ C.P) :
    countedOutneighbors G C p ⊆ G.outNeighborFinset p := by
  intro v hv
  apply (Digraph.mem_outNeighborFinset (G := G)).mpr
  simp only [countedOutneighbors, Finset.mem_union] at hv
  rcases hv with ((hvZ | hvRoot) | hvH) | hvP
  · exact pToZ (G := G) R p hp v hvZ
  · by_cases hps : G.Adj p C.s
    · have hvEq : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
      subst v
      exact hps
    · simp [rootArcFinset, hps] at hvRoot
  · exact (Finset.mem_filter.mp hvH).2
  · exact (Finset.mem_filter.mp hvP).2

include R in
theorem card_countedOutneighbors (p : V) :
    (countedOutneighbors G C p).card =
      2 + epsilonAt G p C.s + directCount G C.H p + directCount G C.P p := by
  have hZRoot : Disjoint C.Z (rootArcFinset G C p) := by
    rw [Finset.disjoint_left]
    intro v hvZ hvRoot
    by_cases hps : G.Adj p C.s
    · have hvEq : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
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
      · have hvEq : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
        subst v
        exact Digraph.LocalConfiguration.s_notMem_H (G := G) C R.oriented.1
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
        · have hvEq : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
          subst v
          exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP'
        · simp [rootArcFinset, hps] at hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 hvP'
  unfold countedOutneighbors directCount
  rw [Finset.card_union_of_disjoint hAllP,
    Finset.card_union_of_disjoint hZRootH,
    Finset.card_union_of_disjoint hZRoot,
    R.zCard, card_rootArcFinset]

include R in
theorem sum_card_countedOutneighbors :
    ∑ p ∈ C.P, (countedOutneighbors G C p).card = 56 := by
  simp_rw [card_countedOutneighbors (G := G) R]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [R.pCard, R.rootArcCount, ← edgeCount, R.pToHCount,
    ← edgeCount, R.pInternalCount]
  omega

include R in
theorem outNeighborFinset_eq_countedOutneighbors (p : V) (hp : p ∈ C.P) :
    G.outNeighborFinset p = countedOutneighbors G C p := by
  have hSubset :=
    countedOutneighbors_subset_outNeighborFinset (G := G) R p hp
  symm
  apply Finset.eq_of_subset_of_card_le hSubset
  have hCardLe : ∀ q ∈ C.P,
      (countedOutneighbors G C q).card ≤ (G.outNeighborFinset q).card := by
    intro q hq
    exact Finset.card_le_card <|
      countedOutneighbors_subset_outNeighborFinset (G := G) R q hq
  by_contra hNot
  have hStrict : (countedOutneighbors G C p).card < (G.outNeighborFinset p).card :=
    by omega
  have hSumStrict :
      (∑ q ∈ C.P, (countedOutneighbors G C q).card) <
        ∑ q ∈ C.P, (G.outNeighborFinset q).card := by
    apply Finset.sum_lt_sum hCardLe
    exact ⟨p, hp, hStrict⟩
  have hOutSum : ∑ q ∈ C.P, (G.outNeighborFinset q).card = 56 := by
    simpa [Digraph.outdegree] using pDegreeSum (G := G) R
  rw [sum_card_countedOutneighbors (G := G) R, hOutSum] at hSumStrict
  omega

include R in
theorem outgoingCaptured (p : V) (hp : p ∈ C.P) :
    G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
  rw [outNeighborFinset_eq_countedOutneighbors (G := G) R p hp]
  intro v hv
  simp only [countedOutneighbors, Finset.mem_union] at hv ⊢
  rcases hv with ((hvZ | hvRoot) | hvH) | hvP
  · exact Or.inl (Or.inl (Or.inl hvZ))
  · by_cases hps : G.Adj p C.s
    · have hvEq : v = C.s := by simpa [rootArcFinset, hps] using hvRoot
      exact Or.inl (Or.inl (Or.inr (by simp [hvEq])))
    · simp [rootArcFinset, hps] at hvRoot
  · exact Or.inl (Or.inr (Finset.mem_filter.mp hvH).1)
  · exact Or.inr (Finset.mem_filter.mp hvP).1

include R in
theorem pTournament :
    ∀ {u : V}, u ∈ C.P → ∀ {v : V}, v ∈ C.P → u ≠ v →
      G.Adj u v ∨ G.Adj v u :=
  tournament_of_edgeCount_eq_twentyOne G C.P R.pCard R.oriented R.pInternalCount

include R in
theorem pOutDegreeEight : ∀ p ∈ C.P, G.outdegree p = 8 :=
  outdegree_eq_eight_of_sum_eq_fiftySix G C.P R.pCard
    (fun p _hp ↦ R.minOutDegreeEight p) (pDegreeSum (G := G) R)

include R in
/-- The raw numerical row constructs the structural branch package. -/
theorem toFinalBranch : AlphaBetaTwoZeroBranch G C where
  oriented := R.oriented
  minOutDegreeEight := R.minOutDegreeEight
  noSeymour := R.noSeymour
  pCard := R.pCard
  zCard := R.zCard
  pToZ := pToZ (G := G) R
  pTournament := R.pTournament
  pOutDegreeEight := R.pOutDegreeEight
  outgoingCaptured := outgoingCaptured (G := G) R

include R in
/-- The raw `(m, alpha, beta) = (1, 2, 0)` row is impossible. -/
theorem impossible : False :=
  AlphaBetaTwoZeroBranch.impossible (G := G) (toFinalBranch (G := G) R)

end AlphaBetaTwoZeroCounts

end SeymourEight.RawFinalBranch
