import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Global
import SeymourEight.Reduction

set_option linter.style.header false

/-!
# The exact-seven external-union branch for three `Z` vertices

When every `P → Z` arc is present and the external union of the three
`Z`-outneighborhoods has size seven, degree counting forces the induced
graph on `Z` to be a directed triangle and every vertex of `Z` to dominate
the whole external union.  Deleting one triangle arc then invokes the known
degree-seven case and produces eight strict second neighbors.
-/

namespace SeymourEight.ThreeZExactSeven

open CertificateBridge FiveZExactGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem all_P_to_Z_of_edgeCount_twentyOne (P Z : Finset V)
    (hPCard : P.card = 7) (hZCard : Z.card = 3)
    (hEdges : edgeCount G P Z = 21) :
    ∀ p ∈ P, ∀ z ∈ Z, G.Adj p z := by
  classical
  have hDirectLe : ∀ p ∈ P, directCount G Z p ≤ 3 := by
    intro p _hp
    exact (Finset.card_le_card
      (Finset.filter_subset (p := G.Adj p) Z)).trans_eq hZCard
  have hDirectEq : ∀ p ∈ P, directCount G Z p = 3 := by
    intro p hp
    apply Nat.le_antisymm (hDirectLe p hp)
    by_contra hNot
    have hStrict : directCount G Z p < 3 := by omega
    have hSumStrict : (∑ q ∈ P, directCount G Z q) < ∑ _q ∈ P, 3 := by
      apply Finset.sum_lt_sum hDirectLe
      exact ⟨p, hp, hStrict⟩
    unfold edgeCount at hEdges
    simp [hEdges, hPCard] at hSumStrict
  intro p hp z hz
  have hFilterEq : internalFirstNeighbors G Z p = Z := by
    apply Finset.eq_of_subset_of_card_le
      (Finset.filter_subset (p := G.Adj p) Z)
    have hEq := hDirectEq p hp
    unfold directCount internalFirstNeighbors at hEq
    omega
  have hzFilter : z ∈ internalFirstNeighbors G Z p := by
    rw [hFilterEq]
    exact hz
  exact (Finset.mem_filter.mp hzFilter).2

/-- Full `P → Z` capacity forces at least seven external `Z`-targets. -/
theorem seven_le_zExternalUnion_card (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 3)
    (hPZ : edgeCount G C.P C.Z = 21) :
    7 ≤ (zExternalUnion G C).card := by
  have hInternal := internal_edgeCount_le_choose_two G C.Z hG
  have hCross := cross_edgeCount_add_reverse_le G C.P C.Z hG
  have hExternal := edgeCount_le_card_mul_card
    G C.Z (zExternalUnion G C)
  have hReverse : edgeCount G C.Z C.P = 0 := by
    rw [hPCard, hZCard, hPZ] at hCross
    omega
  have hInternal' : edgeCount G C.Z C.Z ≤ 3 := by
    rw [hZCard] at hInternal
    simpa [Nat.choose] using hInternal
  have hDegreeSum :
      ∑ z ∈ C.Z, G.outdegree z =
        edgeCount G C.Z C.Z +
          edgeCount G C.Z (zExternalUnion G C) + edgeCount G C.Z C.P := by
    calc
      (∑ z ∈ C.Z, G.outdegree z) =
          ∑ z ∈ C.Z, (directCount G C.Z z +
            directCount G (zExternalUnion G C) z + directCount G C.P z) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact z_outdegree_eq_retainedCounts G C z hz
      _ = edgeCount G C.Z C.Z +
          edgeCount G C.Z (zExternalUnion G C) + edgeCount G C.Z C.P := by
        unfold edgeCount
        simp only [Finset.sum_add_distrib]
  have hDegreeLower : 24 ≤ ∑ z ∈ C.Z, G.outdegree z := by
    calc
      24 = ∑ _z ∈ C.Z, 8 := by simp [hZCard]
      _ ≤ ∑ z ∈ C.Z, G.outdegree z := by
        apply Finset.sum_le_sum
        intro z hz
        exact hMin z
  by_contra hNot
  have hWLe : (zExternalUnion G C).card ≤ 6 := by omega
  have hExternal' : edgeCount G C.Z (zExternalUnion G C) ≤ 18 := by
    calc
      _ ≤ C.Z.card * (zExternalUnion G C).card := hExternal
      _ ≤ 18 := by rw [hZCard]; omega
  omega

omit [Fintype V] [DecidableEq V] in
/-- Saturating all three possible pairs makes a three-vertex oriented graph
complete. -/
theorem tournament_of_three_edges (Z : Finset V) (hZCard : Z.card = 3)
    (hG : G.IsOriented) (hEdges : edgeCount G Z Z = 3) :
    ∀ {u : V}, u ∈ Z → ∀ {v : V}, v ∈ Z → u ≠ v →
      G.Adj u v ∨ G.Adj v u := by
  classical
  have hIncidentLe : ∀ v ∈ Z,
      directCount G Z v + internalInDegree G Z v ≤ 2 := by
    intro v hv
    have hDisjoint := disjoint_internal_out_in G Z v hG
    have hSubset := internal_incident_subset_erase G Z v hG
    calc
      directCount G Z v + internalInDegree G Z v =
          (internalFirstNeighbors G Z v ∪
            (Z.filter fun u ↦ G.Adj u v)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
        rfl
      _ ≤ (Z.erase v).card := Finset.card_le_card hSubset
      _ = 2 := by rw [Finset.card_erase_of_mem hv, hZCard]
  have hIncidentSum :
      ∑ v ∈ Z, (directCount G Z v + internalInDegree G Z v) = 6 := by
    rw [Finset.sum_add_distrib, ← edgeCount,
      ← edgeCount_eq_sum_internalInDegree (G := G), hEdges]
  have hIncidentEq : ∀ v ∈ Z,
      directCount G Z v + internalInDegree G Z v = 2 := by
    intro v hv
    apply Nat.le_antisymm (hIncidentLe v hv)
    by_contra hNot
    have hStrict : directCount G Z v + internalInDegree G Z v < 2 := by omega
    have hSumStrict :
        (∑ w ∈ Z, (directCount G Z w + internalInDegree G Z w)) <
          ∑ _w ∈ Z, 2 := by
      apply Finset.sum_lt_sum
      · intro w hw
        exact hIncidentLe w hw
      · exact ⟨v, hv, hStrict⟩
    simp [hIncidentSum, hZCard] at hSumStrict
  intro u hu v hv huv
  have hDisjoint := disjoint_internal_out_in G Z u hG
  have hSubset := internal_incident_subset_erase G Z u hG
  have hUnionCard :
      (internalFirstNeighbors G Z u ∪ (Z.filter fun w ↦ G.Adj w u)).card = 2 := by
    rw [Finset.card_union_of_disjoint hDisjoint]
    exact hIncidentEq u hu
  have hEraseCard : (Z.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem hu, hZCard]
  have hUnionEq :
      internalFirstNeighbors G Z u ∪ (Z.filter fun w ↦ G.Adj w u) = Z.erase u := by
    apply Finset.eq_of_subset_of_card_le hSubset
    rw [hUnionCard, hEraseCard]
  have hvErase : v ∈ Z.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hvUnion := hUnionEq.symm.subset hvErase
  rcases Finset.mem_union.mp hvUnion with huvOut | hvuIn
  · exact Or.inl (Finset.mem_filter.mp huvOut).2
  · exact Or.inr (Finset.mem_filter.mp hvuIn).2

omit [Fintype V] [DecidableEq V] in
theorem eq_of_adj_of_adj_of_directCount_eq_one (Z : Finset V)
    {u v w : V} (hv : v ∈ Z) (hw : w ∈ Z)
    (huv : G.Adj u v) (huw : G.Adj u w)
    (hCount : directCount G Z u = 1) : v = w := by
  classical
  by_contra hvw
  have hPair : ({v, w} : Finset V) ⊆ internalFirstNeighbors G Z u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hv, huv⟩
    · exact Finset.mem_filter.mpr ⟨hw, huw⟩
  have hCard := Finset.card_le_card hPair
  change (internalFirstNeighbors G Z u).card = 1 at hCount
  rw [hCount] at hCard
  have hPairCard : ({v, w} : Finset V).card = 2 := by simp [hvw]
  omega

/-- The exact-seven branch is impossible by a single arc deletion from the
forced directed triangle on `Z`. -/
theorem impossible (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 3)
    (hPZ : edgeCount G C.P C.Z = 21)
    (hWCard : (zExternalUnion G C).card = 7) : False := by
  classical
  let W := zExternalUnion G C
  have hFullPZ := all_P_to_Z_of_edgeCount_twentyOne G C.P C.Z
    hPCard hZCard hPZ
  have hCross := cross_edgeCount_add_reverse_le G C.P C.Z hG
  have hReverse : edgeCount G C.Z C.P = 0 := by
    rw [hPCard, hZCard, hPZ] at hCross
    omega
  have hInternalLe := internal_edgeCount_le_choose_two G C.Z hG
  have hInternalLe' : edgeCount G C.Z C.Z ≤ 3 := by
    rw [hZCard] at hInternalLe
    simpa [Nat.choose] using hInternalLe
  have hExternalLe := edgeCount_le_card_mul_card G C.Z W
  have hExternalLe' : edgeCount G C.Z W ≤ 21 := by
    simpa [W, hZCard, hWCard] using hExternalLe
  have hDegreeSum :
      ∑ z ∈ C.Z, G.outdegree z =
        edgeCount G C.Z C.Z + edgeCount G C.Z W + edgeCount G C.Z C.P := by
    calc
      (∑ z ∈ C.Z, G.outdegree z) =
          ∑ z ∈ C.Z, (directCount G C.Z z + directCount G W z +
            directCount G C.P z) := by
        apply Finset.sum_congr rfl
        intro z hz
        simpa [W] using z_outdegree_eq_retainedCounts G C z hz
      _ = edgeCount G C.Z C.Z + edgeCount G C.Z W + edgeCount G C.Z C.P := by
        unfold edgeCount
        simp only [Finset.sum_add_distrib]
  have hDegreeLower : 24 ≤ ∑ z ∈ C.Z, G.outdegree z := by
    calc
      24 = ∑ _z ∈ C.Z, 8 := by simp [hZCard]
      _ ≤ ∑ z ∈ C.Z, G.outdegree z := by
        apply Finset.sum_le_sum
        intro z hz
        exact hMin z
  have hDegreeSumEq : ∑ z ∈ C.Z, G.outdegree z = 24 := by omega
  have hInternal : edgeCount G C.Z C.Z = 3 := by omega
  have hExternal : edgeCount G C.Z W = 21 := by omega
  have hDegreeEight : ∀ z ∈ C.Z, G.outdegree z = 8 := by
    intro z hz
    apply Nat.le_antisymm
    · by_contra hNot
      have hStrict : 8 < G.outdegree z := by omega
      have hSumStrict : (∑ _w ∈ C.Z, 8) < ∑ w ∈ C.Z, G.outdegree w := by
        apply Finset.sum_lt_sum
        · intro w hw
          exact hMin w
        · exact ⟨z, hz, hStrict⟩
      simp [hZCard, hDegreeSumEq] at hSumStrict
    · exact hMin z
  have hWCount : ∀ z ∈ C.Z, directCount G W z = 7 := by
    intro z hz
    have hLe : ∀ w ∈ C.Z, directCount G W w ≤ 7 := by
      intro w _hw
      exact (Finset.card_le_card
        (Finset.filter_subset (p := G.Adj w) W)).trans_eq (by simpa [W] using hWCard)
    apply Nat.le_antisymm (hLe z hz)
    by_contra hNot
    have hStrict : directCount G W z < 7 := by omega
    have hSumStrict : (∑ w ∈ C.Z, directCount G W w) < ∑ _w ∈ C.Z, 7 := by
      apply Finset.sum_lt_sum hLe
      exact ⟨z, hz, hStrict⟩
    unfold edgeCount at hExternal
    simp [hExternal, hZCard] at hSumStrict
  have hAllZW : ∀ z ∈ C.Z, ∀ w ∈ W, G.Adj z w := by
    intro z hz w hw
    have hFilterEq : internalFirstNeighbors G W z = W := by
      apply Finset.eq_of_subset_of_card_le
        (Finset.filter_subset (p := G.Adj z) W)
      have hEq := hWCount z hz
      unfold directCount internalFirstNeighbors at hEq
      change W.card ≤ (W.filter (G.Adj z)).card
      rw [hEq]
      simpa [W] using hWCard.le
    have : w ∈ internalFirstNeighbors G W z := by rw [hFilterEq]; exact hw
    exact (Finset.mem_filter.mp this).2
  have hPCountZero : ∀ z ∈ C.Z, directCount G C.P z = 0 := by
    intro z hz
    unfold directCount internalFirstNeighbors
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hpP hzp
    exact hG.2 (hFullPZ p hpP z hz) hzp
  have hZCount : ∀ z ∈ C.Z, directCount G C.Z z = 1 := by
    intro z hz
    have hRetained := z_outdegree_eq_retainedCounts G C z hz
    have hW := hWCount z hz
    have hP := hPCountZero z hz
    have hDeg := hDegreeEight z hz
    simp only [W] at hW
    rw [hDeg, hW, hP] at hRetained
    omega
  have hTournament : ∀ {u : V}, u ∈ C.Z → ∀ {v : V}, v ∈ C.Z →
      u ≠ v → G.Adj u v ∨ G.Adj v u :=
    tournament_of_three_edges G C.Z hZCard hG hInternal
  have hZNonempty : C.Z.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z0, hz0Z⟩ := hZNonempty
  have hOutNonempty : (internalFirstNeighbors G C.Z z0).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < directCount G C.Z z0
    rw [hZCount z0 hz0Z]
    omega
  obtain ⟨z1, hz1Out⟩ := hOutNonempty
  have hz1Z : z1 ∈ C.Z := (Finset.mem_filter.mp hz1Out).1
  have hz01 : G.Adj z0 z1 := (Finset.mem_filter.mp hz1Out).2
  have hz10 : z1 ≠ z0 := by
    intro hEq
    subst z1
    exact hG.1 z0 hz01
  let ZE := C.Z.erase z0
  have hz1ZE : z1 ∈ ZE := Finset.mem_erase.mpr ⟨hz10, hz1Z⟩
  have hZECard : Fintype.card {v : V // v ∈ ZE} = 2 := by
    rw [Fintype.card_coe]
    dsimp [ZE]
    rw [Finset.card_erase_of_mem hz0Z, hZCard]
  obtain ⟨z2s, hz2ne⟩ := Fintype.exists_ne_of_one_lt_card
    (α := {v : V // v ∈ ZE}) (by omega) ⟨z1, hz1ZE⟩
  let z2 : V := z2s.1
  have hz2ZE : z2 ∈ ZE := z2s.2
  have hz2Z : z2 ∈ C.Z := Finset.mem_of_mem_erase hz2ZE
  have hz20ne : z2 ≠ z0 := (Finset.mem_erase.mp hz2ZE).1
  have hz21ne : z2 ≠ z1 := by
    intro hEq
    apply hz2ne
    apply Subtype.ext
    exact hEq
  have hn02 : ¬G.Adj z0 z2 := by
    intro h02
    have hEq := eq_of_adj_of_adj_of_directCount_eq_one G C.Z hz1Z hz2Z
      hz01 h02 (hZCount z0 hz0Z)
    exact hz21ne hEq.symm
  have hz20 : G.Adj z2 z0 :=
    (hTournament hz2Z hz0Z hz20ne).resolve_right hn02
  have hn21 : ¬G.Adj z2 z1 := by
    intro h21
    have hEq := eq_of_adj_of_adj_of_directCount_eq_one G C.Z hz0Z hz1Z
      hz20 h21 (hZCount z2 hz2Z)
    exact hz10 hEq.symm
  have hz12 : G.Adj z1 z2 :=
    (hTournament hz1Z hz2Z hz21ne.symm).resolve_right hn21
  have hS : (G.outNeighborFinset z0).erase z1 = W := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_erase.mp hv with ⟨hvne, hvOut⟩
      have hAdj : G.Adj z0 v := (Digraph.mem_outNeighborFinset (G := G)).mp hvOut
      have hCaptured := z_outgoingCaptured G C z0 hz0Z hvOut
      rcases Finset.mem_union.mp hCaptured with hvZW | hvP
      · rcases Finset.mem_union.mp hvZW with hvZ | hvW
        · have hEq := eq_of_adj_of_adj_of_directCount_eq_one G C.Z hz1Z hvZ
            hz01 hAdj (hZCount z0 hz0Z)
          exact (hvne hEq.symm).elim
        · exact hvW
      · exact (hG.2 (hFullPZ v hvP z0 hz0Z) hAdj).elim
    · intro hvW
      apply Finset.mem_erase.mpr
      refine ⟨?_, (Digraph.mem_outNeighborFinset (G := G)).mpr
        (hAllZW z0 hz0Z v hvW)⟩
      intro hEq
      subst v
      exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C)) hz1Z hvW
  let E := G.outNeighborFinsetOf W \ (W ∪ {z0})
  have hECard : 7 ≤ E.card := by
    have hExpansion := Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour
      (hDegreeEight z0 hz0Z) hz01
    simpa [E, hS] using hExpansion
  have hESubset : E ⊆ G.secondOutNeighborFinset z0 := by
    intro v hvE
    rcases Finset.mem_sdiff.mp hvE with ⟨hvReach, hvOutside⟩
    obtain ⟨w, hwW, hwv⟩ := (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hNotAdj : ¬G.Adj z0 v := by
      intro h0v
      have hvOut : v ∈ G.outNeighborFinset z0 :=
        (Digraph.mem_outNeighborFinset (G := G)).mpr h0v
      by_cases hv1 : v = z1
      · subst v
        exact hG.2 (hAllZW z1 hz1Z w hwW) hwv
      · have hvErase : v ∈ (G.outNeighborFinset z0).erase z1 :=
          Finset.mem_erase.mpr ⟨hv1, hvOut⟩
        have hvW : v ∈ W := by simpa [hS] using hvErase
        exact hvOutside (Finset.mem_union_left _ hvW)
    have hvne : v ≠ z0 := by
      intro hEq
      subst v
      exact hvOutside (Finset.mem_union_right _ (Finset.mem_singleton_self z0))
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨w, hAllZW z0 hz0Z w hwW, hwv⟩, hNotAdj, hvne⟩
  have hz2Second : z2 ∈ G.secondOutNeighborFinset z0 := by
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨z1, hz01, hz12⟩, hn02, hz20ne⟩
  have hz2NotE : z2 ∉ E := by
    intro hz2E
    have hz2Reach := (Finset.mem_sdiff.mp hz2E).1
    obtain ⟨w, hwW, hwz2⟩ := (Digraph.mem_outNeighborFinsetOf (G := G)).mp hz2Reach
    exact hG.2 (hAllZW z2 hz2Z w hwW) hwz2
  have hUnionSubset : E ∪ {z2} ⊆ G.secondOutNeighborFinset z0 :=
    Finset.union_subset hESubset (by simpa using hz2Second)
  have hCard := Finset.card_le_card hUnionSubset
  have hUnionCard : (E ∪ {z2}).card = E.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro v hvE hv2
      simpa using hz2NotE (Finset.mem_singleton.mp hv2 ▸ hvE)
  rw [hUnionCard] at hCard
  have hSeymour : G.IsSeymourVertex z0 := by
    unfold Digraph.IsSeymourVertex Digraph.secondOutdegree
    rw [hDegreeEight z0 hz0Z]
    omega
  exact hNoSeymour ⟨z0, hSeymour⟩

end SeymourEight.ThreeZExactSeven
