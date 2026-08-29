import SeymourEight.Shared.AlmostTournamentKing

set_option linter.style.header false

/-!
# King bounds on exact-degree status classes

The two arithmetic cancellation lemmas combine a local degree identity with
a disjoint contribution to the strict second outneighborhood.  The
almost-tournament argument itself is entirely graph-theoretic.
-/

namespace SeymourEight.Shared

open CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [DecidableEq V] [DecidableRel G.Adj]

/-- Internal missing pairs can only disappear when the vertex set shrinks. -/
theorem internalMissingPairs_mono {S P : Finset V} (hSP : S ⊆ P) :
    internalMissingPairs G S ⊆ internalMissingPairs G P := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨hePair, heMissing⟩
  rcases Finset.mem_powersetCard.mp hePair with ⟨heS, heCard⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨fun v hv ↦ hSP (heS hv), heCard⟩, ?_⟩
  exact heMissing

/-- Strict internal second neighbours are monotone in the ambient vertex set. -/
theorem internalSecondNeighbors_mono {S P : Finset V} (hSP : S ⊆ P)
    (p : V) :
    internalSecondNeighbors (G := G) S p ⊆
      internalSecondNeighbors (G := G) P p := by
  intro v hv
  rcases Finset.mem_filter.mp hv with
    ⟨hvS, hNotAdj, hvp, w, hwS, hpw, hwv⟩
  apply Finset.mem_filter.mpr
  exact ⟨hSP hvS, hNotAdj, hvp, w, hSP hwS, hpw, hwv⟩

/-- Direct counts split over a subset and its complement in the ambient set. -/
theorem directCount_eq_subset_add_compl {S P : Finset V} (hSP : S ⊆ P)
    (p : V) :
    directCount G P p = directCount G S p + directCount G (P \ S) p := by
  have hDisjoint : Disjoint S (P \ S) := by
    rw [Finset.disjoint_left]
    intro v hvS hvDiff
    exact (Finset.mem_sdiff.mp hvDiff).2 hvS
  have hUnion : S ∪ (P \ S) = P := Finset.union_sdiff_of_subset hSP
  calc
    directCount G P p = directCount G (S ∪ (P \ S)) p := by rw [hUnion]
    _ = directCount G S p + directCount G (P \ S) p :=
      directCount_union_of_disjoint G S (P \ S) p hDisjoint

/--
Root-path cancellation bound.  The selected vertex is an almost-tournament
king in `S`; exact degree cancels its internal direct count and the `H`
allowance.
-/
theorem exists_rootStatus_king_bound
    (P S : Finset V) (e h : V → Nat) (hS : S.Nonempty) (hSP : S ⊆ P)
    (hG : G.IsOriented)
    (hDegree : ∀ p ∈ S,
      e p + 1 + h p + directCount G P p = 8)
    (hSecond : ∀ p ∈ S,
      (internalSecondNeighbors (G := G) S p).card + 1 ≤ h p) :
    ∃ p ∈ S, S.card + e p + directCount G (P \ S) p ≤
      7 + (internalMissingPairs G S).card := by
  obtain ⟨p, hpS, hKing⟩ :=
    exists_internalReachWithinTwo_add_missing_ge G S hS hG
  have hSplit := directCount_eq_subset_add_compl G hSP p
  have hDeg := hDegree p hpS
  have hSec := hSecond p hpS
  have hCardPos : 1 ≤ S.card := Finset.one_le_card.mpr hS
  have hKing' : S.card ≤
      (internalReachWithinTwo G S p).card +
        (internalMissingPairs G S).card + 1 := by
    omega
  rw [card_internalReachWithinTwo G S p hG] at hKing'
  have hSBound : S.card ≤ directCount G S p + h p +
      (internalMissingPairs G S).card := by
    omega
  have hDegreeReduced :
      e p + h p + directCount G S p + directCount G (P \ S) p = 7 := by
    omega
  refine ⟨p, hpS, ?_⟩
  calc
    S.card + e p + directCount G (P \ S) p ≤
        (directCount G S p + h p + (internalMissingPairs G S).card) +
          e p + directCount G (P \ S) p := by
      exact Nat.add_le_add_right (Nat.add_le_add_right hSBound (e p)) _
    _ = 7 + (internalMissingPairs G S).card := by omega

/--
No-root cancellation bound, with `lambda` common auxiliary second-neighbour
targets.
-/
theorem exists_noRootStatus_king_bound
    (P S : Finset V) (e h : V → Nat) (lambda : Nat)
    (hS : S.Nonempty) (hSP : S ⊆ P) (hG : G.IsOriented)
    (hDegree : ∀ p ∈ S,
      e p + h p + directCount G P p = 8)
    (hSecond : ∀ p ∈ S,
      (internalSecondNeighbors (G := G) S p).card + lambda ≤ 7 + h p) :
    ∃ p ∈ S,
      S.card + e p + lambda + directCount G (P \ S) p ≤
        16 + (internalMissingPairs G S).card := by
  obtain ⟨p, hpS, hKing⟩ :=
    exists_internalReachWithinTwo_add_missing_ge G S hS hG
  have hSplit := directCount_eq_subset_add_compl G hSP p
  have hDeg := hDegree p hpS
  have hSec := hSecond p hpS
  have hCardPos : 1 ≤ S.card := Finset.one_le_card.mpr hS
  have hKing' : S.card ≤
      (internalReachWithinTwo G S p).card +
        (internalMissingPairs G S).card + 1 := by
    omega
  rw [card_internalReachWithinTwo G S p hG] at hKing'
  have hSBound : S.card + lambda ≤ directCount G S p + 7 + h p +
      (internalMissingPairs G S).card + 1 := by
    omega
  have hDegreeReduced :
      e p + h p + directCount G S p + directCount G (P \ S) p = 8 := by
    omega
  refine ⟨p, hpS, ?_⟩
  calc
    S.card + e p + lambda + directCount G (P \ S) p =
        (S.card + lambda) + e p + directCount G (P \ S) p := by omega
    _ ≤ (directCount G S p + 7 + h p +
          (internalMissingPairs G S).card + 1) + e p +
          directCount G (P \ S) p := by
      exact Nat.add_le_add_right (Nat.add_le_add_right hSBound (e p)) _
    _ = 16 + (internalMissingPairs G S).card := by omega

omit [DecidableEq V] in
/-- Every vertex above the lower degree contributes at least one unit of excess. -/
theorem card_degree_ne_of_lower_le_excess_sum
    (P : Finset V) (degree : V → Nat) (lower : Nat)
    (hLower : ∀ p ∈ P, lower ≤ degree p) :
    (P.filter fun p ↦ degree p ≠ lower).card ≤
      ∑ p ∈ P, (degree p - lower) := by
  calc
    (P.filter fun p ↦ degree p ≠ lower).card =
        ∑ _p ∈ P.filter (fun p ↦ degree p ≠ lower), 1 := by simp
    _ ≤ ∑ p ∈ P.filter (fun p ↦ degree p ≠ lower),
        (degree p - lower) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpNe⟩
      have hpLower := hLower p hpP
      omega
    _ ≤ ∑ p ∈ P, (degree p - lower) := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

omit [DecidableEq V] in
/-- The exact-lower-degree class loses at most the total degree excess. -/
theorem card_le_exact_degree_add_excess
    (P : Finset V) (degree : V → Nat) (lower : Nat)
    (hLower : ∀ p ∈ P, lower ≤ degree p) :
    P.card ≤ (P.filter fun p ↦ degree p = lower).card +
      ∑ p ∈ P, (degree p - lower) := by
  have hBad := card_degree_ne_of_lower_le_excess_sum
    (V := V) P degree lower hLower
  rw [← P.card_filter_add_card_filter_not (fun p ↦ degree p = lower)]
  exact Nat.add_le_add_left hBad _

omit [DecidableEq V] in
/-- The number of non-full rows is at most the unused bipartite capacity. -/
theorem card_nonfull_rows_le_capacity_defect (P T : Finset V) :
    (P.filter fun p ↦ directCount G T p ≠ T.card).card ≤
      P.card * T.card - edgeCount G P T := by
  have hRowLe : ∀ p, directCount G T p ≤ T.card := by
    intro p
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hBadLe : (P.filter fun p ↦ directCount G T p ≠ T.card).card ≤
      ∑ p ∈ P, (T.card - directCount G T p) := by
    calc
      _ = ∑ _p ∈ P.filter (fun p ↦ directCount G T p ≠ T.card), 1 := by simp
      _ ≤ ∑ p ∈ P.filter (fun p ↦ directCount G T p ≠ T.card),
          (T.card - directCount G T p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpNe := (Finset.mem_filter.mp hp).2
        have hpLe := hRowLe p
        omega
      _ ≤ ∑ p ∈ P, (T.card - directCount G T p) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hIdentity :
      (∑ p ∈ P, (T.card - directCount G T p)) + edgeCount G P T =
        P.card * T.card := by
    rw [edgeCount, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _p ∈ P, T.card := by
        apply Finset.sum_congr rfl
        intro p _hp
        have := hRowLe p
        omega
      _ = _ := by simp
  omega

omit [DecidableEq V] in
/-- A single row's missing entries are bounded by total unused capacity. -/
theorem row_defect_le_capacity_defect (P T : Finset V) (p : V)
    (hp : p ∈ P) :
    T.card - directCount G T p ≤ P.card * T.card - edgeCount G P T := by
  have hRowLe : ∀ q, directCount G T q ≤ T.card := by
    intro q
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hTermLe : T.card - directCount G T p ≤
      ∑ q ∈ P, (T.card - directCount G T q) :=
    Finset.single_le_sum (s := P)
      (f := fun q ↦ T.card - directCount G T q) (fun _ _ ↦ Nat.zero_le _) hp
  have hIdentity :
      (∑ q ∈ P, (T.card - directCount G T q)) + edgeCount G P T =
        P.card * T.card := by
    rw [edgeCount, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _q ∈ P, T.card := by
        apply Finset.sum_congr rfl
        intro q _hq
        have := hRowLe q
        omega
      _ = _ := by simp
  omega

end SeymourEight.Shared
