import SeymourEight.Cases.BSixKTwo.Basic
import SeymourEight.CaseFramework
import SeymourEight.Shared.LocalDegree

/-!
# Counting reduction for the `(6,2)` case

The generic local edge-count lemmas leave only `x=1,2,3`.  In every row the
external target set has the maximum possible size `7-x`; the `x=3` row is
fully tight.
-/

namespace SeymourEight.BSixKTwo

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimality forces at least one vertex into `X`. -/
theorem one_le_x (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) :
    1 ≤ C.x := by
  have hA1Card : C.A1.card = 2 := hk
  have hA1Nonempty : C.A1.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, huA1⟩ := hA1Nonempty
  have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have hInternal : 2 ≤ (C.A.filter (G.Adj u)).card := by
    have h := (hPivot u huA).1
    omega
  have hSubset : C.A.filter (G.Adj u) ⊆ C.A1.erase u ∪ C.X := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvA, huv⟩
    by_cases hvA1 : v ∈ C.A1
    · exact Finset.mem_union_left C.X
        (Finset.mem_erase.mpr ⟨fun h ↦ hG.1 u (h ▸ huv), hvA1⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_inter.mpr
      constructor
      · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        exact ⟨u, Finset.mem_union_left C.P huA1, huv⟩
      · apply Finset.mem_sdiff.mpr
        refine ⟨hvA, ?_⟩
        intro hvParts
        rcases Finset.mem_union.mp hvParts with hvA1' | hva1
        · exact hvA1 hvA1'
        · have hva1Eq : v = C.a1 := Finset.mem_singleton.mp hva1
          subst v
          have ha1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
          exact hG.2 ha1u huv
  have hCardLe : (C.A.filter (G.Adj u)).card ≤ 1 + C.x := by
    calc
      (C.A.filter (G.Adj u)).card ≤ (C.A1.erase u ∪ C.X).card :=
        Finset.card_le_card hSubset
      _ ≤ (C.A1.erase u).card + C.X.card := Finset.card_union_le _ _
      _ = 1 + C.x := by
        rw [Finset.card_erase_of_mem huA1, hA1Card]
        rfl
  omega

/-- The six-by-external-target incidence block has its evident capacity. -/
theorem external_edgeCount_le (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) :
    edgeCount G C.P (externalTargets G C) ≤
      6 * (C.z + epsilonS G C) := by
  calc
    edgeCount G C.P (externalTargets G C) ≤
        C.P.card * (externalTargets G C).card :=
      Shared.edgeCount_le_card_mul_card G _ _
    _ = 6 * (C.z + epsilonS G C) := by
      rw [hPCard, card_externalTargets]

/-- The `H` degree lower bound specialized to `k=2`. -/
theorem H_degree_capacity (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 2) :
    8 * (C.x + 2) ≤ edgeCount G C.H C.P +
      (C.x + 2).choose 2 + C.x + C.x * (5 - C.x) := by
  have hFive := Shared.equationFive G C hG hMin hPB
  have hH := h_card_eq_x_add_two G C hk
  have hXR := x_add_card_R_eq_five G C hG hRootDegree hk
  have hxLe : C.x ≤ 5 := by omega
  rw [hH] at hFive
  have hR : C.R.card = 5 - C.x := by omega
  rw [hR] at hFive
  exact hFive

/-- Summing the six `P` degrees yields the reverse capacity inequality. -/
theorem P_degree_capacity (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (hPCard : C.P.card = 6) (hk : C.k = 2) :
    48 + edgeCount G C.H C.P ≤
      edgeCount G C.P (externalTargets G C) + 6 * (C.x + 2) + 15 := by
  have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternal := edgeCount_externalTargets G C
  have hCross := Shared.cross_edgeCount_add_reverse_le
    G C.H C.P hG
  have hInternal := Shared.internal_edgeCount_le_choose_two
    G C.P hG
  have hH := h_card_eq_x_add_two G C hk
  rw [hPCard, hH] at hCross
  have hChoose : C.P.card.choose 2 = 15 := by simp [hPCard, Nat.choose]
  rw [hChoose] at hInternal
  omega

/-- Only the three rows `x=1,2,3` remain, and every external block is full-size. -/
theorem parameterRows (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 6) (hk : C.k = 2) :
    (C.x = 1 ∧ C.z + epsilonS G C = 6) ∨
      (C.x = 2 ∧ C.z + epsilonS G C = 5) ∨
      (C.x = 3 ∧ C.z + epsilonS G C = 4) := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 6 := r_eq_six G C hG hMin hBCard hk
  have hxOne := one_le_x G C hG hPivot hk
  have hXR := x_add_card_R_eq_five G C hG hRootDegree hk
  have hBasic := x_add_z_add_epsilonS_le_seven
    G C hG hMin hNoSeymour hBCard hk
  have hHCapacity := H_degree_capacity G C hG hMin hPB hRootDegree hk
  have hPCapacity := P_degree_capacity G C hG hMin hPB hPCard hk
  have hExternal := external_edgeCount_le G C hPCard
  have hxCases : C.x = 1 ∨ C.x = 2 ∨ C.x = 3 ∨ C.x = 4 ∨ C.x = 5 := by
    omega
  rcases hxCases with hx | hx | hx | hx | hx
  · left
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hHCapacity
    omega
  · right; left
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hHCapacity
    omega
  · right; right
    refine ⟨hx, ?_⟩
    simp only [hx, Nat.choose] at hHCapacity
    omega
  · simp only [hx, Nat.choose] at hHCapacity
    omega
  · simp only [hx, Nat.choose] at hHCapacity
    omega

/-- In the `x=3` row the two cross-block counts are tight. -/
theorem x_three_tight_counts (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 6) (hk : C.k = 2)
    (hx : C.x = 3) (hw : C.z + epsilonS G C = 4) :
    edgeCount G C.H C.P = 21 ∧ edgeCount G C.P C.H = 9 := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 6 := r_eq_six G C hG hMin hBCard hk
  have hHCard := h_card_eq_x_add_two G C hk
  have hR := x_add_card_R_eq_five G C hG hRootDegree hk
  have hHCapacity := H_degree_capacity G C hG hMin hPB hRootDegree hk
  have hPCapacity := P_degree_capacity G C hG hMin hPB hPCard hk
  have hExternal := external_edgeCount_le G C hPCard
  have hCross := Shared.cross_edgeCount_add_reverse_le
    G C.H C.P hG
  have hPInternal := Shared.internal_edgeCount_le_choose_two
    G C.P hG
  rw [hHCard, hx] at hCross
  rw [hPCard] at hCross hPInternal
  rw [hx] at hHCapacity
  rw [hx] at hPCapacity
  rw [hw] at hExternal
  simp [Nat.choose] at hHCapacity hCross hPInternal
  have hEHP : edgeCount G C.H C.P = 21 := by omega
  have hExternalEq : edgeCount G C.P (externalTargets G C) = 24 := by omega
  have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternalAccounting := edgeCount_externalTargets G C
  have hEPH : edgeCount G C.P C.H = 9 := by omega
  exact ⟨hEHP, hEPH⟩

end SeymourEight.BSixKTwo
