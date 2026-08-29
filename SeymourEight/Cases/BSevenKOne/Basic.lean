import SeymourEight.CaseFramework
import SeymourEight.DegreeEight
import SeymourEight.Shared.Neighborhood

set_option linter.style.header false

/-!
# The `(|B|,k)=(7,1)` case

This file develops the graph-level proposition `BSevenKOneCase`.  The first
reduction proves that its initial cardinal assumptions force `P=B`, `r=7`,
and exact outdegree eight at the chosen pivot `a1`.
-/

namespace SeymourEight.BSevenKOne

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the `(7,1)` row, minimum degree forces all seven vertices of `B` into `P`. -/
theorem r_eq_seven (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    C.r = 7 := by
  have hDegree := hMin C.a1
  rw [outdegree_a1_eq_k_add_r G C hG, hk] at hDegree
  have hrLe : C.r ≤ 7 := by
    calc
      C.r = C.P.card := rfl
      _ ≤ C.B.card := Finset.card_le_card
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
      _ = 7 := hBCard
  omega

/-- Consequently `P=B`. -/
theorem p_eq_B (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    C.P = C.B := by
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  apply Finset.eq_of_subset_of_card_le
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  rw [hPCard, hBCard]

/-- The chosen pivot itself has exact outdegree eight. -/
theorem outdegree_a1_eq_eight (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    G.outdegree C.a1 = 8 := by
  rw [outdegree_a1_eq_k_add_r G C hG, hk,
    r_eq_seven G C hG hMin hBCard hk]

/-- The forced initial data of the graph-level `(7,1)` case. -/
theorem forced_tight_start (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    C.r = 7 ∧ C.P = C.B ∧ G.outdegree C.a1 = 8 := by
  exact ⟨r_eq_seven G C hG hMin hBCard hk,
    p_eq_B G C hG hMin hBCard hk,
    outdegree_a1_eq_eight G C hG hMin hBCard hk⟩

/-- The protected targets reached from a `P`-vertex through the root. -/
def protectedFinset (C : G.LocalConfiguration) : Finset V :=
  {C.a1} ∪ C.R

/-- In the terminal `x=4` row, the protected family is `{a1} ∪ R` of size three. -/
theorem protectedFinset_card_eq_three (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 1) (hx : C.x = 4) :
    (protectedFinset G C).card = 3 := by
  have hRCount :=
    Digraph.LocalConfiguration.x_add_card_R_eq_six_of_k_eq_one
      (G := G) C hG.1 hRootDegree hk
  have hDisjoint : Disjoint ({C.a1} : Finset V) C.R := by
    rw [Finset.disjoint_left]
    intro v hvPivot hvR
    have hv : v = C.a1 := Finset.mem_singleton.mp hvPivot
    subst v
    exact (Finset.mem_sdiff.mp hvR).2 (by simp)
  unfold protectedFinset
  rw [Finset.card_union_of_disjoint hDisjoint]
  simp
  omega

/-- Every protected target is a strict second neighbor through the root. -/
theorem protectedFinset_subset_second (C : G.LocalConfiguration)
    (hG : G.IsOriented) (p : V) (hp : p ∈ C.P) (hps : G.Adj p C.s) :
    protectedFinset G C ⊆ G.secondOutNeighborFinset p := by
  intro w hw
  have hsw : G.Adj C.s w := by
    rcases Finset.mem_union.mp hw with hwPivot | hwR
    · have hwEq : w = C.a1 := Finset.mem_singleton.mp hwPivot
      subst w
      exact (Digraph.mem_outNeighborFinset (G := G)).mp C.a1_mem_root_outNeighbors
    · exact (Digraph.mem_outNeighborFinset (G := G)).mp
        (Digraph.LocalConfiguration.R_subset_A (G := G) C hwR)
  have hpw : ¬G.Adj p w := by
    rcases Finset.mem_union.mp hw with hwPivot | hwR
    · have hwEq : w = C.a1 := Finset.mem_singleton.mp hwPivot
      subst w
      have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hp).2
      exact hG.2 ha1p
    · intro hpw
      have hwX : w ∈ C.X := by
        apply Finset.mem_inter.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          exact ⟨p, Finset.mem_union_right C.A1 hp, hpw⟩
        · apply Finset.mem_sdiff.mpr
          refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hwR, ?_⟩
          intro hwParts
          exact (Finset.mem_sdiff.mp hwR).2 (by
            rcases Finset.mem_union.mp hwParts with hwA1 | hwPivot
            · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hwA1)
            · exact Finset.mem_union_right (C.A1 ∪ C.X) hwPivot)
      exact (Finset.mem_sdiff.mp hwR).2
        (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hwX))
  have hwp : w ≠ p := by
    intro hEq
    subst w
    exact hG.2 hps hsw
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨C.s, hps, hsw⟩, hpw, hwp⟩

/--
A degree-eight `P`-vertex pointing to the root still reaches at least two of
the three protected targets after its root arc is deleted.
-/
theorem two_protected_reached_after_root_deletion
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 4)
    (p : V) (hp : p ∈ C.P) (hpDegree : G.outdegree p = 8)
    (hps : G.Adj p C.s) :
    2 ≤
      (protectedFinset G C ∩
        (G.outNeighborFinsetOf (G.outNeighborFinset p |>.erase C.s) \
          ((G.outNeighborFinset p |>.erase C.s) ∪ {p}))).card := by
  have hReach := Digraph.oneArcDeletion_reaches_all_but_one G
    (protectedFinset G C) hBound hG hNoSeymour hpDegree hps
    (protectedFinset_subset_second G C hG p hp hps)
  rw [protectedFinset_card_eq_three G C hG hRootDegree hk hx] at hReach
  omega

/-- The minimum-pivot convention forces `X` to be nonempty when `k=1`. -/
theorem one_le_x (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 1) :
    1 ≤ C.x := by
  have hA1Card : C.A1.card = 1 := hk
  obtain ⟨u, hA1⟩ := Finset.card_eq_one.mp hA1Card
  have huA1 : u ∈ C.A1 := by simp [hA1]
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have hInternal : 1 ≤ (C.A.filter (G.Adj u)).card := by
    have hMinU := (hPivot u huA).1
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 <
    (C.A.filter (G.Adj u)).card)
  rcases Finset.mem_filter.mp hv with ⟨hvA, huv⟩
  have hvNotA1 : v ∉ C.A1 := by
    intro hvA1
    have hvu : v = u := by simpa [hA1] using hvA1
    subst v
    exact hG.1 u huv
  have hva1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
  have hva1 : v ≠ C.a1 := by
    intro h
    subst v
    exact hG.2 hva1u huv
  have hvX : v ∈ C.X := by
    apply Finset.mem_inter.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨u, Finset.mem_union_left C.P huA1, huv⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨hvA, ?_⟩
      intro hvParts
      rcases Finset.mem_union.mp hvParts with hvA1 | hva1'
      · exact hvNotA1 hvA1
      · exact hva1 (Finset.mem_singleton.mp hva1')
  exact Finset.card_pos.mpr ⟨v, hvX⟩

/-- A no-Seymour `(7,1)` configuration satisfies the basic `x+z+epsilon_s≤7` bound. -/
theorem x_add_z_add_epsilonS_le_seven (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hBCard : C.B.card = 7) (hk : C.k = 1) :
    C.x + C.z + epsilonS G C ≤ 7 := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hSecond := secondOutdegree_a1_eq_x_add_z_add_epsilonS G C hG hPB
  have hDegree := outdegree_a1_eq_eight G C hG hMin hBCard hk
  have hNotA1 : ¬G.IsSeymourVertex C.a1 := by
    intro hSeymour
    exact hNoSeymour ⟨C.a1, hSeymour⟩
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNotA1
  omega

end SeymourEight.BSevenKOne
