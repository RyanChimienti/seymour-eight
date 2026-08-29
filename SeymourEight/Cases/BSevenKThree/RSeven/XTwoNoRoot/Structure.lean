import SeymourEight.Cases.BSevenKThree.Basic
import SeymourEight.Cases.BSixKThree.Basic
import SeymourEight.Shared.AlmostTournamentKing

set_option linter.style.header false

/-!
# Rigid structure of the `r = 7`, `x = 2` family

The three `A₁` rows attain every available internal-arc capacity: there are
three arcs inside `A₁` and all six arcs from `A₁` to `X`.  Consequently every
`A₁` vertex ties the pivot's internal degree and hence points to all of `P`.
-/

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Structure

open Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem p_eq_B (C : G.LocalConfiguration) (hBCard : C.B.card = 7)
    (hr : C.r = 7) : C.P = C.B := by
  change C.P.card = 7 at hr
  apply Finset.eq_of_subset_of_card_le
    (Digraph.LocalConfiguration.P_subset_B (G := G) C)
  omega

theorem A1_edgeCount_eq_nine (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hx : C.x = 2) :
    edgeCount G C.A1 C.A = 9 := by
  have hA1Card : C.A1.card = 3 := hk
  have hXCard : C.X.card = 2 := hx
  have hLower : 9 ≤ edgeCount G C.A1 C.A := by
    calc
      9 = ∑ _u ∈ C.A1, 3 := by simp [hA1Card]
      _ ≤ ∑ u ∈ C.A1, directCount G C.A u := by
        apply Finset.sum_le_sum
        intro u hu
        simpa [directCount, internalFirstNeighbors, hk] using
          (hPivot u
            (Digraph.LocalConfiguration.A1_subset_A (G := G) C hu)).1
      _ = edgeCount G C.A1 C.A := rfl
  have hToH : edgeCount G C.A1 C.A ≤ edgeCount G C.A1 C.H := by
    unfold edgeCount directCount
    apply Finset.sum_le_sum
    intro u hu
    exact Finset.card_le_card
      (BSixKThree.A1_A_neighbors_subset_H G C hG u hu)
  have hSplit : edgeCount G C.A1 C.H =
      edgeCount G C.A1 C.A1 + edgeCount G C.A1 C.X :=
    edgeCount_union_of_disjoint G C.A1 C.A1 C.X
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hInternal := internal_edgeCount_le_choose_two G C.A1 hG
  have hCross := edgeCount_le_card_mul_card G C.A1 C.X
  rw [hA1Card] at hInternal hCross
  rw [hXCard] at hCross
  simp [Nat.choose] at hInternal
  omega

theorem A1_internalDegree_eq_three (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hx : C.x = 2) (u : V) (hu : u ∈ C.A1) :
    directCount G C.A u = 3 := by
  have hA1Card : C.A1.card = 3 := hk
  apply pointwise_eq_of_sum_eq_card_mul C.A1 (directCount G C.A) 3
      (fun v hv => by
        simpa [directCount, internalFirstNeighbors, hk] using
          (hPivot v
            (Digraph.LocalConfiguration.A1_subset_A (G := G) C hv)).1)
      (by
        change edgeCount G C.A1 C.A = C.A1.card * 3
        rw [A1_edgeCount_eq_nine G C hG hPivot hk hx, hA1Card])
      u hu

theorem A1_adj_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 2)
    (u p : V) (hu : u ∈ C.A1) (hp : p ∈ C.P) : G.Adj u p := by
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.A1_subset_A (G := G) C hu
  have hInternal :
      (C.A.filter (G.Adj u)).card = C.k := by
    change directCount G C.A u = C.k
    rw [A1_internalDegree_eq_three G C hG hPivot hk hx u hu, hk]
  have hTie := (hPivot u huA).2 hInternal
  change C.r ≤ directCount G C.B u at hTie
  have hDirectLe : directCount G C.B u ≤ C.B.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hDirect : directCount G C.B u = 7 := by omega
  have hFilter : C.B.filter (G.Adj u) = C.B := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    change C.B.card ≤ directCount G C.B u
    omega
  have hpB := Digraph.LocalConfiguration.P_subset_B (G := G) C hp
  have hpFilter : p ∈ C.B.filter (G.Adj u) := by simpa [hFilter] using hpB
  exact (Finset.mem_filter.mp hpFilter).2

theorem P_not_adj_A1 (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 2)
    (p u : V) (hp : p ∈ C.P) (hu : u ∈ C.A1) : ¬G.Adj p u :=
  hG.2 (A1_adj_P G C hG hPivot hBCard hk hr hx u p hu hp)

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Structure
