import SeymourEight.Definitions

set_option linter.style.header false

/-!
# Local sets around a degree-eight root

This file defines the set vocabulary used throughout the degree-eight
reduction.  A local configuration chooses a root `s` and an outneighbor `a1`.
The sets `A`, `B`, `A1`, `P`, `Q`, `X`, `R`, `Z`, and `H` describe the first
and second outneighborhoods of these vertices and the relevant intersections.
-/

namespace Digraph

variable {V : Type*} (G : Digraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A root `s` together with a distinguished first outneighbor `a1`. -/
structure LocalConfiguration where
  s : V
  a1 : V
  a1_mem_root_outNeighbors : a1 ∈ G.outNeighborFinset s

namespace LocalConfiguration

variable (C : G.LocalConfiguration)

/-- `A = N⁺(s)`. -/
def A : Finset V :=
  G.outNeighborFinset C.s

/-- `B = N⁺⁺(s)`. -/
def B : Finset V :=
  G.secondOutNeighborFinset C.s

/-- `A1 = N⁺(a1) ∩ A`. -/
def A1 : Finset V :=
  C.A.filter (G.Adj C.a1)

/-- `P = N⁺(a1) ∩ B`. -/
def P : Finset V :=
  C.B.filter (G.Adj C.a1)

/-- `Q = B \ P`. -/
def Q : Finset V :=
  C.B \ C.P

/-- `X = N⁺(A1 ∪ P) ∩ (A \ (A1 ∪ {a1}))`. -/
def X : Finset V :=
  G.outNeighborFinsetOf (C.A1 ∪ C.P) ∩ (C.A \ (C.A1 ∪ {C.a1}))

/-- The vertices of `A` not belonging to `{a1} ∪ A1 ∪ X`. -/
def R : Finset V :=
  C.A \ (C.A1 ∪ C.X ∪ {C.a1})

/-- `Z = N⁺(P) \ ({s} ∪ A ∪ B)`. -/
def Z : Finset V :=
  G.outNeighborFinsetOf C.P \ ({C.s} ∪ C.A ∪ C.B)

/-- `H = A1 ∪ X`, the local `A`-vertices retained in the terminal core. -/
def H : Finset V :=
  C.A1 ∪ C.X

/-- `k = |A1|`. -/
def k : ℕ := C.A1.card

/-- `r = |P|`. -/
def r : ℕ := C.P.card

/-- `x = |X|`. -/
def x : ℕ := C.X.card

/-- `z = |Z|`. -/
def z : ℕ := C.Z.card

/-- `h = |H|`. -/
def h : ℕ := C.H.card

omit [DecidableEq V] in
@[simp]
theorem a1_mem_A : C.a1 ∈ C.A :=
  C.a1_mem_root_outNeighbors

omit [DecidableEq V] in
theorem A1_subset_A : C.A1 ⊆ C.A :=
  Finset.filter_subset _ _

theorem P_subset_B : C.P ⊆ C.B :=
  Finset.filter_subset _ _

theorem Q_subset_B : C.Q ⊆ C.B :=
  Finset.sdiff_subset

/-- `P` and `Q` partition `B`. -/
theorem P_union_Q : C.P ∪ C.Q = C.B := by
  rw [Q, Finset.union_sdiff_of_subset (P_subset_B (G := G) C)]

theorem disjoint_P_Q : Disjoint C.P C.Q := by
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  exact (Finset.mem_sdiff.mp hvQ).2 hvP

/-- The cardinal form of the partition `B = P ∪ Q`. -/
theorem card_B_eq_r_add_card_Q : C.B.card = C.r + C.Q.card := by
  rw [← P_union_Q (G := G) C,
    Finset.card_union_of_disjoint (disjoint_P_Q (G := G) C)]
  rfl

theorem X_subset_A : C.X ⊆ C.A := by
  intro v hv
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1

theorem H_subset_A : C.H ⊆ C.A := by
  intro v hv
  rcases Finset.mem_union.mp hv with hvA1 | hvX
  · exact A1_subset_A (G := G) C hvA1
  · exact X_subset_A (G := G) C hvX

/-- First and strict second outneighbors of the root are disjoint. -/
theorem disjoint_A_B : Disjoint C.A C.B := by
  rw [Finset.disjoint_left]
  intro v hvA hvB
  have hAdj : G.Adj C.s v :=
    (mem_outNeighborFinset (G := G)).mp hvA
  have hSecondSet : v ∈ G.secondOutNeighborSet C.s :=
    (mem_secondOutNeighborFinset (G := G)).mp hvB
  have hNotAdj : ¬G.Adj C.s v :=
    ((mem_secondOutNeighborSet (G := G)).mp hSecondSet).2.1
  exact hNotAdj hAdj

theorem disjoint_H_P : Disjoint C.H C.P := by
  rw [Finset.disjoint_left]
  intro v hvH hvP
  exact (Finset.disjoint_left.mp (disjoint_A_B (G := G) C))
    (H_subset_A (G := G) C hvH) (P_subset_B (G := G) C hvP)

omit [DecidableEq V] in
theorem s_notMem_A (hG : G.IsLoopless) : C.s ∉ C.A := by
  intro hsA
  exact hG C.s ((mem_outNeighborFinset (G := G)).mp hsA)

theorem s_notMem_B : C.s ∉ C.B := by
  intro hsB
  have hSecondSet : C.s ∈ G.secondOutNeighborSet C.s :=
    (mem_secondOutNeighborFinset (G := G)).mp hsB
  exact ((mem_secondOutNeighborSet (G := G)).mp hSecondSet).2.2 rfl

theorem s_notMem_H (hG : G.IsLoopless) : C.s ∉ C.H :=
  fun hsH ↦ s_notMem_A (G := G) C hG (H_subset_A (G := G) C hsH)

theorem s_notMem_P : C.s ∉ C.P :=
  fun hsP ↦ s_notMem_B (G := G) C (P_subset_B (G := G) C hsP)

theorem disjoint_A1_X : Disjoint C.A1 C.X := by
  rw [Finset.disjoint_left]
  intro v hvA1 hvX
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvX).2).2
    (Finset.mem_union_left _ hvA1)

/-- Since `A1` and `X` are disjoint, `h = k + x`. -/
theorem h_eq_k_add_x : C.h = C.k + C.x := by
  rw [h, H, Finset.card_union_of_disjoint (disjoint_A1_X (G := G) C)]
  rfl

theorem a1_notMem_X : C.a1 ∉ C.X := by
  intro h
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2 (by simp)

omit [DecidableEq V] in
/-- Looplessness keeps the pivot `a1` out of its own `A`-outneighborhood. -/
theorem a1_notMem_A1 (hG : G.IsLoopless) : C.a1 ∉ C.A1 := by
  intro h
  exact hG C.a1 (Finset.mem_filter.mp h).2

theorem R_subset_A : C.R ⊆ C.A :=
  Finset.sdiff_subset

/-- `A1`, `X`, `{a1}`, and `R` together cover exactly `A`. -/
theorem local_parts_union_R :
    (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R = C.A := by
  rw [R, Finset.union_sdiff_of_subset]
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hvA1 | hvX
    · exact A1_subset_A (G := G) C hvA1
    · exact X_subset_A (G := G) C hvX
  · have : v = C.a1 := Finset.mem_singleton.mp hv
    exact this ▸ C.a1_mem_root_outNeighbors

theorem disjoint_local_parts_R :
    Disjoint (C.A1 ∪ C.X ∪ {C.a1}) C.R := by
  rw [Finset.disjoint_left]
  intro v hvParts hvR
  exact (Finset.mem_sdiff.mp hvR).2 hvParts

/-- In a loopless graph, `A` is the disjoint union of `A1`, `X`, `{a1}`, and `R`. -/
theorem card_A_eq_k_add_x_add_one_add_card_R (hG : G.IsLoopless) :
    C.A.card = C.k + C.x + 1 + C.R.card := by
  have hAXa : Disjoint (C.A1 ∪ C.X) {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvAX hvPivot
    have hv : v = C.a1 := Finset.mem_singleton.mp hvPivot
    subst v
    rcases Finset.mem_union.mp hvAX with hvA1 | hvX
    · exact a1_notMem_A1 (G := G) C hG hvA1
    · exact a1_notMem_X (G := G) C hvX
  calc
    C.A.card = (C.A1 ∪ C.X ∪ {C.a1} ∪ C.R).card := by
      rw [local_parts_union_R (G := G) C]
    _ = (C.A1 ∪ C.X ∪ {C.a1}).card + C.R.card :=
      Finset.card_union_of_disjoint (disjoint_local_parts_R (G := G) C)
    _ = (C.A1 ∪ C.X).card + 1 + C.R.card := by
      rw [Finset.card_union_of_disjoint hAXa]
      simp
    _ = C.A1.card + C.X.card + 1 + C.R.card := by
      rw [Finset.card_union_of_disjoint (disjoint_A1_X (G := G) C)]
    _ = C.k + C.x + 1 + C.R.card := rfl

/-- When the root has outdegree eight, the three variable parts of `A` sum to seven. -/
theorem k_add_x_add_card_R_eq_seven (hG : G.IsLoopless)
    (hA : C.A.card = 8) :
    C.k + C.x + C.R.card = 7 := by
  have h := card_A_eq_k_add_x_add_one_add_card_R (G := G) C hG
  omega

/-- The specialization of the preceding count used throughout the `k = 1` case. -/
theorem x_add_card_R_eq_six_of_k_eq_one (hG : G.IsLoopless)
    (hA : C.A.card = 8) (hk : C.k = 1) :
    C.x + C.R.card = 6 := by
  have h := k_add_x_add_card_R_eq_seven (G := G) C hG hA
  omega

/-- `Z` is disjoint from every already known vertex in `{s} ∪ A ∪ B`. -/
theorem disjoint_Z_known : Disjoint C.Z ({C.s} ∪ C.A ∪ C.B) := by
  rw [Finset.disjoint_left]
  intro v hvZ hvKnown
  exact (Finset.mem_sdiff.mp hvZ).2 hvKnown

theorem disjoint_Z_H : Disjoint C.Z C.H := by
  rw [Finset.disjoint_left]
  intro v hvZ hvH
  apply (Finset.disjoint_left.mp (disjoint_Z_known (G := G) C)) hvZ
  exact Finset.mem_union_left C.B <|
    Finset.mem_union_right {C.s} (H_subset_A (G := G) C hvH)

theorem disjoint_Z_P : Disjoint C.Z C.P := by
  rw [Finset.disjoint_left]
  intro v hvZ hvP
  apply (Finset.disjoint_left.mp (disjoint_Z_known (G := G) C)) hvZ
  exact Finset.mem_union_right ({C.s} ∪ C.A) (P_subset_B (G := G) C hvP)

theorem s_notMem_Z : C.s ∉ C.Z := by
  intro hsZ
  apply (Finset.disjoint_left.mp (disjoint_Z_known (G := G) C)) hsZ
  exact Finset.mem_union_left C.B (Finset.mem_union_left C.A (by simp))

end LocalConfiguration

end Finite

end Digraph
