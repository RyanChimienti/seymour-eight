import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGraphBridge
import SeymourEight.Shared.ArcCounting

set_option linter.style.header false

/-!
# Four-`Z` capacity bound

With at most one missing `P → Z` incidence, four `Z` vertices have at least
seven distinct outneighbors outside `P ∪ Z`.  This is the manual reduction
that leaves only the union-at-least-eight and exact-seven certificate cores.
-/

namespace SeymourEight.FourZCapacity

open FiveZExactGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem twentySeven_le_PZ_of_missing_le_one (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hMissing : 28 - edgeCount G C.P C.Z ≤ 1) :
    27 ≤ edgeCount G C.P C.Z := by
  have hUpper := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hUpper
  omega

/-- Four `Z` vertices and at most one missing `P → Z` incidence force a
seven-vertex external union. -/
theorem seven_le_zExternalUnion_card (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hPZ : 27 ≤ edgeCount G C.P C.Z) :
    7 ≤ (zExternalUnion G C).card := by
  have hInternal := internal_edgeCount_le_choose_two G C.Z hG
  have hCross := cross_edgeCount_add_reverse_le G C.P C.Z hG
  have hExternal := edgeCount_le_card_mul_card
    G C.Z (zExternalUnion G C)
  have hReverse : edgeCount G C.Z C.P ≤ 1 := by
    rw [hPCard, hZCard] at hCross
    omega
  have hInternal' : edgeCount G C.Z C.Z ≤ 6 := by
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
  have hDegreeLower : 32 ≤ ∑ z ∈ C.Z, G.outdegree z := by
    calc
      32 = ∑ _z ∈ C.Z, 8 := by simp [hZCard]
      _ ≤ ∑ z ∈ C.Z, G.outdegree z := by
        apply Finset.sum_le_sum
        intro z hz
        exact hMin z
  by_contra hNot
  have hWLe : (zExternalUnion G C).card ≤ 6 := by omega
  have hExternal' : edgeCount G C.Z (zExternalUnion G C) ≤ 24 := by
    calc
      _ ≤ C.Z.card * (zExternalUnion G C).card := hExternal
      _ ≤ 24 := by rw [hZCard]; omega
  omega

end SeymourEight.FourZCapacity
