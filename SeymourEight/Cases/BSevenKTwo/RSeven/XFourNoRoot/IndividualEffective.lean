import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.FiveZUnionEightCapacity
import SeymourEight.Cases.BSevenKTwo.Basic
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

/-!
# Individual four-auxiliary capacity

This module proves the individual effective-target bound for four vertices of
`Z`.  Both the three- and four-`Z` certificate bridges reuse the same graph
counting argument.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective

open Shared FiveZExactGraphBridge FiveZUnionEightCapacity

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem directZ_to_Z_capacity_four (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hZCard : C.Z.card = 4) (p : V) :
    edgeCount G (directZNeighbors G C p) C.Z ≤
      (directZNeighbors G C p).card.choose 2 +
        (directZNeighbors G C p).card *
          (4 - (directZNeighbors G C p).card) := by
  let S := directZNeighbors G C p
  let T := C.Z \ S
  have hS : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = C.Z := Finset.union_sdiff_of_subset hS
  have hSplit : edgeCount G S C.Z = edgeCount G S S + edgeCount G S T := by
    rw [← hUnion, edgeCount_union_of_disjoint G S S T hST]
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hCross := edgeCount_le_card_mul_card G S T
  have hTCard : T.card = 4 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hZCard]
  calc
    edgeCount G (directZNeighbors G C p) C.Z =
        edgeCount G S S + edgeCount G S T := hSplit
    _ ≤ S.card.choose 2 + S.card * T.card :=
      Nat.add_le_add hInternal hCross
    _ = (directZNeighbors G C p).card.choose 2 +
        (directZNeighbors G C p).card *
          (4 - (directZNeighbors G C p).card) := by rw [hTCard]

/-- The effective targets supplied by the direct `Z`-neighbors of `p`:
everything they reach except `P` and the already-direct set itself.  Thus it
contains both genuinely external targets and missed vertices of `Z`. -/
def directZEffectiveUnion (C : G.LocalConfiguration) (p : V) : Finset V :=
  G.outNeighborFinsetOf (directZNeighbors G C p) \
    (C.P ∪ directZNeighbors G C p)

theorem directZ_effective_capacity_lower (C : G.LocalConfiguration)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (p : V) :
    (directZNeighbors G C p).card *
        (8 - (directZEffectiveUnion G C p).card) ≤
      edgeCount G (directZNeighbors G C p) (directZNeighbors G C p) +
        edgeCount G (directZNeighbors G C p) C.P := by
  let S := directZNeighbors G C p
  let T := C.Z \ S
  let W := zExternalUnion G C
  let U := directZEffectiveUnion G C p
  have hS : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hTW : Disjoint T W := by
    rw [Finset.disjoint_left]
    intro v hvT hvW
    exact (Finset.mem_sdiff.mp hvW).2
      (Finset.mem_union_right C.P (Finset.mem_sdiff.mp hvT).1)
  have hZSplit : C.Z = S ∪ T := (Finset.union_sdiff_of_subset hS).symm
  have hOutside : ∀ z ∈ S,
      directCount G T z + directCount G W z ≤ U.card := by
    intro z hzS
    rw [← directCount_union_of_disjoint G T W z hTW]
    apply Finset.card_le_card
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvTW, hzv⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      ⟨z, hzS, hzv⟩, ?_⟩
    intro hvPS
    rcases Finset.mem_union.mp hvPS with hvP | hvS
    · rcases Finset.mem_union.mp hvTW with hvT | hvW
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
            (Finset.mem_sdiff.mp hvT).1 hvP
      · exact (Finset.mem_sdiff.mp hvW).2
          (Finset.mem_union_left C.Z hvP)
    · rcases Finset.mem_union.mp hvTW with hvT | hvW
      · exact (Finset.mem_sdiff.mp hvT).2 hvS
      · exact (Finset.mem_sdiff.mp hvW).2
          (Finset.mem_union_right C.P (hS hvS))
  by_cases hLarge : 8 ≤ U.card
  · have : 8 - (directZEffectiveUnion G C p).card = 0 := by
      exact Nat.sub_eq_zero_of_le (by simpa [U] using hLarge)
    rw [this]
    simp
  · have hPointwise : ∀ z ∈ S,
        8 ≤ directCount G S z + directCount G C.P z + U.card := by
      intro z hzS
      have hDegree := FiveZExactGraphBridge.z_outdegree_eq_retainedCounts
        G C z (hS hzS)
      have hMinZ := hMin z
      have hOut := hOutside z hzS
      simp only [W] at hOut
      rw [hZSplit, directCount_union_of_disjoint G S T z hST] at hDegree
      omega
    have hSum : S.card * 8 ≤
        edgeCount G S S + edgeCount G S C.P + S.card * U.card := by
      calc
        S.card * 8 = ∑ _z ∈ S, 8 := by simp
        _ ≤ ∑ z ∈ S,
            (directCount G S z + directCount G C.P z + U.card) := by
          apply Finset.sum_le_sum
          intro z hz
          exact hPointwise z hz
        _ = edgeCount G S S + edgeCount G S C.P + S.card * U.card := by
          unfold edgeCount
          simp only [Finset.sum_add_distrib]
          simp [Nat.add_assoc]
    have hResult : S.card * (8 - U.card) ≤
        edgeCount G S S + edgeCount G S C.P := by
      calc
        S.card * (8 - U.card) = S.card * 8 - S.card * U.card :=
          Nat.mul_sub_left_distrib S.card 8 U.card
        _ ≤ (edgeCount G S S + edgeCount G S C.P + S.card * U.card) -
            S.card * U.card := Nat.sub_le_sub_right hSum _
        _ = edgeCount G S S + edgeCount G S C.P := by omega
    simpa [S, U] using hResult

theorem row_missing_le_total_missing_four (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (p : V) (hpP : p ∈ C.P) :
    4 - (directZNeighbors G C p).card ≤
      28 - edgeCount G C.P C.Z := by
  have hOther : ∑ q ∈ C.P.erase p, directCount G C.Z q ≤ 24 := by
    calc
      ∑ q ∈ C.P.erase p, directCount G C.Z q ≤
          ∑ _q ∈ C.P.erase p, 4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      _ = 24 := by simp [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit := Finset.sum_erase_add C.P (fun q => directCount G C.Z q) hpP
  have hBound : edgeCount G C.P C.Z ≤
      24 + directCount G C.Z p := by
    unfold edgeCount
    omega
  have hTotal : edgeCount G C.P C.Z ≤ 28 := by
    exact (edgeCount_le_card_mul_card G C.P C.Z).trans_eq (by rw [hPCard, hZCard])
  rw [card_directZNeighbors G C p]
  omega

theorem directZ_to_P_capacity_four (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 7)
    (hZCard : C.Z.card = 4) (p : V) (hpP : p ∈ C.P) :
    edgeCount G (directZNeighbors G C p) C.P ≤
      (28 - edgeCount G C.P C.Z) -
        (4 - (directZNeighbors G C p).card) := by
  let S := directZNeighbors G C p
  let T := C.Z \ S
  have hS : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = C.Z := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 4 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hZCard]
  have hpT : directCount G T p = 0 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    apply Finset.card_eq_zero.mpr
    ext z
    simp only [Finset.notMem_empty, iff_false]
    intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzT, hpz⟩
    exact (Finset.mem_sdiff.mp hzT).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzT).1, hpz⟩)
  have hPT : edgeCount G C.P T ≤ 6 * T.card := by
    calc
      edgeCount G C.P T ≤ ∑ q ∈ C.P, if q = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqp : q = p
        · subst q
          simp [hpT]
        · simp only [hqp, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 * T.card := by
        rw [← Finset.sum_erase_add C.P
          (fun q => if q = p then 0 else T.card) hpP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ x ∈ C.P.erase p, if x = p then 0 else T.card) =
              ∑ _x ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_neg (Finset.mem_erase.mp hx).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 6 * T.card := by
            rw [Finset.card_erase_of_mem hpP, hPCard]
  have hPZSplit : edgeCount G C.P C.Z =
      edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = 4 := by
    rw [hTCard]
    have hSLe : S.card ≤ 4 := (Finset.card_le_card hS).trans_eq hZCard
    omega
  have hPZUpper := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hPZUpper
  change edgeCount G S C.P ≤
    (28 - edgeCount G C.P C.Z) - (4 - S.card)
  omega

def effectiveLowerNat (m s : Nat) : Nat :=
  if m = 0 then [0, 11, 9, 8, 7].getD s 7
  else if m = 1 then [0, 10, 8, 7, 7].getD s 7
  else if m = 2 then [0, 9, 8, 7, 6].getD s 6
  else if m = 3 then [0, 8, 7, 7, 6].getD s 6
  else if m = 4 then [0, 7, 7, 6, 6].getD s 6
  else if m = 5 then [0, 6, 6, 6, 6].getD s 6
  else if m = 6 then [0, 5, 6, 6, 5].getD s 5
  else if m = 7 then [0, 4, 5, 5, 5].getD s 5
  else if m = 8 then [0, 3, 5, 5, 5].getD s 5
  else if m = 9 then [0, 2, 4, 5, 5].getD s 5
  else [0, 1, 4, 4, 4].getD s 4

private theorem effectiveLowerNat_of_capacity
    (m s u eZ eP : Nat) (hm : m ≤ 10) (hs : s ≤ 4)
    (hFeasible : 4 - s ≤ m)
    (hLower : s * (8 - u) ≤ eZ + eP)
    (hZ : eZ ≤ s.choose 2) (hP : eP ≤ m - (4 - s)) :
    effectiveLowerNat m s ≤ u := by
  by_cases hu : 8 ≤ u
  · interval_cases m <;> interval_cases s <;>
      simp_all [effectiveLowerNat, Nat.choose] <;> omega
  · have hu' : u ≤ 7 := by omega
    interval_cases m <;> interval_cases s <;> interval_cases u <;>
      simp_all [effectiveLowerNat, Nat.choose] <;> omega

theorem individual_effective_lower (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (p : V) (hpP : p ∈ C.P)
    (hm : 28 - edgeCount G C.P C.Z ≤ 10) :
    effectiveLowerNat (28 - edgeCount G C.P C.Z)
        (directZNeighbors G C p).card ≤
      (directZEffectiveUnion G C p).card := by
  let S := directZNeighbors G C p
  let U := directZEffectiveUnion G C p
  let m := 28 - edgeCount G C.P C.Z
  let s := S.card
  have hs : s ≤ 4 := by
    exact (Finset.card_le_card (directZNeighbors_subset_Z G C p)).trans_eq hZCard
  have hLower := directZ_effective_capacity_lower G C hMin p
  have hZ := internal_edgeCount_le_choose_two G S hG
  have hP := directZ_to_P_capacity_four G C hG hPCard hZCard p hpP
  have hFeasible := row_missing_le_total_missing_four G C hPCard hZCard p hpP
  change s * (8 - U.card) ≤
    edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ s.choose 2 at hZ
  change edgeCount G S C.P ≤ m - (4 - s) at hP
  change 4 - s ≤ m at hFeasible
  change m ≤ 10 at hm
  change effectiveLowerNat m s ≤ U.card
  exact effectiveLowerNat_of_capacity m s U.card
    (edgeCount G S S) (edgeCount G S C.P) hm hs hFeasible hLower hZ hP

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective
