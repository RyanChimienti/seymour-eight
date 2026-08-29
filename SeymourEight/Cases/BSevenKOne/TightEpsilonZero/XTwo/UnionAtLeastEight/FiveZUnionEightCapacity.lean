import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGlobalBridge

set_option linter.style.header false

/-!
# Capacity data for the five-`Z`, union-at-least-eight branch

For a vertex `p ∈ P`, these are the direct `Z`-neighbours of `p` and the
union of their outneighbours outside `P ∪ Z`.
-/

namespace SeymourEight.FiveZUnionEightCapacity

open FiveZExactGraphBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def directZNeighbors (C : G.LocalConfiguration) (p : V) : Finset V :=
  C.Z.filter (G.Adj p)

def directZExternalUnion (C : G.LocalConfiguration) (p : V) : Finset V :=
  G.outNeighborFinsetOf (directZNeighbors G C p) \ (C.P ∪ C.Z)

@[simp]
theorem card_directZNeighbors (C : G.LocalConfiguration) (p : V) :
    (directZNeighbors G C p).card = directCount G C.Z p := by
  rfl

theorem directZNeighbors_subset_Z (C : G.LocalConfiguration) (p : V) :
    directZNeighbors G C p ⊆ C.Z :=
  Finset.filter_subset _ _

theorem directZExternalUnion_subset_externalUnion
    (C : G.LocalConfiguration) (p : V) :
    directZExternalUnion G C p ⊆ zExternalUnion G C := by
  intro v hv
  rcases Finset.mem_sdiff.mp hv with ⟨hvReached, hvOutside⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, hvOutside⟩
  obtain ⟨z, hzS, hzv⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached
  exact (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
    ⟨z, directZNeighbors_subset_Z G C p hzS, hzv⟩

theorem external_neighbor_mem_directUnion (C : G.LocalConfiguration)
    (p z v : V) (hzS : z ∈ directZNeighbors G C p)
    (hvW : v ∈ zExternalUnion G C) (hzv : G.Adj z v) :
    v ∈ directZExternalUnion G C p := by
  rcases Finset.mem_sdiff.mp hvW with ⟨_hvReached, hvOutside⟩
  apply Finset.mem_sdiff.mpr
  exact ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr
    ⟨z, hzS, hzv⟩, hvOutside⟩

theorem directCount_external_eq_directUnion (C : G.LocalConfiguration)
    (p z : V) (hzS : z ∈ directZNeighbors G C p) :
    directCount G (zExternalUnion G C) z =
      directCount G (directZExternalUnion G C p) z := by
  unfold directCount CertificateBridge.internalFirstNeighbors
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hvW, hzv⟩
    exact ⟨external_neighbor_mem_directUnion G C p z v hzS hvW hzv, hzv⟩
  · rintro ⟨hvU, hzv⟩
    exact ⟨directZExternalUnion_subset_externalUnion G C p hvU, hzv⟩

theorem directCount_external_le_unionCard (C : G.LocalConfiguration)
    (p z : V) (hzS : z ∈ directZNeighbors G C p) :
    directCount G (zExternalUnion G C) z ≤
      (directZExternalUnion G C p).card := by
  rw [directCount_external_eq_directUnion G C p z hzS]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Summing minimum degree over the direct `Z`-neighbours of `p`: after
paying for their common external union, the remaining arcs must enter
`Z ∪ P`. -/
theorem directZ_capacity_lower (C : G.LocalConfiguration)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (p : V) :
    (directZNeighbors G C p).card *
        (8 - (directZExternalUnion G C p).card) ≤
      edgeCount G (directZNeighbors G C p) C.Z +
        edgeCount G (directZNeighbors G C p) C.P := by
  let S := directZNeighbors G C p
  let U := directZExternalUnion G C p
  by_cases hLarge : 8 ≤ U.card
  · have hZero : 8 - (directZExternalUnion G C p).card = 0 := by
      apply Nat.sub_eq_zero_of_le
      simpa [U] using hLarge
    rw [hZero]
    simp
  · have hPointwise : ∀ z ∈ S,
        8 ≤ directCount G C.Z z + directCount G C.P z + U.card := by
      intro z hzS
      have hDegree := FiveZExactGraphBridge.z_outdegree_eq_retainedCounts
        G C z (directZNeighbors_subset_Z G C p hzS)
      have hExternal := directCount_external_le_unionCard G C p z hzS
      change directCount G (zExternalUnion G C) z ≤ U.card at hExternal
      have hzMin := hMin z
      omega
    have hSum : S.card * 8 ≤
        edgeCount G S C.Z + edgeCount G S C.P + S.card * U.card := by
      calc
        S.card * 8 = ∑ _z ∈ S, 8 := by simp
        _ ≤ ∑ z ∈ S,
            (directCount G C.Z z + directCount G C.P z + U.card) := by
          apply Finset.sum_le_sum
          intro z hz
          exact hPointwise z hz
        _ = edgeCount G S C.Z + edgeCount G S C.P + S.card * U.card := by
          unfold edgeCount
          simp only [Finset.sum_add_distrib]
          simp [Nat.add_assoc]
    have hResult : S.card * (8 - U.card) ≤
        edgeCount G S C.Z + edgeCount G S C.P := by
      calc
        S.card * (8 - U.card) = S.card * 8 - S.card * U.card := by
          exact Nat.mul_sub_left_distrib S.card 8 U.card
        _ ≤ (edgeCount G S C.Z + edgeCount G S C.P +
            S.card * U.card) - S.card * U.card :=
          Nat.sub_le_sub_right hSum _
        _ = edgeCount G S C.Z + edgeCount G S C.P := by omega
    simpa [S, U] using hResult

/-- Arcs from the direct `Z`-neighbours back into `Z` split into internal
arcs and arcs to the missed part of `Z`. -/
theorem directZ_to_Z_capacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hZCard : C.Z.card = 5) (p : V) :
    edgeCount G (directZNeighbors G C p) C.Z ≤
      (directZNeighbors G C p).card.choose 2 +
        (directZNeighbors G C p).card *
          (5 - (directZNeighbors G C p).card) := by
  let S := directZNeighbors G C p
  let T := C.Z \ S
  have hS : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp hvT).2 hvS
  have hUnion : S ∪ T = C.Z := by
    exact Finset.union_sdiff_of_subset hS
  have hSplit : edgeCount G S C.Z = edgeCount G S S + edgeCount G S T := by
    rw [← hUnion, edgeCount_union_of_disjoint G S S T hST]
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hCross := edgeCount_le_card_mul_card G S T
  have hTCard : T.card = 5 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hZCard]
  calc
    edgeCount G (directZNeighbors G C p) C.Z =
        edgeCount G S S + edgeCount G S T := hSplit
    _ ≤ S.card.choose 2 + S.card * T.card :=
      Nat.add_le_add hInternal hCross
    _ = (directZNeighbors G C p).card.choose 2 +
        (directZNeighbors G C p).card *
          (5 - (directZNeighbors G C p).card) := by
      rw [hTCard]

/-- Only missing `P → Z` incidences can support reverse arcs from a direct
`Z`-neighbour of `p` into `P`; the `Z` vertices missed by `p` already consume
that many missing incidences outside the direct-neighbour set. -/
theorem directZ_to_P_capacity (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 7)
    (hZCard : C.Z.card = 5) (p : V) (hpP : p ∈ C.P) :
    edgeCount G (directZNeighbors G C p) C.P ≤
      (35 - edgeCount G C.P C.Z) -
        (5 - (directZNeighbors G C p).card) := by
  let S := directZNeighbors G C p
  let T := C.Z \ S
  have hS : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp hvT).2 hvS
  have hUnion : S ∪ T = C.Z := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 5 - S.card := by
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
      edgeCount G C.P T ≤
          ∑ q ∈ C.P, if q = p then 0 else T.card := by
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
          (fun q ↦ if q = p then 0 else T.card) hpP]
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
  have hSCard : S.card + T.card = 5 := by
    rw [hTCard]
    have hSLe : S.card ≤ 5 := (Finset.card_le_card hS).trans_eq hZCard
    omega
  have hPZUpper := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hPZUpper
  change edgeCount G S C.P ≤
    (35 - edgeCount G C.P C.Z) - (5 - S.card)
  omega

/-- The incidences from `p` to the part of `Z` that it misses are among the
globally missing `P → Z` incidences.  This elementary row bound is kept
separate because truncated subtraction makes it awkward to recover from the
reverse-edge capacity inequality alone. -/
theorem directZ_row_missing_le_total (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (p : V) (hpP : p ∈ C.P) :
    5 - (directZNeighbors G C p).card ≤
      35 - edgeCount G C.P C.Z := by
  let S := directZNeighbors G C p
  have hpRow : directCount G C.Z p = S.card := by rfl
  have hOtherRows :
      ∑ q ∈ C.P.erase p, directCount G C.Z q ≤ 6 * 5 := by
    calc
      ∑ q ∈ C.P.erase p, directCount G C.Z q ≤
          ∑ _q ∈ C.P.erase p, C.Z.card := by
        apply Finset.sum_le_sum
        intro q hq
        exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = (C.P.erase p).card * C.Z.card := by simp
      _ = 6 * 5 := by
        rw [Finset.card_erase_of_mem hpP, hPCard, hZCard]
  have hSplit : edgeCount G C.P C.Z =
      directCount G C.Z p +
        ∑ q ∈ C.P.erase p, directCount G C.Z q := by
    unfold edgeCount
    rw [← Finset.sum_erase_add C.P (directCount G C.Z) hpP]
    omega
  have hEdgeUpper : edgeCount G C.P C.Z ≤ S.card + 30 := by
    rw [hSplit, hpRow]
    omega
  have hEdgeAbsolute := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hEdgeAbsolute
  change 5 - S.card ≤ 35 - edgeCount G C.P C.Z
  omega

/-- The numerical capacity consequences needed by the aggregate certificate.
When a row sees all five vertices of `Z`, its direct external union is the
full union and hence has size at least eight.  A four-neighbour row has at
least five external targets, with the sole size-five possibility consuming
all three globally missing incidences.  Rows with at most three direct
`Z`-neighbours still have at least five external targets. -/
theorem directZ_effective_card_bounds (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hMissing : 35 - edgeCount G C.P C.Z ≤ 3)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (p : V) (hpP : p ∈ C.P) :
    ((directZNeighbors G C p).card = 5 →
        8 ≤ (directZExternalUnion G C p).card) ∧
      ((directZNeighbors G C p).card = 4 →
        5 ≤ (directZExternalUnion G C p).card ∧
          ((directZExternalUnion G C p).card = 5 →
            35 - edgeCount G C.P C.Z = 3)) ∧
      ((directZNeighbors G C p).card ≤ 3 →
        5 ≤ (directZExternalUnion G C p).card) := by
  let S := directZNeighbors G C p
  let U := directZExternalUnion G C p
  let m := 35 - edgeCount G C.P C.Z
  have hSSubset : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hSLe : S.card ≤ 5 := by
    calc
      S.card ≤ C.Z.card := Finset.card_le_card hSSubset
      _ = 5 := hZCard
  have hRowMissing : 5 - S.card ≤ m := by
    simpa [S, m] using directZ_row_missing_le_total G C hPCard hZCard p hpP
  have hLower := directZ_capacity_lower G C hMin p
  have hZUpper := directZ_to_Z_capacity G C hG hZCard p
  have hPUpper := directZ_to_P_capacity G C hG hPCard hZCard p hpP
  change S.card * (8 - U.card) ≤
    edgeCount G S C.Z + edgeCount G S C.P at hLower
  change edgeCount G S C.Z ≤
    S.card.choose 2 + S.card * (5 - S.card) at hZUpper
  change edgeCount G S C.P ≤ m - (5 - S.card) at hPUpper
  have hUpper : edgeCount G S C.Z + edgeCount G S C.P ≤
      (S.card.choose 2 + S.card * (5 - S.card)) +
        (m - (5 - S.card)) := Nat.add_le_add hZUpper hPUpper
  have hm : m ≤ 3 := by simpa [m] using hMissing
  have hSAtLeastTwo : 2 ≤ S.card := by omega
  constructor
  · intro hSFive
    change S.card = 5 at hSFive
    have hSEq : S = C.Z := Finset.eq_of_subset_of_card_le hSSubset (by
      rw [hSFive, hZCard])
    have hUEq : U = zExternalUnion G C := by
      simp [U, S, directZExternalUnion, zExternalUnion, hSEq]
    change 8 ≤ U.card
    simpa [hUEq] using hFullUnion
  constructor
  · intro hSFour
    change S.card = 4 at hSFour
    have hFive : 5 ≤ U.card := by
      by_contra hNot
      have hULe : U.card ≤ 4 := by omega
      simp [hSFour, Nat.choose] at hLower hUpper
      omega
    change 5 ≤ U.card ∧ (U.card = 5 → m = 3)
    refine ⟨hFive, ?_⟩
    intro hUFive
    simp [hSFour, hUFive, Nat.choose] at hLower hUpper
    omega
  · intro hSThree
    change S.card ≤ 3 at hSThree
    change 5 ≤ U.card
    by_contra hNot
    have hULe : U.card ≤ 4 := by omega
    have hSCases : S.card = 2 ∨ S.card = 3 := by omega
    rcases hSCases with hSTwo | hSThree'
    · simp [hSTwo] at hLower hUpper
      omega
    · simp [hSThree'] at hLower hUpper
      omega

/-- External targets reached through a direct `Z`-neighbour, after removing
the targets already adjacent from `p`, are genuine strict second
outneighbours of `p`. -/
theorem directZExternalStrict_subset_second (C : G.LocalConfiguration)
    (p : V) (hpP : p ∈ C.P) :
    directZExternalUnion G C p \ G.outNeighborFinset p ⊆
      G.secondOutNeighborFinset p := by
  intro v hv
  rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvNotDirect⟩
  rcases Finset.mem_sdiff.mp hvU with ⟨hvReached, hvOutside⟩
  obtain ⟨z, hzS, hzv⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReached
  have hpz : G.Adj p z := (Finset.mem_filter.mp hzS).2
  have hpv : ¬G.Adj p v := by
    simpa only [Digraph.mem_outNeighborFinset] using hvNotDirect
  have hvp : v ≠ p := by
    intro hEq
    subst v
    exact hvOutside (Finset.mem_union_left _ hpP)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨z, hpz, hzv⟩, hpv, hvp⟩

/-- A target in the direct external union which is also a direct neighbour
of `p` must lie in `H`.  The other captured pieces are excluded by the
definition of the union and by `epsilon_s = 0`. -/
theorem directZExternal_direct_subset_H (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (p : V) (hpP : p ∈ C.P) :
    directZExternalUnion G C p ∩ G.outNeighborFinset p ⊆
      C.H.filter (G.Adj p) := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvU, hvDirect⟩
  have hpv : G.Adj p v := by
    simpa only [Digraph.mem_outNeighborFinset] using hvDirect
  have hvCaptured := outgoingCaptured_of_p_eq_B G C hG hPB p hpP hvDirect
  have hvOutside := (Finset.mem_sdiff.mp hvU).2
  simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
  apply Finset.mem_filter.mpr
  refine ⟨?_, hpv⟩
  rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
  · exact (hvOutside (Finset.mem_union_right _ hvZ)).elim
  · have hps : G.Adj p C.s := by simpa [hvs] using hpv
    exact (FiveZExactPBridge.no_P_to_s_of_epsilonS_zero G C hEpsilon
      p hpP hps).elim
  · exact hvH
  · exact (hvOutside (Finset.mem_union_left _ hvP)).elim

/-- The direct external union contributes all but at most the direct
`H`-neighbours to the strict second neighbourhood. -/
theorem directZExternal_card_le_second_add_H (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (p : V) (hpP : p ∈ C.P) :
    (directZExternalUnion G C p).card ≤
      G.secondOutdegree p + directCount G C.H p := by
  let U := directZExternalUnion G C p
  let N := G.outNeighborFinset p
  have hStrict : U \ N ⊆ G.secondOutNeighborFinset p := by
    simpa [U, N] using directZExternalStrict_subset_second G C p hpP
  have hDirect : U ∩ N ⊆ C.H.filter (G.Adj p) := by
    simpa [U, N] using directZExternal_direct_subset_H G C hG hPB
      hEpsilon p hpP
  have hSplit := Finset.card_sdiff_add_card_inter U N
  unfold Digraph.secondOutdegree directCount
    CertificateBridge.internalFirstNeighbors
  calc
    U.card = (U \ N).card + (U ∩ N).card := hSplit.symm
    _ ≤ (G.secondOutNeighborFinset p).card +
        (C.H.filter (G.Adj p)).card :=
      Nat.add_le_add (Finset.card_le_card hStrict)
        (Finset.card_le_card hDirect)

/-- The preceding bound remains valid after simultaneously counting all
strict second neighbours lying in `P`, because `P` is disjoint from the
external union. -/
theorem PSecond_add_directZExternal_card_le_second_add_H
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (p : V) (hpP : p ∈ C.P) :
    (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset p).card +
        (directZExternalUnion G C p).card ≤
      G.secondOutdegree p + directCount G C.H p := by
  let U := directZExternalUnion G C p
  let N := G.outNeighborFinset p
  let PS := C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset p
  let Strict := U \ N
  let Direct := U ∩ N
  have hStrict : Strict ⊆ G.secondOutNeighborFinset p := by
    simpa [Strict, U, N] using
      directZExternalStrict_subset_second G C p hpP
  have hPS : PS ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hDisjoint : Disjoint PS Strict := by
    rw [Finset.disjoint_left]
    intro v hvPS hvStrict
    have hvP := (Finset.mem_filter.mp hvPS).1
    have hvU := (Finset.mem_sdiff.mp hvStrict).1
    exact (Finset.mem_sdiff.mp hvU).2 (Finset.mem_union_left _ hvP)
  have hSecondUnion : PS ∪ Strict ⊆ G.secondOutNeighborFinset p :=
    Finset.union_subset hPS hStrict
  have hSecondCard : PS.card + Strict.card ≤ G.secondOutdegree p := by
    change PS.card + Strict.card ≤ (G.secondOutNeighborFinset p).card
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hSecondUnion
  have hDirect : Direct ⊆ C.H.filter (G.Adj p) := by
    simpa [Direct, U, N] using
      directZExternal_direct_subset_H G C hG hPB hEpsilon p hpP
  have hDirectCard : Direct.card ≤ directCount G C.H p := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    exact Finset.card_le_card hDirect
  have hSplit := Finset.card_sdiff_add_card_inter U N
  change Strict.card + Direct.card = U.card at hSplit
  change PS.card + U.card ≤ G.secondOutdegree p + directCount G C.H p
  omega

/-- In the unique numerical equality left by a four-neighbour row, some
direct `Z`-neighbour must point to the one missed vertex of `Z`.  That missed
vertex is a strict second neighbour outside the external union. -/
theorem directZ_four_five_exception_second (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hMissing : 35 - edgeCount G C.P C.Z = 3)
    (p : V) (hpP : p ∈ C.P)
    (hSCard : (directZNeighbors G C p).card = 4)
    (hUCard : (directZExternalUnion G C p).card = 5) :
    ∃ t ∈ C.Z \ directZNeighbors G C p,
      t ∈ G.secondOutNeighborFinset p ∧
        t ∉ directZExternalUnion G C p := by
  let S := directZNeighbors G C p
  let T := C.Z \ S
  let U := directZExternalUnion G C p
  have hSSubset : S ⊆ C.Z := directZNeighbors_subset_Z G C p
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp hvT).2 hvS
  have hUnion : S ∪ T = C.Z := Finset.union_sdiff_of_subset hSSubset
  have hArc : ∃ z ∈ S, ∃ t ∈ T, G.Adj z t := by
    by_contra hNone
    have hNoArc : ∀ z, z ∈ S → ∀ t, t ∈ T → ¬G.Adj z t := by
      intro z hz t ht hzt
      exact hNone ⟨z, hz, t, ht, hzt⟩
    have hSTZero : edgeCount G S T = 0 := by
      unfold edgeCount
      apply Finset.sum_eq_zero
      intro z hz
      unfold directCount CertificateBridge.internalFirstNeighbors
      apply Finset.card_eq_zero.mpr
      ext t
      simp only [Finset.notMem_empty, iff_false]
      intro ht
      rcases Finset.mem_filter.mp ht with ⟨htT, hzt⟩
      exact hNoArc z hz t htT hzt
    have hSplit : edgeCount G S C.Z =
        edgeCount G S S + edgeCount G S T := by
      rw [← hUnion, edgeCount_union_of_disjoint G S S T hST]
    have hInternal := internal_edgeCount_le_choose_two G S hG
    have hZUpper : edgeCount G S C.Z ≤ 6 := by
      rw [hSplit, hSTZero, Nat.add_zero]
      simpa [S, hSCard, Nat.choose] using hInternal
    have hPUpper := directZ_to_P_capacity G C hG hPCard hZCard p hpP
    have hPUpper' : edgeCount G S C.P ≤ 2 := by
      simpa [S, hSCard, hMissing] using hPUpper
    have hLower := directZ_capacity_lower G C hMin p
    have hLower' : 12 ≤ edgeCount G S C.Z + edgeCount G S C.P := by
      simpa [S, U, hSCard, hUCard] using hLower
    omega
  obtain ⟨z, hzS, t, htT, hzt⟩ := hArc
  refine ⟨t, by simpa [T, S] using htT, ?_, ?_⟩
  · have hpz : G.Adj p z := (Finset.mem_filter.mp hzS).2
    have htZ : t ∈ C.Z := (Finset.mem_sdiff.mp htT).1
    have htNotS : t ∉ S := (Finset.mem_sdiff.mp htT).2
    have hpt : ¬G.Adj p t := by
      intro hpt
      exact htNotS (Finset.mem_filter.mpr ⟨htZ, hpt⟩)
    have htp : t ≠ p := by
      intro hEq
      subst t
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) htZ hpP
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨z, hpz, hzt⟩, hpt, htp⟩
  · intro htU
    have htOutside := (Finset.mem_sdiff.mp htU).2
    exact htOutside (Finset.mem_union_right _
      (Finset.mem_sdiff.mp htT).1)

/-- The graph-theoretic capacity package in exactly the form consumed by
`fiveZExternalLower`: the guaranteed contribution is bounded by the true
strict second degree plus the direct `H` overlap allowance. -/
theorem fiveZExternalLower_nat_le_second_add_H (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hMissing : 35 - edgeCount G C.P C.Z ≤ 3)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (p : V) (hpP : p ∈ C.P) :
    (C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset p).card +
      (if directCount G C.Z p = 5 then 8
      else if directCount G C.Z p = 4 then 6 else 5) ≤
      G.secondOutdegree p + directCount G C.H p := by
  let S := directZNeighbors G C p
  let U := directZExternalUnion G C p
  have hSCard : S.card = directCount G C.Z p := rfl
  have hSLe : S.card ≤ 5 := by
    calc
      S.card ≤ C.Z.card := Finset.card_le_card
        (directZNeighbors_subset_Z G C p)
      _ = 5 := hZCard
  have hBounds := directZ_effective_card_bounds G C hG hMin hPCard
    hZCard hMissing hFullUnion p hpP
  let PS := C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset p
  have hUBase := PSecond_add_directZExternal_card_le_second_add_H G C
    hG hPB hEpsilon p hpP
  change PS.card + U.card ≤
    G.secondOutdegree p + directCount G C.H p at hUBase
  by_cases hFive : directCount G C.Z p = 5
  · simp only [hFive, ↓reduceIte]
    have hUFive : 8 ≤ U.card := hBounds.1 (by simpa [S, hSCard])
    change PS.card + 8 ≤ G.secondOutdegree p + directCount G C.H p
    omega
  · by_cases hFour : directCount G C.Z p = 4
    · simp only [hFour, ↓reduceIte]
      have hSFour : S.card = 4 := by simpa [hSCard] using hFour
      have hFourBounds := hBounds.2.1 hSFour
      have hUAtLeastFive : 5 ≤ U.card := by
        simpa [U] using hFourBounds.1
      by_cases hUSix : 6 ≤ U.card
      · change PS.card + 6 ≤
          G.secondOutdegree p + directCount G C.H p
        omega
      · have hUFive : U.card = 5 := by omega
        have hmThree : 35 - edgeCount G C.P C.Z = 3 :=
          hFourBounds.2 (by simpa [U] using hUFive)
        obtain ⟨t, htT, htSecond, htNotU⟩ :=
          directZ_four_five_exception_second G C hG hMin hPCard hZCard
            hmThree p hpP hSFour (by simpa [U] using hUFive)
        let N := G.outNeighborFinset p
        let Strict := U \ N
        let Direct := U ∩ N
        have hPSSubset : PS ⊆ G.secondOutNeighborFinset p := by
          intro v hv
          exact (Finset.mem_filter.mp hv).2
        have hStrictSubset : Strict ⊆ G.secondOutNeighborFinset p := by
          simpa [Strict, U, N] using
            directZExternalStrict_subset_second G C p hpP
        have hDirectSubset : Direct ⊆ C.H.filter (G.Adj p) := by
          simpa [Direct, U, N] using
            directZExternal_direct_subset_H G C hG hPB hEpsilon p hpP
        have htNotStrict : t ∉ Strict := by
          intro ht
          exact htNotU (Finset.mem_sdiff.mp ht).1
        have hPSStrictDisjoint : Disjoint PS Strict := by
          rw [Finset.disjoint_left]
          intro v hvPS hvStrict
          have hvP := (Finset.mem_filter.mp hvPS).1
          have hvU := (Finset.mem_sdiff.mp hvStrict).1
          exact (Finset.mem_sdiff.mp hvU).2 (Finset.mem_union_left _ hvP)
        have htNotPS : t ∉ PS := by
          intro htPS
          have htP := (Finset.mem_filter.mp htPS).1
          have htZ := (Finset.mem_sdiff.mp htT).1
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) htZ htP
        have htNotPSStrict : t ∉ PS ∪ Strict := by simp [htNotPS, htNotStrict]
        have hStrictPlus : (PS ∪ Strict) ∪ {t} ⊆
            G.secondOutNeighborFinset p := by
          intro v hv
          rcases Finset.mem_union.mp hv with hvPSStrict | hvt
          · rcases Finset.mem_union.mp hvPSStrict with hvPS | hvStrict
            · exact hPSSubset hvPS
            · exact hStrictSubset hvStrict
          · have hvtEq : v = t := Finset.mem_singleton.mp hvt
            simpa [hvtEq] using htSecond
        have hStrictCard : PS.card + Strict.card + 1 ≤
            G.secondOutdegree p := by
          change PS.card + Strict.card + 1 ≤
            (G.secondOutNeighborFinset p).card
          have hDisjointT : Disjoint (PS ∪ Strict) {t} := by
            rw [Finset.disjoint_singleton_right]
            exact htNotPSStrict
          calc
            PS.card + Strict.card + 1 = ((PS ∪ Strict) ∪ {t}).card := by
              rw [Finset.card_union_of_disjoint hDisjointT,
                Finset.card_union_of_disjoint hPSStrictDisjoint]
              simp
            _ ≤ (G.secondOutNeighborFinset p).card :=
              Finset.card_le_card hStrictPlus
        have hDirectCard : Direct.card ≤ directCount G C.H p := by
          unfold directCount CertificateBridge.internalFirstNeighbors
          exact Finset.card_le_card hDirectSubset
        have hSplit := Finset.card_sdiff_add_card_inter U N
        change Strict.card + Direct.card = U.card at hSplit
        change PS.card + 6 ≤
          G.secondOutdegree p + directCount G C.H p
        omega
    · simp only [hFive, hFour, ↓reduceIte]
      have hSThree : S.card ≤ 3 := by
        rw [hSCard]
        omega
      have hUFive : 5 ≤ U.card := hBounds.2.2 hSThree
      change PS.card + 5 ≤ G.secondOutdegree p + directCount G C.H p
      omega

end SeymourEight.FiveZUnionEightCapacity
