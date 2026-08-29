import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreBridge
import SeymourEight.Cases.BSevenKOne.Basic
import SeymourEight.Shared.FinsetBridge

set_option linter.style.header false

/-!
# Graph bridge for the exact five-`Z` certificate

This file builds the graph-facing half of the exact five-`Z` certificate.
The first vertical slice proves that the certificate's retained degree for a
labelled `Z` vertex is its actual graph outdegree.  In particular, this checks
that the exact external union contains every otherwise-unrepresented
outneighbor and that the three retained target classes are disjoint.
-/

namespace SeymourEight.FiveZExactGraphBridge

open FiveZExactRisk FiveZExactCoreBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The complete union of `Z`-outneighbors lying outside `P ∪ Z`. -/
def zExternalUnion (C : G.LocalConfiguration) : Finset V :=
  G.outNeighborFinsetOf C.Z \ (C.P ∪ C.Z)

theorem disjoint_Z_zExternalUnion (C : G.LocalConfiguration) :
    Disjoint C.Z (zExternalUnion G C) := by
  rw [Finset.disjoint_left]
  intro v hvZ hvW
  exact (Finset.mem_sdiff.mp hvW).2 (Finset.mem_union_right C.P hvZ)

theorem disjoint_P_zExternalUnion (C : G.LocalConfiguration) :
    Disjoint C.P (zExternalUnion G C) := by
  rw [Finset.disjoint_left]
  intro v hvP hvW
  exact (Finset.mem_sdiff.mp hvW).2 (Finset.mem_union_left C.Z hvP)

theorem z_outgoingCaptured (C : G.LocalConfiguration) (z : V) (hz : z ∈ C.Z) :
    G.outNeighborFinset z ⊆ C.Z ∪ zExternalUnion G C ∪ C.P := by
  intro v hzv
  by_cases hvP : v ∈ C.P
  · exact Finset.mem_union_right _ hvP
  by_cases hvZ : v ∈ C.Z
  · exact Finset.mem_union_left C.P (Finset.mem_union_left _ hvZ)
  have hvW : v ∈ zExternalUnion G C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, by simp [hvP, hvZ]⟩
    apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
    exact ⟨z, hz, (Digraph.mem_outNeighborFinset (G := G)).mp hzv⟩
  exact Finset.mem_union_left C.P (Finset.mem_union_right C.Z hvW)

/-- Every actual outneighbor of `z ∈ Z` occurs in exactly one retained block. -/
theorem z_outdegree_eq_retainedCounts (C : G.LocalConfiguration)
    (z : V) (hz : z ∈ C.Z) :
    G.outdegree z = directCount G C.Z z +
      directCount G (zExternalUnion G C) z + directCount G C.P z := by
  have hEq : G.outNeighborFinset z =
      (C.Z ∪ zExternalUnion G C ∪ C.P).filter fun v ↦ G.Adj z v := by
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro hzv
      exact ⟨by
        simpa only [Finset.mem_union] using
          z_outgoingCaptured G C z hz
            ((Digraph.mem_outNeighborFinset (G := G)).mpr hzv), hzv⟩
    · exact fun hv ↦ hv.2
  have hZWP : Disjoint (C.Z ∪ zExternalUnion G C) C.P := by
    rw [Finset.disjoint_left]
    intro v hvZW hvP
    rcases Finset.mem_union.mp hvZW with hvZ | hvW
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C)) hvP hvW
  have hZWFilter :
      Disjoint (C.Z.filter fun v ↦ G.Adj z v)
        ((zExternalUnion G C).filter fun v ↦ G.Adj z v) :=
    Finset.disjoint_filter_filter (p := fun v ↦ G.Adj z v)
      (q := fun v ↦ G.Adj z v) (disjoint_Z_zExternalUnion G C)
  have hZWPFilter :
      Disjoint
        ((C.Z.filter fun v ↦ G.Adj z v) ∪
          ((zExternalUnion G C).filter fun v ↦ G.Adj z v))
        (C.P.filter fun v ↦ G.Adj z v) := by
    rw [Finset.disjoint_left]
    intro v hvZW hvP
    apply (Finset.disjoint_left.mp hZWP) ?_ (Finset.mem_filter.mp hvP).1
    rcases Finset.mem_union.mp hvZW with hvZ | hvW
    · exact Finset.mem_union_left _ (Finset.mem_filter.mp hvZ).1
    · exact Finset.mem_union_right _ (Finset.mem_filter.mp hvW).1
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  rw [hEq, Finset.filter_union, Finset.filter_union,
    Finset.card_union_of_disjoint hZWPFilter,
    Finset.card_union_of_disjoint hZWFilter]

/-! ## Converting the certificate byte counts to finset counts -/

/-- A `count` of fewer than 256 Booleans does not overflow its byte. -/
theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat =
      ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hSumLe :
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [count, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      have hLt0 :
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) < 256 := by
        omega
      have hLt1 :
          (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) + 1 < 256 := by
        omega
      have hLt0' :
          (∑ i ∈ Finset.range n,
            (if f i then (1 : BitVec 8) else 0).toNat) < 256 := by
        simpa [bitCount] using hLt0
      have hLt1' :
          (∑ i ∈ Finset.range n,
            (if f i then (1 : BitVec 8) else 0).toNat) + 1 < 256 := by
        simpa [bitCount] using hLt1
      cases hfn : f n
      · simp only [bitCount]
        exact Nat.mod_eq_of_lt hLt0'
      · simp only [bitCount]
        exact Nat.mod_eq_of_lt hLt1'

theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat = ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i ↦ (bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [bitCount]

theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [any]
  | succ n ih =>
      simp only [any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hLast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hLast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · have : i = n := by omega
          exact Or.inr (this ▸ hfi)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (count n b).toNat ≤ (S.filter Q).card := by
  rw [toNat_count_eq_fin_sum n b hn,
    filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · have hQ := hGood j hb
    simp [hb, hQ]
  · have hFalse := Bool.eq_false_of_not_eq_true hb
    simp [hFalse]

theorem zArcCount_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 5) :
    (count 5 (zArc (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) i)).toNat =
      directCount G C.Z (z ⟨i, hi⟩).1 := by
  rw [toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.Z z
  intro j
  rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a i j hi j.isLt]
  simp

theorem zToWCount_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 5) :
    (count 6 (zToW (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) i)).toNat =
      directCount G (zExternalUnion G C) (z ⟨i, hi⟩).1 := by
  rw [toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (zExternalUnion G C) w
  intro j
  rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a i j hi j.isLt]
  simp

theorem zToPCount_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 5) :
    (zPOut (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) i).toNat =
      directCount G C.P (z ⟨i, hi⟩).1 := by
  rw [zPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a i j hi j.isLt]
  simp

/-- The byte-valued retained degree in the finite core is the exact graph degree. -/
theorem zDegree_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 5) :
    (zDegree (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) i).toNat =
      G.outdegree (z ⟨i, hi⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  have hZ := zArcCount_toNat G C p z w h a i hi
  have hW := zToWCount_toNat G C p z w h a i hi
  have hP := zToPCount_toNat G C p z w h a i hi
  have hZLe : directCount G C.Z (z ⟨i, hi⟩).1 ≤ 5 := by
    calc
      directCount G C.Z (z ⟨i, hi⟩).1 ≤ C.Z.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hWLe : directCount G (zExternalUnion G C) (z ⟨i, hi⟩).1 ≤ 6 := by
    calc
      directCount G (zExternalUnion G C) (z ⟨i, hi⟩).1 ≤
          (zExternalUnion G C).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by simpa using (Fintype.card_congr w).symm
  have hPLe : directCount G C.P (z ⟨i, hi⟩).1 ≤ 7 := by
    calc
      directCount G C.P (z ⟨i, hi⟩).1 ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  rw [zDegree, BitVec.toNat_add, BitVec.toNat_add, hZ, hW, hP,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact (z_outdegree_eq_retainedCounts G C
    (z ⟨i, hi⟩).1 (z ⟨i, hi⟩).2).symm

/-! ## Soundness of the represented strict second neighbors of `Z` -/

/-- A certificate target in `Z` is an actual strict second neighbor. -/
theorem secondZFromZ_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 5) (ht : target < 5)
    (hSecond : secondZFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source target = true) :
    (z ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  simp only [secondZFromZ, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hReach⟩, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (z ⟨target, ht⟩).1 := by
    rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (z ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 5) = ⟨source, hs⟩ := by
      apply z.injective
      exact Subtype.ext hEq
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (z ⟨target, ht⟩).1 := by
    simp only [reachesZFromZ, Bool.or_eq_true] at hReach
    rcases hReach with hViaZ | hViaP
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 5 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (z ⟨target, ht⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (z ⟨target, ht⟩).1 := by
        rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

/-- The internal-`Z` summand never exceeds the actual strict second degree. -/
theorem secondZFromZCount_toNat_le_secondOutdegree
    (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (source : Nat) (hs : source < 5) :
    (count 5 (secondZFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source)).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  rw [toNat_count_eq_fin_sum 5 _ (by omega)]
  unfold Digraph.secondOutdegree
  calc
    (∑ j : Fin 5, if secondZFromZ
        (coreBits G.Adj (fun k ↦ (p k).1) h (fun k ↦ (z k).1)
          (fun k ↦ (w k).1) a) source j then 1 else 0) ≤
        ∑ j : Fin 5,
          if (z j).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1
          then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hBit : secondZFromZ
          (coreBits G.Adj (fun k ↦ (p k).1) h (fun k ↦ (z k).1)
            (fun k ↦ (w k).1) a) source j = true
      · have hMem := secondZFromZ_true_mem G C p z w h a
          source j hs j.isLt hBit
        simp [hBit, hMem]
      · have hFalse := Bool.eq_false_of_not_eq_true hBit
        simp [hFalse]
    _ = (C.Z.filter fun v ↦
          v ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      symm
      apply filterCard_eq_sum_fin C.Z z
    _ ≤ (G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).2

/-- A represented target in the exact external union is an actual strict
second neighbor.  The equality at label zero is precisely the overlap datum
`W[0] = H[0]` used by the finite core. -/
theorem secondWFromZ_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V)
    (hW0 : (w 0).1 = h 0)
    (source target : Nat) (hs : source < 5) (ht : target < 6)
    (hSecond : secondWFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source target = true) :
    (w ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  simp only [secondWFromZ, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (w ⟨target, ht⟩).1 := by
    rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (w ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
      (z ⟨source, hs⟩).2 (hEq ▸ (w ⟨target, ht⟩).2)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (w ⟨target, ht⟩).1 := by
    simp only [reachesWFromZ, Bool.or_eq_true] at hReach
    rcases hReach with hViaZ | hViaP
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 5 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmSource, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (w ⟨target, ht⟩).1 := by
        rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨hTargetZero, hAny⟩
      obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 7 _).mp hAny
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecondH : G.Adj (p ⟨middle, hm⟩).1 (h 0) := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle 0 hm (by omega)] at hSecondBool
        exact of_decide_eq_true hSecondBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (w ⟨target, ht⟩).1 := by
        subst target
        simpa [hW0] using hSecondH
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondWFromZCount_toNat_le_secondOutdegree
    (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (hW0 : (w 0).1 = h 0)
    (source : Nat) (hs : source < 5) :
    (count 6 (secondWFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source)).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  rw [toNat_count_eq_fin_sum 6 _ (by omega)]
  unfold Digraph.secondOutdegree
  calc
    (∑ j : Fin 6, if secondWFromZ
        (coreBits G.Adj (fun k ↦ (p k).1) h (fun k ↦ (z k).1)
          (fun k ↦ (w k).1) a) source j then 1 else 0) ≤
        ∑ j : Fin 6,
          if (w j).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1
          then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hBit : secondWFromZ
          (coreBits G.Adj (fun k ↦ (p k).1) h (fun k ↦ (z k).1)
            (fun k ↦ (w k).1) a) source j = true
      · have hMem := secondWFromZ_true_mem G C p z w h a hW0
          source j hs j.isLt hBit
        simp [hBit, hMem]
      · have hFalse := Bool.eq_false_of_not_eq_true hBit
        simp [hFalse]
    _ = ((zExternalUnion G C).filter fun v ↦
          v ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      symm
      apply filterCard_eq_sum_fin (zExternalUnion G C) w
    _ ≤ (G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).2

/-- A represented `P` target is an actual strict second neighbor of `Z`. -/
theorem secondPFromZ_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V)
    (hW0 : (w 0).1 = h 0)
    (source target : Nat) (hs : source < 5) (ht : target < 7)
    (hSecond : secondPFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source target = true) :
    (p ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  simp only [secondPFromZ, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
      (z ⟨source, hs⟩).2 (hEq ▸ (p ⟨target, ht⟩).2)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [reachesPFromZ, Bool.or_eq_true] at hReach
    rcases hReach with (hViaH | hViaP) | hViaZ
    · simp only [Bool.and_eq_true] at hViaH
      rcases hViaH with ⟨hFirstBool, hSecondBool⟩
      have hFirstW : G.Adj (z ⟨source, hs⟩).1 (w 0).1 := by
        rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source 0 hs (by omega)] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (h 0) := by
        simpa [hW0] using hFirstW
      have hSecond' : G.Adj (h 0) (p ⟨target, ht⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          0 target (by omega) ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨h 0, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmTarget, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ :=
        (any_eq_true_iff 5 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmSource, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (p ⟨target, ht⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
          middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondPFromZCount_toNat_le_secondOutdegree
    (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 → V) (a : Fin 8 → V) (hW0 : (w 0).1 = h 0)
    (source : Nat) (hs : source < 5) :
    (count 7 (secondPFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source)).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  rw [toNat_count_eq_fin_sum 7 _ (by omega)]
  unfold Digraph.secondOutdegree
  calc
    (∑ j : Fin 7, if secondPFromZ
        (coreBits G.Adj (fun k ↦ (p k).1) h (fun k ↦ (z k).1)
          (fun k ↦ (w k).1) a) source j then 1 else 0) ≤
        ∑ j : Fin 7,
          if (p j).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1
          then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hBit : secondPFromZ
          (coreBits G.Adj (fun k ↦ (p k).1) h (fun k ↦ (z k).1)
            (fun k ↦ (w k).1) a) source j = true
      · have hMem := secondPFromZ_true_mem G C p z w h a hW0
          source j hs j.isLt hBit
        simp [hBit, hMem]
      · have hFalse := Bool.eq_false_of_not_eq_true hBit
        simp [hFalse]
    _ = (C.P.filter fun v ↦
          v ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      symm
      apply filterCard_eq_sum_fin C.P p
    _ ≤ (G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).2

/-- The retained `H \ W` targets are strict second neighbors.  Their lack of
a direct `Z`-arc follows from completeness of `W`, not from an extra Boolean
variable in the finite core. -/
theorem reachesOutsideHFromZ_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (source target : Nat) (hs : source < 5) (ht : target < 3)
    (hReach : reachesOutsideHFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (h ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  simp only [reachesOutsideHFromZ, Bool.and_eq_true,
    decide_eq_true_eq] at hReach
  rcases hReach with ⟨hTargetNe, hAny⟩
  obtain ⟨middle, hm, hPath⟩ :=
    (any_eq_true_iff 7 _).mp hAny
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (z ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
    rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond : G.Adj (p ⟨middle, hm⟩).1 (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (h ⟨target, ht⟩).1 := by
    intro hDirect
    have hNotP : (h ⟨target, ht⟩).1 ∉ C.P := by
      intro hP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (h ⟨target, ht⟩).2 hP
    have hNotZ : (h ⟨target, ht⟩).1 ∉ C.Z := by
      intro hZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
        hZ (h ⟨target, ht⟩).2
    have hTargetW : (h ⟨target, ht⟩).1 ∈ zExternalUnion G C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, by simp [hNotP, hNotZ]⟩
      apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨(z ⟨source, hs⟩).1, (z ⟨source, hs⟩).2, hDirect⟩
    have hIndexZero : (⟨target, ht⟩ : Fin 3) = 0 :=
      (hInW ⟨target, ht⟩).mp hTargetW
    exact hTargetNe (Fin.ext_iff.mp hIndexZero)
  have hTargetVertexNe : (h ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
      (z ⟨source, hs⟩).2 (hEq ▸ (h ⟨target, ht⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨middle, hm⟩).1, hFirst, hSecond⟩,
    hNotArc, hTargetVertexNe⟩

theorem reachesOutsideHFromZCount_toNat_le_secondOutdegree
    (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (source : Nat) (hs : source < 5) :
    (count 3 (reachesOutsideHFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source)).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  rw [toNat_count_eq_fin_sum 3 _ (by omega)]
  unfold Digraph.secondOutdegree
  calc
    (∑ j : Fin 3, if reachesOutsideHFromZ
        (coreBits G.Adj (fun k ↦ (p k).1) (fun k ↦ (h k).1)
          (fun k ↦ (z k).1) (fun k ↦ (w k).1) a) source j then 1 else 0) ≤
        ∑ j : Fin 3,
          if (h j).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1
          then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hBit : reachesOutsideHFromZ
          (coreBits G.Adj (fun k ↦ (p k).1) (fun k ↦ (h k).1)
            (fun k ↦ (z k).1) (fun k ↦ (w k).1) a) source j = true
      · have hMem := reachesOutsideHFromZ_true_mem G C p z w h a hInW
          source j hs j.isLt hBit
        simp [hBit, hMem]
      · have hFalse := Bool.eq_false_of_not_eq_true hBit
        simp [hFalse]
    _ = (C.H.filter fun v ↦
          v ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      symm
      apply filterCard_eq_sum_fin C.H h
    _ ≤ (G.secondOutNeighborFinset (z ⟨source, hs⟩).1).card := by
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).2

/-- The full four-block represented count for a `Z` vertex is bounded by its
actual strict second outdegree.  This is the graph-soundness statement used
to justify `zNonSeymour` in the finite core. -/
theorem zSecondCount_coreBits_toNat_le_secondOutdegree
    (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hW0 : (w 0).1 = (h 0).1)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (source : Nat) (hs : source < 5) :
    (zSecondCount
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (z ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  let QOutside : V → Prop := fun v ↦
    v ∉ zExternalUnion G C ∧ v ∈ G.secondOutNeighborFinset u
  have hZBound : (count 5 (secondZFromZ bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact secondZFromZ_true_mem G C p z w (fun j ↦ (h j).1) a
      source j hs j.isLt hBit
  have hWBound : (count 6 (secondWFromZ bits source)).toNat ≤
      ((zExternalUnion G C).filter Q).card := by
    apply count_le_filterCard (zExternalUnion G C) w _ Q (by omega)
    intro j hBit
    exact secondWFromZ_true_mem G C p z w (fun j ↦ (h j).1) a hW0
      source j hs j.isLt hBit
  have hPBound : (count 7 (secondPFromZ bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPFromZ_true_mem G C p z w (fun j ↦ (h j).1) a hW0
      source j hs j.isLt hBit
  have hHBound : (count 3 (reachesOutsideHFromZ bits source)).toNat ≤
      (C.H.filter QOutside).card := by
    apply count_le_filterCard C.H h _ QOutside (by omega)
    intro j hBit
    have hMem := reachesOutsideHFromZ_true_mem G C p z w h a hInW
      source j hs j.isLt hBit
    have hNe : (j : Nat) ≠ 0 := by
      simp only [bits, reachesOutsideHFromZ, Bool.and_eq_true,
        decide_eq_true_eq] at hBit
      exact hBit.1
    have hNotW : (h j).1 ∉ zExternalUnion G C := by
      intro hjW
      have hj0 : j = 0 := (hInW j).mp hjW
      exact hNe (Fin.ext_iff.mp hj0)
    exact ⟨hNotW, hMem⟩
  have hZCard : (C.Z.filter Q).card ≤ 5 := by
    calc
      (C.Z.filter Q).card ≤ C.Z.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hWCard : ((zExternalUnion G C).filter Q).card ≤ 6 := by
    calc
      ((zExternalUnion G C).filter Q).card ≤ (zExternalUnion G C).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by simpa using (Fintype.card_congr w).symm
  have hPCard : (C.P.filter Q).card ≤ 7 := by
    calc
      (C.P.filter Q).card ≤ C.P.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : (C.H.filter QOutside).card ≤ 3 := by
    calc
      (C.H.filter QOutside).card ≤ C.H.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := by simpa using (Fintype.card_congr h).symm
  have hCountNat : (zSecondCount bits source).toNat =
      (count 5 (secondZFromZ bits source)).toNat +
        (count 6 (secondWFromZ bits source)).toNat +
          (count 7 (secondPFromZ bits source)).toNat +
            (count 3 (reachesOutsideHFromZ bits source)).toNat := by
    rw [zSecondCount, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  let SZ := C.Z.filter Q
  let SW := (zExternalUnion G C).filter Q
  let SP := C.P.filter Q
  let SH := C.H.filter QOutside
  have hZ_W : Disjoint SZ SW := by
    rw [Finset.disjoint_left]
    intro v hvZ hvW
    exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
      (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvW).1
  have hZW_P : Disjoint (SZ ∪ SW) SP := by
    rw [Finset.disjoint_left]
    intro v hvZW hvP
    rcases Finset.mem_union.mp hvZW with hvZ | hvW
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
        (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
    · exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
        (Finset.mem_filter.mp hvP).1 (Finset.mem_filter.mp hvW).1
  have hZWP_H : Disjoint (SZ ∪ SW ∪ SP) SH := by
    rw [Finset.disjoint_left]
    intro v hvZWP hvH
    rcases Finset.mem_union.mp hvZWP with hvZW | hvP
    · rcases Finset.mem_union.mp hvZW with hvZ | hvW
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
          (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvH).1
      · exact (Finset.mem_filter.mp hvH).2.1 (Finset.mem_filter.mp hvW).1
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 (Finset.mem_filter.mp hvP).1
  have hUnionSubset : SZ ∪ SW ∪ SP ∪ SH ⊆
      G.secondOutNeighborFinset u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvZWP | hvH
    · rcases Finset.mem_union.mp hvZWP with hvZW | hvP
      · rcases Finset.mem_union.mp hvZW with hvZ | hvW
        · exact (Finset.mem_filter.mp hvZ).2
        · exact (Finset.mem_filter.mp hvW).2
      · exact (Finset.mem_filter.mp hvP).2
    · exact (Finset.mem_filter.mp hvH).2.2
  have hUnionCard : (SZ ∪ SW ∪ SP ∪ SH).card =
      SZ.card + SW.card + SP.card + SH.card := by
    rw [Finset.card_union_of_disjoint hZWP_H,
      Finset.card_union_of_disjoint hZW_P,
      Finset.card_union_of_disjoint hZ_W]
  rw [hCountNat]
  calc
    (count 5 (secondZFromZ bits source)).toNat +
          (count 6 (secondWFromZ bits source)).toNat +
        (count 7 (secondPFromZ bits source)).toNat +
      (count 3 (reachesOutsideHFromZ bits source)).toNat ≤
        SZ.card + SW.card + SP.card + SH.card := by
      dsimp only [SZ, SW, SP, SH]
      omega
    _ = (SZ ∪ SW ∪ SP ∪ SH).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card :=
      Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (z ⟨source, hs⟩).1 := rfl

/-- Minimum outdegree and absence of a Seymour vertex imply the complete
Boolean `Z` row required by `familyCore`. -/
theorem zRow_coreBits_true (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ zExternalUnion G C})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (hW0 : (w 0).1 = (h 0).1)
    (hInW : ∀ j : Fin 3, (h j).1 ∈ zExternalUnion G C ↔ j = 0)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 5) :
    ((8 : BitVec 8).ule
        (zDegree (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source) &&
      zNonSeymour
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (z ⟨source, hs⟩).1
  have hDegree := zDegree_coreBits_toNat G C p z w (fun j ↦ (h j).1) a
    source hs
  have hSecond := zSecondCount_coreBits_toNat_le_secondOutdegree
    G C p z w h a hW0 hInW source hs
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [Bool.and_eq_true]
  constructor
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hMin u
  · simp only [zNonSeymour, BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hSecond.trans_lt (by simpa [u] using hStrict)

end SeymourEight.FiveZExactGraphBridge
