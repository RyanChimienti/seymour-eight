import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMtwoAssembly
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.EligibleType
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeMThreeHDefs
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMthreeLocalBridge

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Equality closure for external defect three in the three-`Z` row

At defect three all aggregate capacity inequalities are equalities.  Hence
`H` is a tournament and every `X` vertex is exact and dominates both omitted
`A` targets.  The exact-vertex deletion inequality leaves a 36-bit tournament
obstruction, avoiding a second large graph certificate.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMthreeBridge

open CertificateBridge Shared
open BroadFourBridge RepeatedSharedOmissionBridge
open ZThreeMThreeHCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure HLabels (C : G.LocalConfiguration) where
  aone : Fin 2 ≃ {v : V // v ∈ C.A1}
  x : Fin 4 ≃ {v : V // v ∈ C.X}
  h : Fin 6 ≃ {v : V // v ∈ C.H}
  h_aone : ∀ i : Fin 2, (h ⟨i, by omega⟩).1 = (aone i).1
  h_x : ∀ i : Fin 4, (h ⟨i + 2, by omega⟩).1 = (x i).1

noncomputable def labels (C : G.LocalConfiguration)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hHCard : C.H.card = 6) : HLabels G C := by
  let ea := finsetEquivFin C.A1 hAOneCard
  let ex := finsetEquivFin C.X hXCard
  let f : Fin 6 → {v : V // v ∈ C.H} := fun i =>
    if hi : i.val < 2 then
      ⟨(ea ⟨i.val, hi⟩).1, Finset.mem_union_left C.X (ea ⟨i.val, hi⟩).2⟩
    else
      ⟨(ex ⟨i.val - 2, by omega⟩).1,
        Finset.mem_union_right C.A1 (ex ⟨i.val - 2, by omega⟩).2⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro i j hij
      by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
      · have he : (⟨i.val, hi⟩ : Fin 2) = ⟨j.val, hj⟩ := by
          apply ea.injective
          apply Subtype.ext
          simpa [f, hi, hj] using congrArg Subtype.val hij
        apply Fin.ext
        simpa using congrArg Fin.val he
      · have hval : (ea ⟨i.val, hi⟩).1 =
            (ex ⟨j.val - 2, by omega⟩).1 := by
          simpa [f, hi, hj] using congrArg Subtype.val hij
        exact ((Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
            (ea ⟨i.val, hi⟩).2 (hval ▸ (ex ⟨j.val - 2, by omega⟩).2)).elim
      · have hval : (ex ⟨i.val - 2, by omega⟩).1 =
            (ea ⟨j.val, hj⟩).1 := by
          simpa [f, hi, hj] using congrArg Subtype.val hij
        exact ((Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
            (ea ⟨j.val, hj⟩).2 (hval ▸ (ex ⟨i.val - 2, by omega⟩).2)).elim
      · have he : (⟨i.val - 2, by omega⟩ : Fin 4) =
            ⟨j.val - 2, by omega⟩ := by
          apply ex.injective
          apply Subtype.ext
          simpa [f, hi, hj] using congrArg Subtype.val hij
        apply Fin.ext
        have := congrArg Fin.val he
        change i.val - 2 = j.val - 2 at this
        have hi2 := Nat.le_of_not_gt hi
        have hj2 := Nat.le_of_not_gt hj
        omega
    · simpa using hHCard.symm
  let eh := Equiv.ofBijective f hf
  refine ⟨ea, ex, eh, ?_, ?_⟩
  · intro i
    simp [eh, f, ea, i.isLt]
  · intro i
    simp [eh, f, ex]

def hBitAt (C : G.LocalConfiguration) (L : HLabels G C) (n : Nat) : Bool :=
  if hn : n < 36 then
    decide (G.Adj (L.h ⟨n / 6, by omega⟩).1
      (L.h ⟨n % 6, Nat.mod_lt _ (by omega)⟩).1)
  else false

private def graphBits (C : G.LocalConfiguration) (L : HLabels G C) :
    Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 36 => hBitAt G C L n))

@[simp] theorem getLsbD_graphBits (C : G.LocalConfiguration) (L : HLabels G C)
    (n : Nat) (hn : n < 36) :
    (graphBits G C L).getLsbD n = hBitAt G C L n := by
  rw [graphBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn)
      false, List.getElem_ofFn]

theorem hArc_graphBits (C : G.LocalConfiguration) (L : HLabels G C)
    (i j : Nat) (hi : i < 6) (hj : j < 6) :
    hArc (graphBits G C L) i j =
      (decide (i ≠ j) &&
        decide (G.Adj (L.h ⟨i, hi⟩).1 (L.h ⟨j, hj⟩).1)) := by
  by_cases hij : i = j
  · simp [hArc, hij]
  · rw [hArc, getLsbD_graphBits G C L _ (by omega)]
    simp only [hBitAt, show 6 * i + j < 36 by omega, dite_true]
    have hDiv : (6 * i + j) / 6 = i := by omega
    have hMod : (6 * i + j) % 6 = j := by
      simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj
    simp only [hDiv, hMod]

private theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    ZThreeMThreeHCore.any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [ZThreeMThreeHCore.any]
  | succ n ih =>
      rw [ZThreeMThreeHCore.any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hf⟩ | hf)
        · exact ⟨i, by omega, hf⟩
        · exact ⟨n, by omega, hf⟩
      · rintro ⟨i, hi, hf⟩
        by_cases hin : i = n
        · exact Or.inr (hin ▸ hf)
        · exact Or.inl ⟨i, by omega, hf⟩

private theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    ZThreeMThreeHCore.all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [ZThreeMThreeHCore.all]
  | succ n ih =>
      rw [ZThreeMThreeHCore.all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hprev, hn⟩ i hi
        by_cases hin : i = n
        · exact hin ▸ hn
        · exact hprev i (by omega)
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

private theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (ZThreeMThreeHCore.count n f).toNat =
      ∑ i ∈ Finset.range n, (ZThreeMThreeHCore.bitCount (f i)).toNat := by
  induction n with
  | zero => simp [ZThreeMThreeHCore.count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hLe : (∑ i ∈ Finset.range n,
          (ZThreeMThreeHCore.bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [ZThreeMThreeHCore.count, BitVec.toNat_add, ih hn',
        Finset.sum_range_succ]
      cases hf : f n
      · simpa [ZThreeMThreeHCore.bitCount, hf] using Nat.mod_eq_of_lt
          (by omega : (∑ i ∈ Finset.range n,
            (ZThreeMThreeHCore.bitCount (f i)).toNat) < 256)
      · simpa [ZThreeMThreeHCore.bitCount, hf] using Nat.mod_eq_of_lt
          (by omega : (∑ i ∈ Finset.range n,
            (ZThreeMThreeHCore.bitCount (f i)).toNat) + 1 < 256)

private theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool)
    (hn : n < 256) :
    (ZThreeMThreeHCore.count n f).toNat =
      ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn,
    ← Fin.sum_univ_eq_sum_range
      (fun i ↦ (ZThreeMThreeHCore.bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [ZThreeMThreeHCore.bitCount]

theorem xReach_graphBits_iff (C : G.LocalConfiguration) (L : HLabels G C)
    (hG : G.IsOriented) (x target : Nat) (hx : x < 4) (ht : target < 4) :
    xReach (graphBits G C L) x target = true ↔
      RepeatedSharedOmissionBridge.reachesWithinH G C
        (L.x ⟨x, hx⟩).1 (L.x ⟨target, ht⟩).1 := by
  unfold xReach RepeatedSharedOmissionBridge.reachesWithinH
  rw [Bool.or_eq_true, any_eq_true_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hs := L.h_x ⟨x, hx⟩
  have ht' := L.h_x ⟨target, ht⟩
  constructor
  · rintro (hDirect | ⟨middle, hm, ⟨⟨⟨hneS, hneT⟩, hFirst⟩, hLast⟩⟩)
    · left
      rw [hArc_graphBits G C L (x + 2) (target + 2) (by omega)
        (by omega)] at hDirect
      rw [Bool.and_eq_true] at hDirect
      simpa [hs, ht'] using hDirect.2
    · right
      refine ⟨(L.h ⟨middle, hm⟩).1, (L.h ⟨middle, hm⟩).2, ?_, ?_, ?_, ?_⟩
      · intro heq
        apply hneS
        have hiEq : (⟨middle, hm⟩ : Fin 6) = ⟨x + 2, by omega⟩ := by
          apply L.h.injective
          apply Subtype.ext
          simpa [hs] using heq
        exact congrArg Fin.val hiEq
      · intro heq
        apply hneT
        have hiEq : (⟨middle, hm⟩ : Fin 6) = ⟨target + 2, by omega⟩ := by
          apply L.h.injective
          apply Subtype.ext
          simpa [ht'] using heq
        exact congrArg Fin.val hiEq
      · rw [hArc_graphBits G C L (x + 2) middle (by omega) hm] at hFirst
        rw [Bool.and_eq_true] at hFirst
        simpa [hs] using hFirst.2
      · rw [hArc_graphBits G C L middle (target + 2) hm (by omega)] at hLast
        rw [Bool.and_eq_true] at hLast
        simpa [ht'] using hLast.2
  · rintro (hDirect | ⟨middle, hmH, hneS, hneT, hFirst, hLast⟩)
    · left
      rw [hArc_graphBits G C L (x + 2) (target + 2) (by omega) (by omega)]
      have hne : x ≠ target := by
        intro heq
        subst target
        exact hG.1 _ hDirect
      simp [hs, ht', hDirect, hne]
    · obtain ⟨i, hi⟩ := L.h.surjective ⟨middle, hmH⟩
      right
      refine ⟨i, i.isLt, ?_⟩
      have hmid : (L.h i).1 = middle := congrArg Subtype.val hi
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro heq
        apply hneS
        rw [← hmid, ← hs]
        have hiEq : i = ⟨x + 2, by omega⟩ := Fin.ext (by omega)
        exact congrArg (fun q ↦ (L.h q).1) hiEq
      · intro heq
        apply hneT
        rw [← hmid, ← ht']
        have hiEq : i = ⟨target + 2, by omega⟩ := Fin.ext (by omega)
        exact congrArg (fun q ↦ (L.h q).1) hiEq
      · rw [hArc_graphBits G C L (x + 2) i (by omega) i.isLt]
        have hne : x + 2 ≠ i.val := by
          intro heq
          apply hneS
          rw [← hmid, ← hs]
          have hiEq : i = ⟨x + 2, by omega⟩ := Fin.ext heq.symm
          exact congrArg (fun q ↦ (L.h q).1) hiEq
        simp [hs, hmid, hFirst, hne]
      · rw [hArc_graphBits G C L i (target + 2) i.isLt (by omega)]
        have hne : i.val ≠ target + 2 := by
          intro heq
          apply hneT
          rw [← hmid, ← ht']
          have hiEq : i = ⟨target + 2, by omega⟩ := Fin.ext heq
          exact congrArg (fun q ↦ (L.h q).1) hiEq
        simp [ht', hmid, hLast, hne]

open Classical in
theorem xReachCount_toNat (C : G.LocalConfiguration) (L : HLabels G C)
    (hG : G.IsOriented) (x : Nat) (hx : x < 4) :
    (xReachCount (graphBits G C L) x).toNat =
      (C.X.filter fun y ↦ y ≠ (L.x ⟨x, hx⟩).1 ∧
        RepeatedSharedOmissionBridge.reachesWithinH G C
          (L.x ⟨x, hx⟩).1 y).card := by
  classical
  rw [xReachCount, toNat_count_eq_fin_sum 4 _ (by omega),
    filterCard_eq_sum_fin C.X L.x
      (fun y ↦ y ≠ (L.x ⟨x, hx⟩).1 ∧
        RepeatedSharedOmissionBridge.reachesWithinH G C
          (L.x ⟨x, hx⟩).1 y)]
  apply Finset.sum_congr rfl
  intro target htMem
  have hne : (L.x target).1 ≠ (L.x ⟨x, hx⟩).1 ↔ target.val ≠ x := by
    constructor
    · intro hn heq
      apply hn
      have hiEq : target = ⟨x, hx⟩ := Fin.ext heq
      exact congrArg (fun q ↦ (L.x q).1) hiEq
    · intro hn heq
      apply hn
      have hiEq := L.x.injective (Subtype.ext heq)
      exact Fin.ext_iff.mp hiEq
  have hReach := xReach_graphBits_iff G C L hG x target hx target.isLt
  simp [hne, hReach, Bool.and_eq_true]

open Classical in
theorem xOutH_toNat (C : G.LocalConfiguration) (L : HLabels G C)
    (hG : G.IsOriented) (x : Nat) (hx : x < 4) :
    (xOutH (graphBits G C L) x).toNat =
      directCount G C.H (L.x ⟨x, hx⟩).1 := by
  rw [xOutH, toNat_count_eq_fin_sum 6 _ (by omega),
    directCount_eq_sum_fin G C.H L.h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hArc_graphBits G C L (x + 2) j (by omega) j.isLt]
  have hs := L.h_x ⟨x, hx⟩
  by_cases heq : x + 2 = j.val
  · have hi : (⟨x + 2, by omega⟩ : Fin 6) = j := Fin.ext heq
    have hverts : (L.x ⟨x, hx⟩).1 = (L.h j).1 :=
      hs.symm.trans (congrArg (fun q ↦ (L.h q).1) hi)
    have hNo : ¬G.Adj (L.x ⟨x, hx⟩).1 (L.h j).1 := by
      rw [hverts]
      exact hG.1 _
    simp [heq, hNo]
  · simp [heq, hs]

open Classical in
theorem x_type_bound (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPCard : C.P.card = 7) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 4) (hRCard : C.R.card = 1)
    (hZCard : C.Z.card = 3)
    (hPZ : edgeCount G C.P C.Z = 18)
    (source : V) (hSourceX : source ∈ C.X)
    (hDegree : G.outdegree source = 8)
    (hDomPivot : G.Adj source C.a1)
    (hDomR : ∀ r ∈ C.R, G.Adj source r) :
    let b := directCount G C.P source
    let r := (C.X.filter fun y ↦ y ≠ source ∧
      RepeatedSharedOmissionBridge.reachesWithinH G C source y).card
    1 ≤ b ∧ (b = 1 ∨ (b = 2 ∧ r ≤ 3) ∨
      (b = 3 ∧ r ≤ 2) ∨ (4 ≤ b ∧ r ≤ 1)) := by
  classical
  let pMiss := C.P.filter fun p ↦ ¬G.Adj source p
  let aMiss := C.A1.filter fun a ↦ ¬G.Adj source a
  let xReached := C.X.filter fun y ↦ y ≠ source ∧
    RepeatedSharedOmissionBridge.reachesWithinH G C source y
  let xStrict := xReached.filter fun y ↦ ¬G.Adj source y
  let zReached := C.Z.filter fun z ↦
    ∃ p ∈ C.P, G.Adj source p ∧ G.Adj p z
  let b := directCount G C.P source
  let dA := directCount G C.A1 source
  let dX := directCount G C.X source
  let r := xReached.card
  have hSourceA : source ∈ C.A :=
    Digraph.LocalConfiguration.X_subset_A (G := G) C hSourceX
  have hDirectH : directCount G C.H source = dA + dX := by
    simpa [Digraph.LocalConfiguration.H, dA, dX] using
      directCount_union_of_disjoint G C.A1 C.X source
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  have hDirectR : directCount G C.R source = 1 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    have hFilter : C.R.filter (G.Adj source) = C.R := by
      apply Finset.filter_eq_self.mpr
      intro q hq
      exact hDomR q hq
    rw [hFilter, hRCard]
  have hDirectA : directCount G C.A source = 2 + dA + dX := by
    have hHa1 : Disjoint C.H {C.a1} := by
      rw [Finset.disjoint_left]
      intro v hvH hv
      have hvEq := Finset.mem_singleton.mp hv
      subst v
      rcases Finset.mem_union.mp hvH with hvA1 | hvX
      · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
      · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
    have hPartsR := Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C,
      directCount_union_of_disjoint G (C.A1 ∪ C.X ∪ {C.a1}) C.R source hPartsR,
      directCount_union_of_disjoint G (C.A1 ∪ C.X) {C.a1} source hHa1,
      directCount_union_of_disjoint G C.A1 C.X source
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C),
      directCount_singleton, hDirectR]
    simp [epsilonAt, hDomPivot]
    omega
  have hDegreeSplit : b + dA + dX = 6 := by
    have hd := BroadFourBridge.A_outdegree_eq_A_add_P G C hG hPB source hSourceA
    rw [hDegree, hDirectA] at hd
    change 8 = 2 + dA + dX + b at hd
    omega
  have hpSplit : pMiss.card + b = 7 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := C.P) (p := fun p ↦ G.Adj source p)
    simpa [pMiss, b, directCount, CertificateBridge.internalFirstNeighbors,
      Nat.add_comm, hPCard] using h
  have haSplit : aMiss.card + dA = 2 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := C.A1) (p := fun a ↦ G.Adj source a)
    simpa [aMiss, dA, directCount, CertificateBridge.internalFirstNeighbors,
      Nat.add_comm, hAOneCard] using h
  have hDirectXSubset : C.X.filter (G.Adj source) ⊆ xReached := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyX, hsy⟩
    exact Finset.mem_filter.mpr ⟨hyX, fun heq ↦ hG.1 source (heq ▸ hsy),
      Or.inl hsy⟩
  have hDirectXEq : xReached.filter (G.Adj source) =
      C.X.filter (G.Adj source) := by
    apply Finset.Subset.antisymm
    · intro y hy
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1,
          (Finset.mem_filter.mp hy).2⟩
    · intro y hy
      exact Finset.mem_filter.mpr ⟨hDirectXSubset hy,
        (Finset.mem_filter.mp hy).2⟩
  have hxSplit : xStrict.card + dX = r := by
    have h := Finset.card_filter_add_card_filter_not
      (s := xReached) (p := fun y ↦ G.Adj source y)
    rw [hDirectXEq] at h
    simpa [xStrict, dX, r, directCount,
      CertificateBridge.internalFirstNeighbors, Nat.add_comm] using h
  have hSecondBound : pMiss.card + aMiss.card + xStrict.card + zReached.card ≤
      G.secondOutdegree source := by
    let U := pMiss ∪ aMiss ∪ xStrict ∪ zReached
    have hUSubset : U ⊆ G.secondOutNeighborFinset source := by
      intro v hv
      simp only [U, Finset.mem_union] at hv
      rcases hv with ((hvP | hvA) | hvX) | hvZ
      · rcases Finset.mem_filter.mp hvP with ⟨hvPMem, hn⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨C.a1, hDomPivot, (Finset.mem_filter.mp hvPMem).2⟩, hn,
          fun heq ↦ (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hSourceA
              (Digraph.LocalConfiguration.P_subset_B (G := G) C
                (heq ▸ hvPMem))⟩
      · rcases Finset.mem_filter.mp hvA with ⟨hvAMem, hn⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨C.a1, hDomPivot, (Finset.mem_filter.mp hvAMem).2⟩, hn,
          fun heq ↦ (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
              (heq ▸ hvAMem) hSourceX⟩
      · rcases Finset.mem_filter.mp hvX with ⟨hvReach, hn⟩
        rcases (Finset.mem_filter.mp hvReach).2 with ⟨hne, hReach⟩
        rcases hReach with hDirect | ⟨middle, hmH, _, _, hsm, hmv⟩
        · exact (hn hDirect).elim
        · rw [Digraph.mem_secondOutNeighborFinset,
            Digraph.mem_secondOutNeighborSet]
          exact ⟨⟨middle, hsm, hmv⟩, hn, hne⟩
      · rcases Finset.mem_filter.mp hvZ with ⟨hvZ, p, hp, hsp, hpv⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨p, hsp, hpv⟩, A_not_adj_Z G C hG source v hSourceA hvZ,
          fun heq ↦ (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ
              (heq ▸ Finset.mem_union_right C.A1 hSourceX)⟩
    have hPA : Disjoint pMiss aMiss :=
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm.mono
        (Finset.filter_subset _ _) ((Finset.filter_subset _ _).trans
          (Finset.subset_union_left))
    have hPAX : Disjoint (pMiss ∪ aMiss) xStrict := by
      rw [Finset.disjoint_left]
      intro v hvPA hvX
      have hvXC := (Finset.mem_filter.mp (Finset.mem_filter.mp hvX).1).1
      rcases Finset.mem_union.mp hvPA with hvP | hvA
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
            (Finset.mem_union_right C.A1 hvXC) (Finset.mem_filter.mp hvP).1
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
            (Finset.mem_filter.mp hvA).1 hvXC
    have hAllZ : Disjoint (pMiss ∪ aMiss ∪ xStrict) zReached := by
      rw [Finset.disjoint_left]
      intro v hvLeft hvZ
      have hvZC := (Finset.mem_filter.mp hvZ).1
      rcases Finset.mem_union.mp hvLeft with hvPA | hvX
      · rcases Finset.mem_union.mp hvPA with hvP | hvA
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZC
              (Finset.mem_filter.mp hvP).1
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZC
              (Finset.mem_union_left C.X (Finset.mem_filter.mp hvA).1)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZC
            (Finset.mem_union_right C.A1
              (Finset.mem_filter.mp (Finset.mem_filter.mp hvX).1).1)
    have hUCard : U.card =
        pMiss.card + aMiss.card + xStrict.card + zReached.card := by
      simp only [U]
      rw [Finset.card_union_of_disjoint hAllZ,
        Finset.card_union_of_disjoint hPAX,
        Finset.card_union_of_disjoint hPA]
    rw [← hUCard]
    exact Finset.card_le_card hUSubset
  have hSecondLe : G.secondOutdegree source ≤ 7 :=
    Digraph.secondOutdegree_le_seven G hDegree hNoSeymour
  have hReachBound : 3 + r + zReached.card ≤ 7 := by
    have hIdentity : pMiss.card + aMiss.card + xStrict.card = 3 + r := by
      omega
    omega
  let S := C.P.filter (G.Adj source)
  let T := C.P \ S
  have hSCard : S.card = b := by rfl
  have hTCard : T.card = 7 - b := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _),
      hPCard, hSCard]
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = C.P := Finset.union_sdiff_of_subset
    (Finset.filter_subset _ _)
  have hSplit : edgeCount G C.P C.Z =
      edgeCount G S C.Z + edgeCount G T C.Z := by
    rw [← hUnion,
      RepeatedSharedOmissionBridge.edgeCount_source_union G S T C.Z hST]
  have hTCap := edgeCount_le_card_mul_card G T C.Z
  rw [hTCard, hZCard] at hTCap
  have hSLower : 3 * b - 3 ≤ edgeCount G S C.Z := by omega
  have hSEq : edgeCount G S C.Z = edgeCount G S zReached := by
    unfold edgeCount
    apply Finset.sum_congr rfl
    intro p hp
    unfold directCount CertificateBridge.internalFirstNeighbors
    congr 1
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hpz⟩
      refine ⟨Finset.mem_filter.mpr ⟨hz, p, (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2, hpz⟩, hpz⟩
    · rintro ⟨hz, hpz⟩
      exact ⟨(Finset.mem_filter.mp hz).1, hpz⟩
  have hSCap : edgeCount G S C.Z ≤ b * zReached.card := by
    rw [hSEq, ← hSCard]
    exact edgeCount_le_card_mul_card G S zReached
  have hbLe : b ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hzTwo (hb : 2 ≤ b) : 2 ≤ zReached.card := by
    interval_cases b <;> omega
  have hzThree (hb : 4 ≤ b) : 3 ≤ zReached.card := by
    interval_cases b <;> omega
  have hdALe : dA ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hAOneCard
  have hdXLe : dX ≤ 3 := by
    have hSub : C.X.filter (G.Adj source) ⊆ C.X.erase source := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyX, hsy⟩
      exact Finset.mem_erase.mpr ⟨fun heq ↦ hG.1 source (heq ▸ hsy), hyX⟩
    have hc := Finset.card_le_card hSub
    rw [Finset.card_erase_of_mem hSourceX, hXCard] at hc
    exact hc
  have hbPos : 1 ≤ b := by omega
  refine ⟨hbPos, ?_⟩
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  by_cases hb2 : b = 2
  · right; left
    refine ⟨hb2, ?_⟩
    change xReached.card ≤ 3
    have hSub : xReached ⊆ C.X.erase source := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyX, hyNe, _⟩
      exact Finset.mem_erase.mpr ⟨hyNe, hyX⟩
    have hc := Finset.card_le_card hSub
    rw [Finset.card_erase_of_mem hSourceX, hXCard] at hc
    exact hc
  by_cases hb3 : b = 3
  · right; right; left
    refine ⟨hb3, ?_⟩
    change xReached.card ≤ 2
    have hz := hzTwo (by omega)
    omega
  · right; right; right
    have hb4 : 4 ≤ b := by omega
    refine ⟨hb4, ?_⟩
    change xReached.card ≤ 1
    have hz := hzThree hb4
    omega

theorem zThree_defectThree_impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (_hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 3)
    (hDefect : 21 - edgeCount G C.P C.Z = 3) : False := by
  classical
  have hPB : C.P = C.B :=
    RepeatedSharedOmissionBridge.p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hAOneCard : C.A1.card = 2 := hk
  have hXCard : C.X.card = 4 := hx
  have hZCard : C.Z.card = 3 := by
    change C.Z.card = 3 at hz
    exact hz
  have hRCard : C.R.card = 1 := by
    have h := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
    rw [hx] at h
    omega
  have hQCard : C.Q.card = 0 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hPZLe : edgeCount G C.P C.Z ≤ 21 := by
    exact (edgeCount_le_card_mul_card G C.P C.Z).trans_eq (by
      rw [hPCard, hZCard])
  have hPZ : edgeCount G C.P C.Z = 18 := by omega
  have hHP : 25 ≤ edgeCount G C.H C.P :=
    twentyFive_le_H_to_P G C hG hMin hRootDegree hk hx hy hPB
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHLe : edgeCount G C.P C.H ≤ 17 := by omega
  have hPPLe : edgeCount G C.P C.P ≤ 21 := by
    have hInternal := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at hInternal
    norm_num [Nat.choose] at hInternal
    exact hInternal
  have hRootZero := edgeCount_P_root_zero G C hNoRoot
  have hRootSum : (∑ p ∈ C.P, epsilonAt G p C.s) = 0 := by
    rw [← edgeCount_singleton G C.P C.s]
    exact hRootZero
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  rw [hRootSum, hPZ] at hAccounting
  have hPDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hPH : edgeCount G C.P C.H = 17 := by omega
  have hPP : edgeCount G C.P C.P = 21 := by omega
  have hPDegreeSum : ∑ p ∈ C.P, G.outdegree p = 56 := by omega
  have hPDegree : ∀ p ∈ C.P, G.outdegree p = 8 :=
    pointwise_eq_of_sum_eq_card_mul C.P G.outdegree 8
      (fun p hp ↦ hMin p) (by simpa [hPCard] using hPDegreeSum)
  have hHPExact : edgeCount G C.H C.P = 25 := by omega
  have hHAUpper := Shared.H_to_A_le_internal_add_x_add_xR G C hG
  rw [hHCard, hx, hRCard] at hHAUpper
  norm_num [Nat.choose] at hHAUpper
  have hHQZero : edgeCount G C.H C.Q = 0 := by
    have hCap := edgeCount_le_card_mul_card G C.H C.Q
    rw [hQCard] at hCap
    omega
  have hHDegreeSplit := BSixKThree.degreeSum_H_eq_A_add_P_add_Q G C hG
  rw [hHPExact, hHQZero] at hHDegreeSplit
  have hHDegreeLower : 48 ≤ ∑ u ∈ C.H, G.outdegree u := by
    calc
      48 = ∑ _u ∈ C.H, 8 := by simp [hHCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hHA : edgeCount G C.H C.A = 23 := by omega
  have hHDegreeSum : ∑ u ∈ C.H, G.outdegree u = 48 := by omega
  have hHHLe := internal_edgeCount_le_choose_two G C.H hG
  rw [hHCard] at hHHLe
  norm_num [Nat.choose] at hHHLe
  have hHa1Le := Shared.H_to_a1_le_x G C hG
  rw [hx] at hHa1Le
  have hHRLe := Shared.H_to_R_le_x_mul_card_R G C
  rw [hx, hRCard] at hHRLe
  have hHa1Disjoint : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hv
    have hvEq := Finset.mem_singleton.mp hv
    subst v
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  have hPartsR := Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hHASplit : edgeCount G C.H C.A = edgeCount G C.H C.H +
      edgeCount G C.H {C.a1} + edgeCount G C.H C.R := by
    rw [← Digraph.LocalConfiguration.local_parts_union_R (G := G) C,
      edgeCount_union_of_disjoint G C.H (C.A1 ∪ C.X ∪ {C.a1}) C.R hPartsR,
      edgeCount_union_of_disjoint G C.H (C.A1 ∪ C.X) {C.a1} hHa1Disjoint]
    change edgeCount G C.H (C.A1 ∪ C.X) + edgeCount G C.H {C.a1} +
        edgeCount G C.H C.R =
      edgeCount G C.H (C.A1 ∪ C.X) + edgeCount G C.H {C.a1} +
        edgeCount G C.H C.R
    rfl
  have hHH : edgeCount G C.H C.H = 15 := by omega
  have hHa1 : edgeCount G C.H {C.a1} = 4 := by omega
  have hHR : edgeCount G C.H C.R = 4 := by omega
  have hHDegree : ∀ u ∈ C.H, G.outdegree u = 8 :=
    pointwise_eq_of_sum_eq_card_mul C.H G.outdegree 8
      (fun u hu ↦ hMin u) (by simpa [hHCard] using hHDegreeSum)
  have hHTournament : ∀ u ∈ C.H, ∀ v ∈ C.H, u ≠ v →
      G.Adj u v ∨ G.Adj v u := by
    intro u hu v hv hne
    exact RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
      G C.H hG (by simpa [hHCard, Nat.choose] using hHH) hu hv hne
  have hDomPivot : ∀ u ∈ C.X, G.Adj u C.a1 := by
    let incoming := C.H.filter (fun u ↦ G.Adj u C.a1)
    have hSubset : incoming ⊆ C.X := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huH, hua1⟩
      rcases Finset.mem_union.mp huH with huA1 | huX
      · exact (hG.2 (Finset.mem_filter.mp huA1).2 hua1).elim
      · exact huX
    have hIncomingCard : incoming.card = 4 := by
      rw [edgeCount_eq_sum_incoming G C.H {C.a1}] at hHa1
      simpa [incoming, internalInDegree] using hHa1
    have hEq : incoming = C.X :=
      Finset.eq_of_subset_of_card_le hSubset (by omega)
    intro u hu
    have huIncoming : u ∈ incoming := by rw [hEq]; exact hu
    exact (Finset.mem_filter.mp huIncoming).2
  have hDomR : ∀ u ∈ C.X, ∀ r ∈ C.R, G.Adj u r := by
    intro u hu r hrMem
    have hREq : C.R = {r} := by
      exact (Finset.eq_of_subset_of_card_le
        (Finset.singleton_subset_iff.mpr hrMem) (by simp [hRCard])).symm
    have hHRSingle : edgeCount G C.H {r} = 4 := by simpa [hREq] using hHR
    let incoming := C.H.filter (fun v ↦ G.Adj v r)
    have hSubset : incoming ⊆ C.X := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvH, hvr⟩
      rcases Finset.mem_union.mp hvH with hvA1 | hvX
      · exact (RepeatedSharedOmissionBridge.A1_not_adj_R G C v r hvA1 hrMem hvr).elim
      · exact hvX
    have hIncomingCard : incoming.card = 4 := by
      rw [edgeCount_eq_sum_incoming G C.H {r}] at hHRSingle
      simpa [incoming, internalInDegree] using hHRSingle
    have hEq : incoming = C.X :=
      Finset.eq_of_subset_of_card_le hSubset (by omega)
    have huIncoming : u ∈ incoming := by rw [hEq]; exact hu
    exact (Finset.mem_filter.mp huIncoming).2
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  let L := ZThreeMthreeLocalBridge.labels G C hPCard hACard hAOneCard
    hXCard hRCard hHCard hZCard
  have hDisjoint : Disjoint C.P C.H :=
    (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
  let K := C.P ∪ C.H
  have hKCard : K.card = 13 := by
    simp [K, Finset.card_union_of_disjoint hDisjoint, hPCard, hHCard]
  have hKEdges : edgeCount G K K = 78 := by
    rw [RepeatedSharedOmissionBridge.edgeCount_source_union G C.P C.H K hDisjoint,
      show K = C.P ∪ C.H from rfl,
      edgeCount_union_of_disjoint G C.P C.P C.H hDisjoint,
      edgeCount_union_of_disjoint G C.H C.P C.H hDisjoint]
    omega
  have hKMax : edgeCount G K K = K.card.choose 2 := by
    rw [hKEdges, hKCard]
    norm_num [Nat.choose]
  have hCompleteK {u v : V} (hu : u ∈ K) (hv : v ∈ K) (hne : u ≠ v) :=
    RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
      G K hG hKMax hu hv hne
  have hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1 := by
    intro i j hij
    apply hCompleteK
    · exact Finset.mem_union_left C.H (L.p i).2
    · exact Finset.mem_union_left C.H (L.p j).2
    · intro heq
      apply hij
      exact L.p.injective (Subtype.ext heq)
  have hAH : ∀ j : Fin 6, (L.a ⟨j + 1, by omega⟩).1 ∈ C.H := L.a_h
  have hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1 := by
    intro i j
    apply hCompleteK
    · exact Finset.mem_union_left C.H (L.p i).2
    · exact Finset.mem_union_right C.P (hAH j)
    · intro heq
      have hpNotH : (L.p i).1 ∉ C.H :=
        Finset.disjoint_left.mp hDisjoint (L.p i).2
      exact hpNotH (heq ▸ hAH j)
  have hHDegreeLocal : ∀ j : Fin 6,
      G.outdegree (L.a ⟨j + 1, by omega⟩).1 = 8 := by
    intro j
    exact hHDegree _ (hAH j)
  have hPDegreeLocal : ∀ i : Fin 7, G.outdegree (L.p i).1 = 8 := by
    intro i
    exact hPDegree _ (L.p i).2
  have hHTournamentLocal : ∀ i j : Fin 6, i ≠ j →
      G.Adj (L.a ⟨i + 1, by omega⟩).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.a ⟨i + 1, by omega⟩).1 := by
    intro i j hij
    apply hHTournament _ (hAH i) _ (hAH j)
    intro heq
    apply hij
    have hIndex := congrArg Fin.val (L.a.injective (Subtype.ext heq))
    change i.val + 1 = j.val + 1 at hIndex
    apply Fin.ext
    omega
  have hXDomPivotLocal : ∀ x : Fin 4,
      G.Adj (L.a ⟨x + 3, by omega⟩).1 C.a1 := by
    intro x
    exact hDomPivot _ (L.a_x x)
  have hXDomRLocal : ∀ x : Fin 4,
      G.Adj (L.a ⟨x + 3, by omega⟩).1 (L.a 7).1 := by
    intro x
    exact hDomR _ (L.a_x x) _ L.a_r
  have hCore := ZThreeMthreeLocalBridge.core_true G hBound C L hG hPB
    hNoSeymour hRootZero hPComplete hPHComplete hHDegreeLocal hPDegreeLocal
    hHTournamentLocal hXDomPivotLocal hXDomRLocal hPZ
  have hUnsat := ZThreeMThreeLocalCore.unsat
    (ZThreeMthreeLocalBridge.graphBits G C L)
  rw [hCore] at hUnsat
  exact Bool.noConfusion hUnsat

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMthreeBridge
