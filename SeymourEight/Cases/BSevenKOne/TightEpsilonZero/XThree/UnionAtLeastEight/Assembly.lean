import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.GraphBridge
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.Dispatch
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.TerminalCoreGraphBridge

set_option linter.style.header false

namespace SeymourEight.FourZUnionEightAssembly

open FourZUnionEight FourZUnionEightBridge FourZUnionEightGraphBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactCoreBridge FiveZExactGlobalBridge Shared
  BSevenKOneCounting TerminalCoreBridge TerminalCoreGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Sort all seven labels by the same radix key used by the terminal-core
tail sort.  This is the `missing = 0` canonical labelling. -/
noncomputable def fullySortedFinsetEquiv (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P}) :
    Fin 7 ≃ {v : V // v ∈ P} :=
  (Tuple.sort (fun i : Fin 7 ↦
    descendingKey degree hCount (eP i).1)).trans eP

omit [Fintype V] [DecidableEq V] in
theorem fullySorted_key_anti (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P})
    {i j : Fin 7} (hij : i ≤ j) :
    256 * degree (fullySortedFinsetEquiv degree hCount P eP i).1 +
        hCount (fullySortedFinsetEquiv degree hCount P eP i).1 ≥
      256 * degree (fullySortedFinsetEquiv degree hCount P eP j).1 +
        hCount (fullySortedFinsetEquiv degree hCount P eP j).1 := by
  exact Tuple.monotone_sort
    (fun q : Fin 7 ↦ descendingKey degree hCount (eP q).1) hij

omit [Fintype V] [DecidableEq V] in
theorem fullySorted_degree_anti (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P})
    (hCountLt : ∀ v, hCount v < 256) {i j : Fin 7} (hij : i ≤ j) :
    degree (fullySortedFinsetEquiv degree hCount P eP j).1 ≤
      degree (fullySortedFinsetEquiv degree hCount P eP i).1 := by
  have hKey := fullySorted_key_anti degree hCount P eP hij
  have hi := hCountLt (fullySortedFinsetEquiv degree hCount P eP i).1
  have hj := hCountLt (fullySortedFinsetEquiv degree hCount P eP j).1
  omega

omit [Fintype V] [DecidableEq V] in
theorem fullySorted_hCount_anti_of_degree_eq (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P})
    {i j : Fin 7} (hij : i ≤ j)
    (hDegree : degree (fullySortedFinsetEquiv degree hCount P eP i).1 =
      degree (fullySortedFinsetEquiv degree hCount P eP j).1) :
    hCount (fullySortedFinsetEquiv degree hCount P eP j).1 ≤
      hCount (fullySortedFinsetEquiv degree hCount P eP i).1 := by
  have hKey := fullySorted_key_anti degree hCount P eP hij
  omega

/-- At full `P × Z` density every `P` row contains all four `Z`s. -/
theorem rows_four_of_edgeCount_eq_twentyEight (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hPZ : edgeCount G C.P C.Z = 28) (u : V) (hu : u ∈ C.P) :
    directCount G C.Z u = 4 := by
  have huLe : directCount G C.Z u ≤ 4 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hRestLe : ∑ q ∈ C.P.erase u, directCount G C.Z q ≤ 24 := by
    calc
      _ ≤ ∑ _q ∈ C.P.erase u, 4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      _ = 24 := by simp [Finset.card_erase_of_mem hu, hPCard]
  have hSplit := Finset.sum_erase_add C.P (directCount G C.Z) hu
  change (∑ q ∈ C.P, directCount G C.Z q) = 28 at hPZ
  omega

/-- With exactly one missing `P → Z` incidence there is a unique deficient
row: it has size three and every other row has size four. -/
theorem exists_exceptional_row_of_edgeCount_eq_twentySeven
    (C : G.LocalConfiguration) (hPCard : C.P.card = 7)
    (hZCard : C.Z.card = 4) (hPZ : edgeCount G C.P C.Z = 27) :
    ∃ u ∈ C.P, directCount G C.Z u = 3 ∧
      ∀ q ∈ C.P, q ≠ u → directCount G C.Z q = 4 := by
  have hSum : ∑ q ∈ C.P, directCount G C.Z q = 27 := hPZ
  have hEachLe : ∀ q ∈ C.P, directCount G C.Z q ≤ 4 := by
    intro q hq
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  by_contra hNot
  push Not at hNot
  have hAllFour : ∀ q ∈ C.P, directCount G C.Z q = 4 := by
    intro q hq
    have hqLe := hEachLe q hq
    by_contra hne
    have hqThree : directCount G C.Z q ≤ 3 := by omega
    have hRestLe : ∑ r ∈ C.P.erase q, directCount G C.Z r ≤ 24 := by
      calc
        _ ≤ ∑ _r ∈ C.P.erase q, 4 := by
          apply Finset.sum_le_sum
          intro r hr
          exact hEachLe r (Finset.mem_of_mem_erase hr)
        _ = 24 := by simp [Finset.card_erase_of_mem hq, hPCard]
    have hSplit := Finset.sum_erase_add C.P (directCount G C.Z) hq
    have hqEq : directCount G C.Z q = 3 := by omega
    obtain ⟨r, hrP, hrNe, hrNotFour⟩ := hNot q hq hqEq
    have hrLe := hEachLe r hrP
    have hrThree : directCount G C.Z r ≤ 3 := by omega
    have hOthersLe : ∑ t ∈ (C.P.erase q).erase r,
        directCount G C.Z t ≤ 20 := by
      calc
        _ ≤ ∑ _t ∈ (C.P.erase q).erase r, 4 := by
          apply Finset.sum_le_sum
          intro t ht
          exact hEachLe t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
        _ = 20 := by
          have hrErase : r ∈ C.P.erase q := Finset.mem_erase.mpr ⟨hrNe, hrP⟩
          simp [Finset.card_erase_of_mem hrErase,
            Finset.card_erase_of_mem hq, hPCard]
    have hrErase : r ∈ C.P.erase q := Finset.mem_erase.mpr ⟨hrNe, hrP⟩
    have hSplitRest := Finset.sum_erase_add (C.P.erase q)
      (directCount G C.Z) hrErase
    omega
  have hCardSum : (∑ _q ∈ C.P, 4) = 28 := by simp [hPCard]
  have : (∑ q ∈ C.P, directCount G C.Z q) = ∑ _q ∈ C.P, 4 := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hAllFour q hq
  omega

/-- Contradiction after choosing the canonical exceptional/sorted `P` labels.
The separate labelling lemma isolates symmetry normalization from certificate
soundness. -/
theorem impossible_of_compatibleLabels (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 1) (hx : C.x = 3) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (hZCard : C.Z.card = 4)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (missing : Nat) (hMissing : missing ≤ 1)
    (hPZ : edgeCount G C.P C.Z + missing = 28)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hOrder : FourZUnionEight.orderedP missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)) = true) : False := by
  let degreeSum := ∑ u ∈ C.P, G.outdegree u
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
  have hCore := coreBits_true G C hG hMin hNoSeymour hRootDegree hk hx hPB
    hEpsilon hZCard hFullUnion missing degreeSum hMissing hPZ p h hRows rfl hOrder
  change FourZUnionEight.core missing degreeSum bits = true at hCore
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hDegreeLower : 56 ≤ degreeSum := by
    change 56 ≤ ∑ u ∈ C.P, G.outdegree u
    calc
      56 = ∑ _u ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ u ∈ C.P, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hPHUpper : edgeCount G C.P C.H ≤ 14 := by
    have hReverse := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hCross
    simp [hx, Nat.choose] at hReverse
    omega
  have hPPUpper : edgeCount G C.P C.P ≤ 21 :=
    internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ u ∈ C.P, epsilonAt G u C.s = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [epsilonAt, FiveZExactPBridge.no_P_to_s_of_epsilonS_zero
      G C hEpsilon u hu]
  rw [hNoRoot] at hAccounting
  have hDegreeUpper : degreeSum ≤ 63 - missing := by
    change (∑ u ∈ C.P, G.outdegree u) ≤ 63 - missing
    omega
  have hUnsat := FourZUnionEight.core_unsat missing degreeSum hMissing
    hDegreeLower hDegreeUpper bits
  rw [hUnsat] at hCore
  contradiction

/-- The graph-level assembly with canonical labels chosen internally.  At
defect zero all seven `P` labels are sorted; at defect one the unique
three-`Z` row is fixed at zero and the remaining six labels are sorted. -/
theorem impossible_unionEight_of_exactCards (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 1) (hx : C.x = 3) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (hPZLower : 27 ≤ edgeCount G C.P C.Z)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 4)
    (hHCard : C.H.card = 4) : False := by
  classical
  have hPZUpper : edgeCount G C.P C.Z ≤ 28 := by
    have hc := edgeCount_le_card_mul_card G C.P C.Z
    simpa [hPCard, hZCard] using hc
  let h : Fin 4 ≃ {v : V // v ∈ C.H} := finsetEquivFin C.H hHCard
  have hCountLt : ∀ v, directCount G C.H v < 256 := by
    intro v
    have hv : directCount G C.H v ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    omega
  rcases (show edgeCount G C.P C.Z = 28 ∨
      edgeCount G C.P C.Z = 27 by omega) with hPZ | hPZ
  · let eP : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
    let p := fullySortedFinsetEquiv G.outdegree (directCount G C.H) C.P eP
    have hRows : ∀ i : Nat, (hi : i < 7) →
        directCount G C.Z (p ⟨i, hi⟩).1 =
          if 0 = 1 ∧ i = 0 then 3 else 4 := by
      intro i hi
      simp only [zero_ne_one, false_and, ↓reduceIte]
      exact rows_four_of_edgeCount_eq_twentyEight G C hPCard hZCard hPZ _
        (p ⟨i, hi⟩).2
    have hSorted : ∀ q : Nat, (hq : q < 6) →
        G.outdegree (p ⟨q + 1, by omega⟩).1 ≤
            G.outdegree (p ⟨q, by omega⟩).1 ∧
          (G.outdegree (p ⟨q, by omega⟩).1 =
              G.outdegree (p ⟨q + 1, by omega⟩).1 →
            directCount G C.H (p ⟨q + 1, by omega⟩).1 ≤
              directCount G C.H (p ⟨q, by omega⟩).1) := by
      intro q hq
      have hij : (⟨q, by omega⟩ : Fin 7) ≤ ⟨q + 1, by omega⟩ :=
        Fin.mk_le_mk.mpr (by omega)
      constructor
      · exact fullySorted_degree_anti G.outdegree (directCount G C.H) C.P eP
          hCountLt hij
      · intro heq
        exact fullySorted_hCount_anti_of_degree_eq G.outdegree
          (directCount G C.H) C.P eP
          hij heq
    have hOrder := orderedP_coreBits_true G C hG hPB hEpsilon 0 p h hRows hSorted
    exact impossible_of_compatibleLabels G C hG hMin hNoSeymour hRootDegree
      hk hx hPB hEpsilon hZCard hFullUnion 0 (by omega) (by omega)
      p h hRows hOrder
  · obtain ⟨u, huP, huThree, huUnique⟩ :=
      exists_exceptional_row_of_edgeCount_eq_twentySeven G C hPCard hZCard hPZ
    let eP := finsetEquivFinAtZero C.P hPCard u huP
    let p := sortedFinsetEquiv G.outdegree (directCount G C.H) C.P eP
    have hpZero : (p 0).1 = u := by
      change (sortedFinsetEquiv G.outdegree (directCount G C.H) C.P eP 0).1 = u
      rw [sortedFinsetEquiv_coe, sortedP_zero]
      exact finsetEquivFinAtZero_zero C.P hPCard u huP
    have hRows : ∀ i : Nat, (hi : i < 7) →
        directCount G C.Z (p ⟨i, hi⟩).1 =
          if 1 = 1 ∧ i = 0 then 3 else 4 := by
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simpa [hpZero] using huThree
      · simp only [true_and, if_neg hi0]
        apply huUnique _ (p ⟨i, hi⟩).2
        intro heq
        have hIndex : (⟨i, hi⟩ : Fin 7) = 0 := by
          apply p.injective
          apply Subtype.ext
          simpa [hpZero] using heq
        exact hi0 (Fin.ext_iff.mp hIndex)
    have hSorted : ∀ q : Nat, (hq : q < 5) →
        G.outdegree (p ⟨q + 2, by omega⟩).1 ≤
            G.outdegree (p ⟨q + 1, by omega⟩).1 ∧
          (G.outdegree (p ⟨q + 1, by omega⟩).1 =
              G.outdegree (p ⟨q + 2, by omega⟩).1 →
            directCount G C.H (p ⟨q + 2, by omega⟩).1 ≤
              directCount G C.H (p ⟨q + 1, by omega⟩).1) := by
      intro q hq
      have hij : (⟨q, by omega⟩ : Fin 6) ≤ ⟨q + 1, by omega⟩ :=
        Fin.mk_le_mk.mpr (by omega)
      constructor
      · simpa [p, sortedFinsetEquiv_coe] using
          (sortedP_degree_anti G.outdegree (directCount G C.H)
            (fun j ↦ (eP j).1) hCountLt hij)
      · intro heq
        simpa [p, sortedFinsetEquiv_coe] using
          (sortedP_hCount_anti_of_degree_eq G.outdegree (directCount G C.H)
            (fun j ↦ (eP j).1) hij heq)
    have hOrder := orderedP_coreBits_true G C hG hPB hEpsilon 1 p h hRows hSorted
    exact impossible_of_compatibleLabels G C hG hMin hNoSeymour hRootDegree
      hk hx hPB hEpsilon hZCard hFullUnion 1 (by omega) (by omega)
      p h hRows hOrder

/-- Public graph theorem for the `x = 3`, four-`Z`, external-union-at-least
eight branch. -/
theorem impossible_exactFourZ_unionAtLeastEight (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 3) (hz : C.z = 4)
    (hEpsilon : epsilonS G C = 0)
    (hPZ : 27 ≤ edgeCount G C.P C.Z)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card) : False := by
  have hPB := SeymourEight.BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 4 := by
    change C.Z.card = 4 at hz
    exact hz
  have hHCard : C.H.card = 4 := by
    change C.h = 4
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  exact impossible_unionEight_of_exactCards G C hG hMin hNoSeymour
    hRootDegree hk hx hPB hEpsilon hFullUnion hPZ hPCard hZCard hHCard

end SeymourEight.FourZUnionEightAssembly
