import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.TerminalCoreGraphBridge
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

/-! Canonical finite label utilities for the exact-seven four-`Z` branch. -/

namespace SeymourEight.FourZExactSevenLabels

open Shared TerminalCoreBridge TerminalCoreGraphBridge

variable {V : Type*}

/-! The common `A = {a1} ∪ H ∪ R` labels. -/

noncomputable def aLabelEquiv (G : Digraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (eR : Fin 3 ≃ {v : V // v ∈ C.R}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i =>
    if hi0 : i.val = 0 then ⟨C.a1, C.a1_mem_root_outNeighbors⟩
    else if hiH : i.val ≤ 4 then
      ⟨(h ⟨i.val - 1, by omega⟩).1,
        Digraph.LocalConfiguration.H_subset_A (G := G) C
          (h ⟨i.val - 1, by omega⟩).2⟩
    else
      ⟨(eR ⟨i.val - 5, by omega⟩).1,
        Digraph.LocalConfiguration.R_subset_A (G := G) C
          (eR ⟨i.val - 5, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    have hvAll : v.1 ∈ (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R := by
      rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
      exact v.2
    rcases Finset.mem_union.mp hvAll with hvParts | hvR
    · rcases Finset.mem_union.mp hvParts with hvAX | hva1
      · rcases Finset.mem_union.mp hvAX with hvA1 | hvX
        · obtain ⟨i, hi⟩ := h.surjective
            ⟨v.1, Finset.mem_union_left C.X hvA1⟩
          refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show i.val + 1 ≠ 0 by omega,
            show i.val + 1 ≤ 4 by omega] using congrArg Subtype.val hi
        · obtain ⟨i, hi⟩ := h.surjective
            ⟨v.1, Finset.mem_union_right C.A1 hvX⟩
          refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, show i.val + 1 ≠ 0 by omega,
            show i.val + 1 ≤ 4 by omega] using congrArg Subtype.val hi
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hva1).symm
    · obtain ⟨i, hi⟩ := eR.surjective ⟨v.1, hvR⟩
      refine ⟨⟨i.val + 5, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 5 ≤ 4 by omega] using congrArg Subtype.val hi
  · simp [hACard]

@[simp] theorem aLabelEquiv_zero (G : Digraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (eR : Fin 3 ≃ {v : V // v ∈ C.R}) :
    (aLabelEquiv G C hACard h eR 0).1 = C.a1 := by rfl

@[simp] theorem aLabelEquiv_h (G : Digraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (eR : Fin 3 ≃ {v : V // v ∈ C.R})
    (j : Fin 4) :
    (aLabelEquiv G C hACard h eR ⟨j.val + 1, by omega⟩).1 = (h j).1 := by
  simp [aLabelEquiv,
    show j.val + 1 ≤ 4 by omega]

@[simp] theorem aLabelEquiv_r (G : Digraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (C : G.LocalConfiguration) (hACard : C.A.card = 8)
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (eR : Fin 3 ≃ {v : V // v ∈ C.R})
    (j : Fin 3) :
    (aLabelEquiv G C hACard h eR ⟨j.val + 5, by omega⟩).1 = (eR j).1 := by
  simp [aLabelEquiv,
    show ¬j.val + 5 ≤ 4 by omega, show j.val + 5 - 5 = j.val by omega]

/-- Sort all seven labels in descending lexicographic order by
`(degree,H-count)`.  The radix is safe because the secondary count is at most
four (the generic statement only asks for `<256`). -/
def allSortPermutation (degree hCount : V → Nat) (p : Fin 7 → V) :
    Equiv.Perm (Fin 7) :=
  Tuple.sort (fun i ↦ descendingKey degree hCount (p i))

def sortedAllP (degree hCount : V → Nat) (p : Fin 7 → V) : Fin 7 → V :=
  p ∘ allSortPermutation degree hCount p

theorem sortedAllP_bijective (degree hCount : V → Nat) (p : Fin 7 → V)
    (hp : Function.Bijective p) :
    Function.Bijective (sortedAllP degree hCount p) :=
  hp.comp (allSortPermutation degree hCount p).bijective

theorem sortedAllP_key_anti (degree hCount : V → Nat) (p : Fin 7 → V)
    {i j : Fin 7} (hij : i ≤ j) :
    256 * degree (sortedAllP degree hCount p i) +
        hCount (sortedAllP degree hCount p i) ≥
      256 * degree (sortedAllP degree hCount p j) +
        hCount (sortedAllP degree hCount p j) := by
  exact Tuple.monotone_sort
    (fun k ↦ descendingKey degree hCount (p k)) hij

theorem sortedAllP_degree_anti (degree hCount : V → Nat) (p : Fin 7 → V)
    (hCountLt : ∀ v, hCount v < 256) {i j : Fin 7} (hij : i ≤ j) :
    degree (sortedAllP degree hCount p j) ≤
      degree (sortedAllP degree hCount p i) := by
  have hk := sortedAllP_key_anti degree hCount p hij
  have hi := hCountLt (sortedAllP degree hCount p i)
  have hj := hCountLt (sortedAllP degree hCount p j)
  omega

theorem sortedAllP_hCount_anti_of_degree_eq
    (degree hCount : V → Nat) (p : Fin 7 → V) {i j : Fin 7} (hij : i ≤ j)
    (hDegree : degree (sortedAllP degree hCount p i) =
      degree (sortedAllP degree hCount p j)) :
    hCount (sortedAllP degree hCount p j) ≤
      hCount (sortedAllP degree hCount p i) := by
  have hk := sortedAllP_key_anti degree hCount p hij
  omega

noncomputable def sortedAllFinsetEquiv (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P}) :
    Fin 7 ≃ {v : V // v ∈ P} :=
  (allSortPermutation degree hCount (fun i ↦ (eP i).1)).trans eP

@[simp] theorem sortedAllFinsetEquiv_coe (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P}) (i : Fin 7) :
    (sortedAllFinsetEquiv degree hCount P eP i).1 =
      sortedAllP degree hCount (fun j ↦ (eP j).1) i := rfl

/-- Adjacent graph keys are sorted for the no-missing case. -/
theorem sortedAllFinsetEquiv_order (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P})
    (hCountLt : ∀ v, hCount v < 256) :
    ∀ (q : Nat) (hq : q < 6),
      degree (sortedAllFinsetEquiv degree hCount P eP ⟨q + 1, by omega⟩).1 ≤
          degree (sortedAllFinsetEquiv degree hCount P eP ⟨q, by omega⟩).1 ∧
        (degree (sortedAllFinsetEquiv degree hCount P eP ⟨q, by omega⟩).1 =
            degree (sortedAllFinsetEquiv degree hCount P eP ⟨q + 1, by omega⟩).1 →
          hCount (sortedAllFinsetEquiv degree hCount P eP ⟨q + 1, by omega⟩).1 ≤
            hCount (sortedAllFinsetEquiv degree hCount P eP ⟨q, by omega⟩).1) := by
  intro q hq
  constructor
  · have ht := sortedAllP_degree_anti degree hCount (fun i ↦ (eP i).1)
      hCountLt (i := ⟨q, by omega⟩) (j := ⟨q + 1, by omega⟩)
        (by simp only [Fin.mk_le_mk]; omega)
    simpa only [sortedAllFinsetEquiv_coe] using ht
  · intro heq
    have ht := sortedAllP_hCount_anti_of_degree_eq degree hCount
      (fun i ↦ (eP i).1) (i := ⟨q, by omega⟩) (j := ⟨q + 1, by omega⟩)
      (by simp only [Fin.mk_le_mk]; omega)
      (by simpa only [sortedAllFinsetEquiv_coe] using heq)
    simpa only [sortedAllFinsetEquiv_coe] using ht

/-- Adjacent graph keys are sorted after label zero for the one-missing case. -/
theorem sortedTailFinsetEquiv_order (degree hCount : V → Nat)
    (P : Finset V) (eP : Fin 7 ≃ {v : V // v ∈ P})
    (hCountLt : ∀ v, hCount v < 256) :
    ∀ (q : Nat) (hq : q < 5),
      degree (sortedFinsetEquiv degree hCount P eP ⟨q + 2, by omega⟩).1 ≤
          degree (sortedFinsetEquiv degree hCount P eP ⟨q + 1, by omega⟩).1 ∧
        (degree (sortedFinsetEquiv degree hCount P eP ⟨q + 1, by omega⟩).1 =
            degree (sortedFinsetEquiv degree hCount P eP ⟨q + 2, by omega⟩).1 →
          hCount (sortedFinsetEquiv degree hCount P eP ⟨q + 2, by omega⟩).1 ≤
            hCount (sortedFinsetEquiv degree hCount P eP ⟨q + 1, by omega⟩).1) := by
  intro q hq
  constructor
  · have ht := sortedP_degree_anti degree hCount (fun i ↦ (eP i).1)
      hCountLt (i := ⟨q, by omega⟩) (j := ⟨q + 1, by omega⟩)
        (by simp only [Fin.mk_le_mk]; omega)
    simpa only [sortedFinsetEquiv_coe, Fin.succ_mk] using ht
  · intro heq
    have ht := sortedP_hCount_anti_of_degree_eq degree hCount
      (fun i ↦ (eP i).1) (i := ⟨q, by omega⟩) (j := ⟨q + 1, by omega⟩)
      (by simp only [Fin.mk_le_mk]; omega)
      (by simpa only [sortedFinsetEquiv_coe, Fin.succ_mk] using heq)
    simpa only [sortedFinsetEquiv_coe, Fin.succ_mk] using ht

end SeymourEight.FourZExactSevenLabels
