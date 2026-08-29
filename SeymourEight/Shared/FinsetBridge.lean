import SeymourEight.Shared.ArcCounting
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false

/-!
# Shared finite-set bridges

Small adapters for transporting graph counts across equivalences with `Fin n`.
-/

namespace SeymourEight.Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Canonically label an `n`-element finset by `Fin n`. -/
noncomputable def finsetEquivFin {n : Nat} (S : Finset V) (hCard : S.card = n) :
    Fin n ≃ {v : V // v ∈ S} :=
  (finCongr hCard.symm).trans S.equivFin.symm

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem finsetEquivFin_mem {n : Nat} (S : Finset V) (hCard : S.card = n)
    (i : Fin n) : (finsetEquivFin S hCard i).1 ∈ S :=
  (finsetEquivFin S hCard i).2

omit [Fintype V] [DecidableEq V] in
/-- Reindex an ordinary direct-neighbor count through a finset equivalence. -/
theorem directCount_eq_sum_fin {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (u : V) :
    directCount G S u =
      ∑ i : Fin n, if decide (G.Adj u (e i).1) then 1 else 0 := by
  classical
  calc
    directCount G S u = ∑ v ∈ S, if G.Adj u v then 1 else 0 := by
      simp [directCount, CertificateBridge.internalFirstNeighbors]
    _ = ∑ x : {v : V // v ∈ S}, if G.Adj u x.1 then 1 else 0 := by
      symm
      rw [show (Finset.univ : Finset {v : V // v ∈ S}) = S.attach by
        exact Finset.univ_eq_attach S]
      exact S.sum_attach (fun v ↦ if G.Adj u v then 1 else 0)
    _ = ∑ x : {v : V // v ∈ S},
        if decide (G.Adj u x.1) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : G.Adj u x.1 <;> simp [hx]
    _ = ∑ i : Fin n, if decide (G.Adj u (e i).1) then 1 else 0 := by
      exact (Equiv.sum_comp e (fun x : {v : V // v ∈ S} ↦
        if decide (G.Adj u x.1) then 1 else 0)).symm

omit [Fintype V] [DecidableEq V] in
/-- Reindex the tails in an edge count by a finite equivalence. -/
theorem edgeCount_eq_sum_fin {n : Nat} (S T : Finset V)
    (eS : Fin n ≃ {v : V // v ∈ S}) :
    edgeCount G S T = ∑ i : Fin n, directCount G T (eS i).1 := by
  classical
  unfold edgeCount
  calc
    (∑ u ∈ S, directCount G T u) =
        ∑ x : {v : V // v ∈ S}, directCount G T x.1 := by
      symm
      rw [show (Finset.univ : Finset {v : V // v ∈ S}) = S.attach by
        exact Finset.univ_eq_attach S]
      exact S.sum_attach (fun u ↦ directCount G T u)
    _ = ∑ i : Fin n, directCount G T (eS i).1 := by
      exact (Equiv.sum_comp eS
        (fun x : {v : V // v ∈ S} ↦ directCount G T x.1)).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Reindex a finset sum through an equivalence with its subtype. -/
theorem sum_finset_eq_sum_fin {n : Nat} (S : Finset V)
    (eS : Fin n ≃ {v : V // v ∈ S}) (f : V → Nat) :
    ∑ v ∈ S, f v = ∑ i : Fin n, f (eS i).1 := by
  classical
  calc
    (∑ v ∈ S, f v) = ∑ x : {v : V // v ∈ S}, f x.1 := by
      symm
      rw [show (Finset.univ : Finset {v : V // v ∈ S}) = S.attach by
        exact Finset.univ_eq_attach S]
      exact S.sum_attach f
    _ = ∑ i : Fin n, f (eS i).1 := by
      exact (Equiv.sum_comp eS (fun x : {v : V // v ∈ S} ↦ f x.1)).symm

omit [Fintype V] [DecidableEq V] in
/-- Reindex the cardinality of a filtered finset. -/
theorem filterCard_eq_sum_fin {n : Nat} (S : Finset V)
    (eS : Fin n ≃ {v : V // v ∈ S}) (Q : V → Prop) [DecidablePred Q] :
    (S.filter Q).card = ∑ i : Fin n, if Q (eS i).1 then 1 else 0 := by
  classical
  calc
    (S.filter Q).card = ∑ v ∈ S, if Q v then 1 else 0 := by simp
    _ = ∑ x : {v : V // v ∈ S}, if Q x.1 then 1 else 0 := by
      symm
      rw [show (Finset.univ : Finset {v : V // v ∈ S}) = S.attach by
        exact Finset.univ_eq_attach S]
      exact S.sum_attach (fun v ↦ if Q v then 1 else 0)
    _ = ∑ i : Fin n, if Q (eS i).1 then 1 else 0 := by
      exact (Equiv.sum_comp eS
        (fun x : {v : V // v ∈ S} ↦ if Q x.1 then 1 else 0)).symm

omit [Fintype V] [DecidableEq V] in
/-- Count a finset through any Boolean row that exactly recognizes its arcs. -/
theorem directCount_eq_sum_bool {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (u : V) (b : Fin n → Bool)
    (hb : ∀ i, b i = true ↔ G.Adj u (e i).1) :
    directCount G S u = ∑ i : Fin n, if b i then 1 else 0 := by
  rw [directCount_eq_sum_fin G S e]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hbi : b i = true
  · have hadj := (hb i).mp hbi
    simp [hbi, hadj]
  · have hadj : ¬G.Adj u (e i).1 := by
      intro hadj
      exact hbi ((hb i).mpr hadj)
    have hbFalse : b i = false := Bool.eq_false_of_not_eq_true hbi
    simp [hbFalse, hadj]

end SeymourEight.Shared
