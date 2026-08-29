import SeymourEight.Shared.FinsetBridge
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Shared canonical label helpers

Finite obstruction certificates routinely sort an interchangeable vertex
class by a graph-invariant numeric key.  This module packages that operation
once, independently of any certificate layout.
-/

namespace SeymourEight.Shared.CertificateLabels

open CertificateBridge

variable {V : Type*}

def sortPermutation {n : Nat} (key : V → Nat) (e : Fin n → V) :
    Equiv.Perm (Fin n) :=
  Tuple.sort fun i => OrderDual.toDual (key (e i))

noncomputable def sortedFinsetEquiv {n : Nat} (key : V → Nat)
    (S : Finset V) (e : Fin n ≃ {v : V // v ∈ S}) :
    Fin n ≃ {v : V // v ∈ S} :=
  (sortPermutation key (fun i => (e i).1)).trans e

theorem sorted_key_anti {n : Nat} (key : V → Nat) (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) {i j : Fin n} (hij : i ≤ j) :
    key (sortedFinsetEquiv key S e i).1 ≥
      key (sortedFinsetEquiv key S e j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (key (e q).1)) hij

end SeymourEight.Shared.CertificateLabels
