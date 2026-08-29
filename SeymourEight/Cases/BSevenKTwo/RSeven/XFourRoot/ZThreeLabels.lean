import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.ZThreeGraphFacts
import SeymourEight.Shared.FinsetBridge
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

/-!
# Canonical labels for the projected three-`Z` cores

The `P` order puts externally deficient rows first and then sorts by the
label-invariant low-core row key.  The `Z` order refines column defect by the
incidence from `p0`; this selects the diagonal representative of the disjoint
two-omission orbit.  Finally all six `H` vertices are sorted by their complete
fourteen-bit `P ↔ H` signature.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeLabels

open Shared XFourNoRoot.ZThreeCore XFourNoRoot.ZThreeBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  h : Fin 6 ≃ {v : V // v ∈ C.H}
  z : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)}

def pExternalDefect (C : G.LocalConfiguration) (v : V) : Nat :=
  3 - directCount G (externalTargets G C) v

def pLowKey (C : G.LocalConfiguration) (v : V) : Nat :=
  65536 * pExternalDefect G C v + 256 * G.outdegree v +
    16 * directCount G C.P v + directCount G C.H v

def pSortPermutation (C : G.LocalConfiguration) (p : Fin 7 → V) :
    Equiv.Perm (Fin 7) :=
  Tuple.sort fun i => OrderDual.toDual (pLowKey G C (p i))

noncomputable def sortedP (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P}) :
    Fin 7 ≃ {v : V // v ∈ C.P} :=
  (pSortPermutation G C (fun i => (eP i).1)).trans eP

theorem sortedP_key_anti (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P}) {i j : Fin 7} (hij : i ≤ j) :
    pLowKey G C (sortedP G C eP i).1 ≥
      pLowKey G C (sortedP G C eP j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (pLowKey G C (eP q).1)) hij

def zIncoming (p : Fin 7 → V) (v : V) : Nat :=
  ∑ i, if G.Adj (p i) v then 1 else 0

def zLabelKey (p : Fin 7 → V) (v : V) : Nat :=
  2 * (7 - zIncoming G p v) + if G.Adj (p 0) v then 0 else 1

def zSortPermutation (p : Fin 7 → V) (z : Fin 3 → V) :
    Equiv.Perm (Fin 3) :=
  Tuple.sort fun i => OrderDual.toDual (zLabelKey G p (z i))

noncomputable def sortedZ (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)}) :
    Fin 3 ≃ {v : V // v ∈ (externalTargets G C)} :=
  (zSortPermutation G p (fun i => (eZ i).1)).trans eZ

theorem sortedZ_key_anti (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)}) {i j : Fin 3} (hij : i ≤ j) :
    zLabelKey G p (sortedZ G p C eZ i).1 ≥
      zLabelKey G p (sortedZ G p C eZ j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (zLabelKey G p (eZ q).1)) hij

def signatureKey : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => signatureKey n f + if f n then 2 ^ n else 0

theorem signatureKey_lt (n : Nat) (f : Nat → Bool) :
    signatureKey n f < 2 ^ n := by
  induction n with
  | zero => simp [signatureKey]
  | succ n ih =>
      simp only [signatureKey, pow_succ]
      cases h : f n <;> simp <;> omega

theorem signatureKey_congr_below (n : Nat) (f g : Nat → Bool)
    (h : ∀ k < n, f k = g k) : signatureKey n f = signatureKey n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [signatureKey]
      rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem lexGe_of_signatureKey_ge (n : Nat) (left right : Nat → Bool)
    (h : signatureKey n right ≤ signatureKey n left) :
    lexGe n left right = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases heq : left n = right n
      · have hLower : signatureKey n right ≤ signatureKey n left := by
          simp only [signatureKey] at h
          rw [heq] at h
          exact Nat.add_le_add_iff_right.mp h
        simp [lexGe, heq, ih hLower]
      · cases hl : left n <;> cases hr : right n
        · exact (heq (by simp [hl, hr])).elim
        · have hLeft := signatureKey_lt n left
          simp [signatureKey, hl, hr] at h
          omega
        · simp [lexGe, hl, hr]
        · exact (heq (by simp [hl, hr])).elim

def hSignature (p : Fin 7 → V) (v : V) (k : Nat) : Bool :=
  if hk : k < 7 then decide (G.Adj (p ⟨k, hk⟩) v)
  else if hk' : k < 14 then decide (G.Adj v (p ⟨k - 7, by omega⟩))
  else false

def hLabelKey (p : Fin 7 → V) (v : V) : Nat :=
  signatureKey 14 (hSignature G p v)

def hSortPermutation (p : Fin 7 → V) (h : Fin 6 → V) :
    Equiv.Perm (Fin 6) :=
  Tuple.sort fun i => OrderDual.toDual (hLabelKey G p (h i))

noncomputable def sortedH (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eH : Fin 6 ≃ {v : V // v ∈ C.H}) :
    Fin 6 ≃ {v : V // v ∈ C.H} :=
  (hSortPermutation G p (fun i => (eH i).1)).trans eH

theorem sortedH_key_anti (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eH : Fin 6 ≃ {v : V // v ∈ C.H}) {i j : Fin 6} (hij : i ≤ j) :
    hLabelKey G p (sortedH G p C eH i).1 ≥
      hLabelKey G p (sortedH G p C eH j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (hLabelKey G p (eH q).1)) hij

noncomputable def canonicalLabels (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) : Labels G C := by
  let eP := finsetEquivFin C.P hPCard
  let p := sortedP G C eP
  let eZ := finsetEquivFin (externalTargets G C) hZCard
  let z := sortedZ G (fun i => (p i).1) C eZ
  let eH := finsetEquivFin C.H hHCard
  let h := sortedH G (fun i => (p i).1) C eH
  exact ⟨p, h, z⟩

theorem canonicalLabels_p_key_anti (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) {i j : Fin 7} (hij : i ≤ j) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    pLowKey G C (L.p i).1 ≥ pLowKey G C (L.p j).1 := by
  exact sortedP_key_anti G C (finsetEquivFin C.P hPCard) hij

theorem canonicalLabels_z_key_anti (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) {i j : Fin 3} (hij : i ≤ j) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    zLabelKey G (fun q => (L.p q).1) (L.z i).1 ≥
      zLabelKey G (fun q => (L.p q).1) (L.z j).1 := by
  exact sortedZ_key_anti G
    (fun q => (sortedP G C (finsetEquivFin C.P hPCard) q).1) C
    (finsetEquivFin (externalTargets G C) hZCard) hij

private abbrev graphBits (C : G.LocalConfiguration) (L : Labels G C) :
    Encoding := coreBits G.Adj (fun i => (L.p i).1) (fun i => (L.h i).1)
      (fun i => (L.z i).1)

theorem phColumnBit_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (h k : Nat) (hh : h < 6) (hk : k < 14) :
    phColumnBit (graphBits G C L) h k =
      hSignature G (fun i => (L.p i).1) (L.h ⟨h, hh⟩).1 k := by
  by_cases hk7 : k < 7
  · rw [phColumnBit, if_pos hk7, pToH_coreBits G.Adj _ _ _ k h hk7 hh]
    simp [hSignature, hk7]
  · have hkSub : k - 7 < 7 := by omega
    rw [phColumnBit, if_neg hk7,
      hToP_coreBits G.Adj _ _ _ h (k - 7) hh hkSub]
    simp [hSignature, hk7, hk]

theorem sortedH_lex (p : Fin 7 → V) (C : G.LocalConfiguration)
    (eH : Fin 6 ≃ {v : V // v ∈ C.H}) (z : Fin 3 → V)
    (q : Nat) (hq : q < 5) :
    lexGe 14
      (phColumnBit (coreBits G.Adj p
        (fun i => (sortedH G p C eH i).1) z) q)
      (phColumnBit (coreBits G.Adj p
        (fun i => (sortedH G p C eH i).1) z) (q + 1)) = true := by
  let h := sortedH G p C eH
  let bits := coreBits G.Adj p (fun i => (h i).1) z
  have hKey := sortedH_key_anti G p C eH
    (i := ⟨q, by omega⟩) (j := ⟨q + 1, by omega⟩)
    (Fin.mk_le_mk.mpr (by omega))
  apply lexGe_of_signatureKey_ge
  have hLeft : signatureKey 14 (phColumnBit bits q) =
      hLabelKey G p (h ⟨q, by omega⟩).1 := by
    rw [hLabelKey]
    apply signatureKey_congr_below
    intro k hk
    by_cases hk7 : k < 7
    · rw [phColumnBit, if_pos hk7,
        pToH_coreBits G.Adj p (fun i => (h i).1) z k q hk7 (by omega)]
      simp [hSignature, hk7]
    · rw [phColumnBit, if_neg hk7,
        hToP_coreBits G.Adj p (fun i => (h i).1) z q (k - 7)
          (by omega) (by omega)]
      simp [hSignature, hk7, hk]
  have hRight : signatureKey 14 (phColumnBit bits (q + 1)) =
      hLabelKey G p (h ⟨q + 1, by omega⟩).1 := by
    rw [hLabelKey]
    apply signatureKey_congr_below
    intro k hk
    by_cases hk7 : k < 7
    · rw [phColumnBit, if_pos hk7,
        pToH_coreBits G.Adj p (fun i => (h i).1) z k (q + 1)
          hk7 (by omega)]
      simp [hSignature, hk7]
    · rw [phColumnBit, if_neg hk7,
        hToP_coreBits G.Adj p (fun i => (h i).1) z (q + 1) (k - 7)
          (by omega) (by omega)]
      simp [hSignature, hk7, hk]
  rw [hLeft, hRight]
  simpa [h] using hKey

theorem canonicalLabels_h_lex (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) (q : Nat) (hq : q < 5) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    lexGe 14 (phColumnBit (graphBits G C L) q)
      (phColumnBit (graphBits G C L) (q + 1)) = true := by
  change lexGe 14
      (phColumnBit (coreBits G.Adj
        (fun i => (sortedP G C (finsetEquivFin C.P hPCard) i).1)
        (fun i => (sortedH G
          (fun j => (sortedP G C (finsetEquivFin C.P hPCard) j).1) C
          (finsetEquivFin C.H hHCard) i).1)
        (fun i => (sortedZ G
          (fun j => (sortedP G C (finsetEquivFin C.P hPCard) j).1) C
          (finsetEquivFin (externalTargets G C) hZCard) i).1)) q)
      (phColumnBit (coreBits G.Adj
        (fun i => (sortedP G C (finsetEquivFin C.P hPCard) i).1)
        (fun i => (sortedH G
          (fun j => (sortedP G C (finsetEquivFin C.P hPCard) j).1) C
          (finsetEquivFin C.H hHCard) i).1)
        (fun i => (sortedZ G
          (fun j => (sortedP G C (finsetEquivFin C.P hPCard) j).1) C
          (finsetEquivFin (externalTargets G C) hZCard) i).1)) (q + 1)) = true
  exact sortedH_lex G
    (fun i => (sortedP G C (finsetEquivFin C.P hPCard) i).1) C
    (finsetEquivFin C.H hHCard)
    (fun i => (sortedZ G
      (fun j => (sortedP G C (finsetEquivFin C.P hPCard) j).1) C
      (finsetEquivFin (externalTargets G C) hZCard) i).1) q hq

end SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeLabels
