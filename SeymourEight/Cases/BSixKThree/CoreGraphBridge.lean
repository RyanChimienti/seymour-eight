import SeymourEight.Cases.BSixKThree.Counting
import SeymourEight.Certificates.BSixKThree
import SeymourEight.Shared.FinsetBridge

/-!
# Incidence bridge for the `(6,3)` finite cores

The definitions in this file impose the certificate's fixed ordering on the
six local finsets.  External columns may be padded with `false` to embed a
smaller represented target set in a maximal certificate core.
-/

namespace SeymourEight.BSixKThreeCoreGraphBridge

open BSixKThree BSixKThreeCore Shared CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def aLabel {x : Nat} (hx : x ≤ 4) (a1 : V) (a : Fin 3 → V)
    (xv : Fin x → V) (rv : Fin (4 - x) → V) : Fin 8 → V :=
  fun i =>
    if h0 : i.val = 0 then a1
    else if hA : i.val ≤ 3 then a ⟨i.val - 1, by omega⟩
    else if hX : i.val < 4 + x then xv ⟨i.val - 4, by omega⟩
    else rv ⟨i.val - (4 + x), by omega⟩

def bLabel {r : Nat} (hr : r ≤ 6) (p : Fin r → V)
    (q : Fin (6 - r) → V) : Fin 6 → V :=
  fun i => if hi : i.val < r then p ⟨i.val, hi⟩
    else q ⟨i.val - r, by omega⟩

def localLabel {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) : Fin 14 → V :=
  fun i => if hi : i.val < 8 then aLabel hx a1 a xv rv ⟨i.val, hi⟩
    else bLabel hr p q ⟨i.val - 8, by omega⟩

def localAt (label : Fin 14 → V) (i : Nat) : V :=
  label ⟨i % 14, Nat.mod_lt _ (by omega)⟩

def graphArc (label : Fin 14 → V) (i j : Nat) : Bool :=
  decide (G.Adj (localAt label i) (localAt label j))

def graphExternalArc {r actual : Nat} (p : Fin r → V)
    (target : Fin actual → V) (i j : Nat) : Bool :=
  if hi : i < r then
    if hj : j < actual then decide (G.Adj (p ⟨i, hi⟩) (target ⟨j, hj⟩))
    else false
  else false

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem aLabel_zero {x : Nat} (hx : x ≤ 4) (a1 : V) (a : Fin 3 → V)
    (xv : Fin x → V) (rv : Fin (4 - x) → V) :
    aLabel hx a1 a xv rv 0 = a1 := by
  classical
  simp [aLabel]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem aLabel_A1 {x : Nat} (hx : x ≤ 4) (a1 : V) (a : Fin 3 → V)
    (xv : Fin x → V) (rv : Fin (4 - x) → V) (i : Nat) (hi : i < 3) :
    aLabel hx a1 a xv rv ⟨1 + i, by omega⟩ = a ⟨i, hi⟩ := by
  classical
  have h0 : 1 + i ≠ 0 := by omega
  have hA : 1 + i ≤ 3 := by omega
  simp only [aLabel, h0, hA, ↓reduceDIte]
  apply congrArg a
  apply Fin.ext
  change 1 + i - 1 = i
  omega

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem aLabel_X {x : Nat} (hx : x ≤ 4) (a1 : V) (a : Fin 3 → V)
    (xv : Fin x → V) (rv : Fin (4 - x) → V) (i : Nat) (hi : i < x) :
    aLabel hx a1 a xv rv ⟨4 + i, by omega⟩ = xv ⟨i, hi⟩ := by
  classical
  have h0 : 4 + i ≠ 0 := by omega
  have hA : ¬4 + i ≤ 3 := by omega
  have hX : 4 + i < 4 + x := by omega
  simp only [aLabel, h0, hA, hX, ↓reduceDIte]
  apply congrArg xv
  apply Fin.ext
  change 4 + i - 4 = i
  omega

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem aLabel_R {x : Nat} (hx : x ≤ 4) (a1 : V) (a : Fin 3 → V)
    (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (i : Nat) (hi : i < 4 - x) :
    aLabel hx a1 a xv rv ⟨4 + x + i, by omega⟩ = rv ⟨i, hi⟩ := by
  classical
  have h0 : 4 + x + i ≠ 0 := by omega
  have hA : ¬4 + x + i ≤ 3 := by omega
  have hX : ¬4 + x + i < 4 + x := by omega
  simp only [aLabel, h0, hA, hX, ↓reduceDIte]
  apply congrArg rv
  apply Fin.ext
  change 4 + x + i - (4 + x) = i
  omega

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem bLabel_P {r : Nat} (hr : r ≤ 6) (p : Fin r → V)
    (q : Fin (6 - r) → V) (i : Nat) (hi : i < r) :
    bLabel hr p q ⟨i, by omega⟩ = p ⟨i, hi⟩ := by
  classical
  simp [bLabel, hi]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem bLabel_Q {r : Nat} (hr : r ≤ 6) (p : Fin r → V)
    (q : Fin (6 - r) → V) (i : Nat) (hi : i < 6 - r) :
    bLabel hr p q ⟨r + i, by omega⟩ = q ⟨i, hi⟩ := by
  classical
  simp [bLabel]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem localLabel_A {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < 8) :
    localLabel hx hr a1 a xv rv p q ⟨i, by omega⟩ =
      aLabel hx a1 a xv rv ⟨i, hi⟩ := by
  classical
  simp [localLabel, hi]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem localLabel_B {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < 6) :
    localLabel hx hr a1 a xv rv p q ⟨8 + i, by omega⟩ =
      bLabel hr p q ⟨i, hi⟩ := by
  classical
  simp [localLabel]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem localLabel_zero {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) :
    localLabel hx hr a1 a xv rv p q 0 = a1 := by
  classical
  simp [localLabel, aLabel]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem localLabel_A1 {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < 3) :
    localLabel hx hr a1 a xv rv p q ⟨1 + i, by omega⟩ = a ⟨i, hi⟩ := by
  classical
  simp only [localLabel, show 1 + i < 8 by omega, ↓reduceDIte,
    aLabel, show 1 + i ≠ 0 by omega, show 1 + i ≤ 3 by omega]
  apply congrArg a
  apply Fin.ext
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem localLabel_X {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < x) :
    localLabel hx hr a1 a xv rv p q ⟨4 + i, by omega⟩ = xv ⟨i, hi⟩ := by
  classical
  simp only [localLabel, show 4 + i < 8 by omega, ↓reduceDIte,
    aLabel, show 4 + i ≠ 0 by omega, show ¬4 + i ≤ 3 by omega,
    show 4 + i < 4 + x by omega]
  apply congrArg xv
  apply Fin.ext
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem localLabel_R {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < 4 - x) :
    localLabel hx hr a1 a xv rv p q ⟨4 + x + i, by omega⟩ = rv ⟨i, hi⟩ := by
  classical
  simp only [localLabel, show 4 + x + i < 8 by omega, ↓reduceDIte,
    aLabel, show 4 + x + i ≠ 0 by omega, show ¬4 + x + i ≤ 3 by omega,
    show ¬4 + x + i < 4 + x by omega]
  apply congrArg rv
  apply Fin.ext
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem localLabel_P {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < r) :
    localLabel hx hr a1 a xv rv p q ⟨8 + i, by omega⟩ = p ⟨i, hi⟩ := by
  classical
  simp only [localLabel, show ¬8 + i < 8 by omega, ↓reduceDIte,
    bLabel, show 8 + i - 8 < r by omega]
  apply congrArg p
  apply Fin.ext
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem localLabel_Q {x r : Nat} (hx : x ≤ 4) (hr : r ≤ 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (p : Fin r → V) (q : Fin (6 - r) → V) (i : Nat) (hi : i < 6 - r) :
    localLabel hx hr a1 a xv rv p q ⟨8 + r + i, by omega⟩ = q ⟨i, hi⟩ := by
  classical
  simp only [localLabel, show ¬8 + r + i < 8 by omega, ↓reduceDIte,
    bLabel, show ¬8 + r + i - 8 < r by omega]
  apply congrArg q
  apply Fin.ext
  simp
  omega

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem localAt_of_lt (label : Fin 14 → V) (i : Nat) (hi : i < 14) :
    localAt label i = label ⟨i, hi⟩ := by
  classical
  simp [localAt, Nat.mod_eq_of_lt hi]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem graphExternalArc_of_lt {r actual : Nat} (p : Fin r → V)
    (target : Fin actual → V) (i j : Nat) (hi : i < r) (hj : j < actual) :
    graphExternalArc G p target i j =
      decide (G.Adj (p ⟨i, hi⟩) (target ⟨j, hj⟩)) := by
  classical
  simp [graphExternalArc, hi, hj]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem graphExternalArc_of_ge {r actual : Nat} (p : Fin r → V)
    (target : Fin actual → V) (i j : Nat) (hj : actual ≤ j) :
    graphExternalArc G p target i j = false := by
  classical
  simp [graphExternalArc, hj]

theorem allN_eq_true_iff (n : Nat) (f : Nat → Bool) :
    allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
      simp only [allN, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hBefore, hLast⟩ i hi
        by_cases hin : i < n
        · exact hBefore i hin
        · have : i = n := by omega
          simpa [this] using hLast
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

theorem anyN_eq_true_iff (n : Nat) (f : Nat → Bool) :
    anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [anyN]
  | succ n ih =>
      simp only [anyN, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hLast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hLast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · have : i = n := by omega
          exact Or.inr (this ▸ hfi)

theorem anyN_eq_false_of (n : Nat) (f : Nat → Bool)
    (h : ∀ i < n, f i = false) : anyN n f = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [anyN, h n (by omega), Bool.or_false, ih (fun i hi => h i (by omega))]

theorem sumN_congr (n : Nat) (f g : Nat → Bool)
    (h : ∀ i < n, f i = g i) : sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumN, sumN, ih (fun i hi => h i (by omega)), h n (by omega)]

def trueCount (n : Nat) (f : Nat → Bool) : Nat :=
  ((Finset.range n).filter fun i => f i = true).card

theorem trueCount_le (n : Nat) (f : Nat → Bool) : trueCount n f ≤ n := by
  unfold trueCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range n)

theorem toNat_sumN (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (sumN n f).toNat = ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hSumLe : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [sumN, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      have hLt0 : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) < 256 := by
        omega
      have hLt1 : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) + 1 < 256 := by
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
      · simp only [bitCount, ↓reduceIte]
        exact Nat.mod_eq_of_lt hLt1'

theorem toNat_sumN_eq_trueCount (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (sumN n f).toNat = trueCount n f := by
  rw [toNat_sumN n f hn]
  unfold trueCount
  simp only [bitCount]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : f i <;> simp

/-- Decode an iterated sum of bounded byte counts when overflow is impossible. -/
theorem toNat_sumCountsN_of_le (n cap : Nat) (f : Nat → BitVec 8)
    (hTotal : n * cap < 256) (hf : ∀ i < n, (f i).toNat ≤ cap) :
    (sumCountsN n f).toNat = ∑ i ∈ Finset.range n, (f i).toNat := by
  induction n with
  | zero => simp [sumCountsN]
  | succ n ih =>
      rw [Nat.succ_mul] at hTotal
      have hnTotal : n * cap < 256 := by omega
      have hSumLe : (∑ i ∈ Finset.range n, (f i).toNat) ≤ n * cap := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, cap := by
            apply Finset.sum_le_sum
            intro i hi
            exact hf i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
          _ = n * cap := by simp
      rw [sumCountsN, BitVec.toNat_add,
        ih hnTotal (fun i hi => hf i (by omega)), Finset.sum_range_succ]
      apply Nat.mod_eq_of_lt
      have := hf n (by omega)
      omega

theorem trueCount_eq_filter_fin (n : Nat) (f : Nat → Bool) :
    trueCount n f = ((Finset.univ : Finset (Fin n)).filter
      fun i => f i.val = true).card := by
  unfold trueCount
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if f i = true then 1 else 0) n]

theorem trueCount_eq_sum (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    trueCount n f = ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  rw [← toNat_sumN_eq_trueCount n f hn, toNat_sumN n f hn]

set_option linter.flexible false in
theorem trueCount_padded (actual w : Nat) (f : Nat → Bool)
    (hActual : actual ≤ w) (hw : w < 256)
    (hFalse : ∀ j, actual ≤ j → j < w → f j = false) :
    trueCount w f = trueCount actual f := by
  rw [trueCount_eq_sum _ _ hw, trueCount_eq_sum _ _ (by omega),
    show w = actual + (w - actual) by omega, Finset.sum_range_add]
  simp
  intro j hj
  simp [hFalse (actual + j) (by omega) (by omega), bitCount]

theorem toNat_representedSecondCount (r w : Nat)
    (arc externalArc : Nat → Nat → Bool) (u : Nat) (hw : w < 242) :
    (representedSecondCount r w arc externalArc u).toNat =
      trueCount 14 (fun t => decide (t ≠ u) && !arc u t &&
        reachedLocal arc u t) +
      trueCount w (reachedExternal r arc externalArc u) := by
  have hLocal := trueCount_le 14 (fun t => decide (t ≠ u) && !arc u t &&
    reachedLocal arc u t)
  have hExternal := trueCount_le w (reachedExternal r arc externalArc u)
  rw [representedSecondCount, secondLocal, BitVec.toNat_add,
    toNat_sumN_eq_trueCount _ _ (by omega),
    toNat_sumN_eq_trueCount _ _ (by omega)]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  omega

omit [Fintype V] [DecidableEq V] in
theorem two_trueCounts_le_card {n₁ n₂ : Nat} (f₁ f₂ : Nat → Bool)
    (label₁ : Fin n₁ → V) (label₂ : Fin n₂ → V) (S : Finset V)
    (hInjective : Function.Injective
      (Sum.elim label₁ label₂ : Fin n₁ ⊕ Fin n₂ → V))
    (hMem₁ : ∀ i : Fin n₁, f₁ i = true → label₁ i ∈ S)
    (hMem₂ : ∀ i : Fin n₂, f₂ i = true → label₂ i ∈ S) :
    trueCount n₁ f₁ + trueCount n₂ f₂ ≤ S.card := by
  classical
  let label : Fin n₁ ⊕ Fin n₂ → V := Sum.elim label₁ label₂
  let selected : Finset (Fin n₁ ⊕ Fin n₂) :=
    Finset.univ.filter fun q => match q with
      | Sum.inl i => f₁ i = true
      | Sum.inr i => f₂ i = true
  have hCard : selected.card = trueCount n₁ f₁ + trueCount n₂ f₂ := by
    rw [trueCount_eq_filter_fin, trueCount_eq_filter_fin]
    dsimp [selected]
    simp only [Finset.card_filter, Fintype.sum_sum_type]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hfi : f₁ i = true <;> simp [hfi]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hfi : f₂ i = true <;> simp [hfi]
  have hImageCard : (selected.image label).card = selected.card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hInjective hab
  have hImageSubset : selected.image label ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨q, hq, rfl⟩
    have hSelected := (Finset.mem_filter.mp hq).2
    rcases q with i | i
    · exact hMem₁ i hSelected
    · exact hMem₂ i hSelected
  rw [← hCard, ← hImageCard]
  exact Finset.card_le_card hImageSubset

/-- Assemble the common Boolean core from pointwise constraints. -/
theorem core_true_of (r x w : Nat) (arc externalArc : Nat → Nat → Bool)
    (hOriented : ∀ i < 14, arc i i = false ∧
      ∀ j < 14, (decide (i = j) || !(arc i j && arc j i)) = true)
    (hFirst : ∀ j < 14,
      (arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 8 + r)) = true)
    (hA1R : ∀ i < 3, ∀ j < 4 - x, arc (1 + i) (4 + x + j) = false)
    (hPR : ∀ i < r, ∀ j < 4 - x, arc (8 + i) (4 + x + j) = false)
    (hPivotA1 : ∀ i < 3, pivotRow r arc (1 + i) = true)
    (hPivotX : ∀ i < x, pivotRow r arc (4 + i) = true)
    (hDegreeX : ∀ i < x,
      (8 : BitVec 8).toNat ≤ (localOut arc (4 + i)).toNat)
    (hDegreeP : ∀ i < r,
      (8 : BitVec 8).toNat ≤
        (localOut arc (8 + i) + sumN w (externalArc i)).toNat)
    (hSecond : ∀ i < 3,
      (representedSecondCount r w arc externalArc (1 + i)).toNat <
        (localOut arc (1 + i)).toNat) :
    core r x w arc externalArc = true := by
  have h1 : (allN 14 fun i => !arc i i && allN 14 fun j =>
      decide (i = j) || !(arc i j && arc j i)) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    rw [Bool.and_eq_true, allN_eq_true_iff]
    constructor
    · simpa using (hOriented i hi).1
    · exact (hOriented i hi).2
  have h2 : (allN 14 fun j =>
      arc 0 j == decide (1 ≤ j && j ≤ 3 || 8 ≤ j && j < 8 + r)) = true := by
    rw [allN_eq_true_iff]
    exact hFirst
  have h3 : (allN 3 fun i => allN (4 - x) fun j =>
      !arc (1 + i) (4 + x + j)) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    rw [allN_eq_true_iff]
    intro j hj
    simpa using hA1R i hi j hj
  have h4 : (allN r fun i => allN (4 - x) fun j =>
      !arc (8 + i) (4 + x + j)) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    rw [allN_eq_true_iff]
    intro j hj
    simpa using hPR i hi j hj
  have h5 : (allN 3 fun i => pivotRow r arc (1 + i)) = true := by
    rw [allN_eq_true_iff]
    exact hPivotA1
  have h6 : (allN x fun i => pivotRow r arc (4 + i)) = true := by
    rw [allN_eq_true_iff]
    exact hPivotX
  have h7 : (allN x fun i =>
      (8 : BitVec 8).ule (localOut arc (4 + i))) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    simpa only [BitVec.ule_eq_decide, decide_eq_true_eq,
      BitVec.toNat_ofNat] using hDegreeX i hi
  have h8 : (allN r fun i => (8 : BitVec 8).ule
      (localOut arc (8 + i) + sumN w (externalArc i))) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    simpa only [BitVec.ule_eq_decide, decide_eq_true_eq,
      BitVec.toNat_ofNat] using hDegreeP i hi
  have h9 : (allN 3 fun i =>
      (representedSecondCount r w arc externalArc (1 + i)).ult
        (localOut arc (1 + i))) = true := by
    rw [allN_eq_true_iff]
    intro i hi
    simpa only [BitVec.ult_eq_decide, decide_eq_true_eq] using hSecond i hi
  rw [core]
  simpa only [Bool.and_eq_true] using
    ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

/-- The prescribed ordering is an equivalence from `Fin 8` to `A`. -/
noncomputable def aLabelEquiv {x : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hACard : C.A.card = 8)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R}) :
    Fin 8 ≃ {v : V // v ∈ C.A} := by
  let f : Fin 8 → {v : V // v ∈ C.A} := fun i => ⟨
    aLabel hx C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) i, by
        by_cases h0 : i.val = 0
        · simp [aLabel, h0]
        by_cases hA : i.val ≤ 3
        · simpa [aLabel, h0, hA] using
            Digraph.LocalConfiguration.A1_subset_A (G := G) C
              (eA1 ⟨i.val - 1, by omega⟩).2
        by_cases hX : i.val < 4 + x
        · simpa [aLabel, h0, hA, hX] using
            Digraph.LocalConfiguration.X_subset_A (G := G) C
              (eX ⟨i.val - 4, by omega⟩).2
        · simpa [aLabel, h0, hA, hX] using
            Digraph.LocalConfiguration.R_subset_A (G := G) C
              (eR ⟨i.val - (4 + x), by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    have hvParts : v.1 ∈ C.A1 ∪ C.X ∪ {C.a1} ∨ v.1 ∈ C.R := by
      rw [← Finset.mem_union]
      rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
      exact v.2
    rcases hvParts with hvParts | hvR
    · rcases Finset.mem_union.mp hvParts with hvAX | hva1
      · rcases Finset.mem_union.mp hvAX with hvA1 | hvX
        · obtain ⟨i, hi⟩ := eA1.surjective ⟨v.1, hvA1⟩
          refine ⟨⟨1 + i.val, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f] using congrArg Subtype.val hi
        · obtain ⟨i, hi⟩ := eX.surjective ⟨v.1, hvX⟩
          refine ⟨⟨4 + i.val, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f] using congrArg Subtype.val hi
      · have hvEq : v.1 = C.a1 := Finset.mem_singleton.mp hva1
        refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using hvEq.symm
    · obtain ⟨i, hi⟩ := eR.surjective ⟨v.1, hvR⟩
      refine ⟨⟨4 + x + i.val, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
  · simp [hACard]

@[simp]
theorem aLabelEquiv_apply {x : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hACard : C.A.card = 8)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R}) (i : Fin 8) :
    (aLabelEquiv G C hx hACard eA1 eX eR i).1 =
      aLabel hx C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
        (fun j => (eR j).1) i := rfl

/-- The prescribed ordering is an equivalence from `Fin 6` to `B`. -/
noncomputable def bLabelEquiv {r : Nat} (C : G.LocalConfiguration)
    (hr : r ≤ 6) (hBCard : C.B.card = 6)
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q}) :
    Fin 6 ≃ {v : V // v ∈ C.B} := by
  let f : Fin 6 → {v : V // v ∈ C.B} := fun i => ⟨
    bLabel hr (fun j => (eP j).1) (fun j => (eQ j).1) i, by
      by_cases hi : i.val < r
      · simpa [bLabel, hi] using
          Digraph.LocalConfiguration.P_subset_B (G := G) C
            (eP ⟨i.val, hi⟩).2
      · simpa [bLabel, hi] using
          Digraph.LocalConfiguration.Q_subset_B (G := G) C
            (eQ ⟨i.val - r, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    have hv : v.1 ∈ C.P ∪ C.Q := by
      rw [Digraph.LocalConfiguration.P_union_Q (G := G) C]
      exact v.2
    rcases Finset.mem_union.mp hv with hvP | hvQ
    · obtain ⟨i, hi⟩ := eP.surjective ⟨v.1, hvP⟩
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := eQ.surjective ⟨v.1, hvQ⟩
      refine ⟨⟨r + i.val, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
  · simp [hBCard]

@[simp]
theorem bLabelEquiv_apply {r : Nat} (C : G.LocalConfiguration)
    (hr : r ≤ 6) (hBCard : C.B.card = 6)
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q}) (i : Fin 6) :
    (bLabelEquiv G C hr hBCard eP eQ i).1 =
      bLabel hr (fun j => (eP j).1) (fun j => (eQ j).1) i := rfl

/-- Combine the `A` and `B` orderings into the fourteen local labels. -/
noncomputable def localLabelEquiv {x r : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hr : r ≤ 6) (hACard : C.A.card = 8)
    (hBCard : C.B.card = 6)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R})
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q}) :
    Fin 14 ≃ {v : V // v ∈ C.A ∪ C.B} := by
  let eA := aLabelEquiv G C hx hACard eA1 eX eR
  let eB := bLabelEquiv G C hr hBCard eP eQ
  let f : Fin 14 → {v : V // v ∈ C.A ∪ C.B} := fun i =>
    if hi : i.val < 8 then ⟨(eA ⟨i.val, hi⟩).1,
      Finset.mem_union_left C.B (eA ⟨i.val, hi⟩).2⟩
    else ⟨(eB ⟨i.val - 8, by omega⟩).1,
      Finset.mem_union_right C.A (eB ⟨i.val - 8, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro v
    rcases Finset.mem_union.mp v.2 with hvA | hvB
    · obtain ⟨i, hi⟩ := eA.surjective ⟨v.1, hvA⟩
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := eB.surjective ⟨v.1, hvB⟩
      refine ⟨⟨8 + i.val, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
  · rw [Fintype.card_fin, Fintype.card_coe,
      Finset.card_union_of_disjoint
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C), hACard, hBCard]

@[simp]
theorem localLabelEquiv_apply {x r : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hr : r ≤ 6) (hACard : C.A.card = 8)
    (hBCard : C.B.card = 6)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R})
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q}) (i : Fin 14) :
    (localLabelEquiv G C hx hr hACard hBCard eA1 eX eR eP eQ i).1 =
      localLabel hx hr C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
        (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1) i := by
  by_cases hi : i.val < 8
  · simp [localLabelEquiv, localLabel, hi, aLabelEquiv_apply]
  · simp [localLabelEquiv, localLabel, hi, bLabelEquiv_apply]

omit [Fintype V] [DecidableEq V] in
theorem toNat_sumN_equiv {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (u : V) (hnPos : 0 < n) (hn : n < 256) :
    (sumN n (fun i => decide (G.Adj u (e ⟨i % n,
      Nat.mod_lt _ hnPos⟩).1))).toNat = directCount G S u := by
  rw [toNat_sumN n _ hn]
  have hDirect := Shared.directCount_eq_sum_fin G S e u
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : Nat => (bitCount (decide
      (G.Adj u (e ⟨i % n, Nat.mod_lt _ hnPos⟩).1))).toNat) n]
  rw [hDirect]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ⟨i.val % n, Nat.mod_lt i.val hnPos⟩ = i by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt]
  by_cases hAdj : G.Adj u (e i).1 <;> simp [bitCount, hAdj]

theorem toNat_localOut {x r : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hr : r ≤ 6) (hACard : C.A.card = 8)
    (hBCard : C.B.card = 6)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R})
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q}) (u : Nat) (hu : u < 14) :
    let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1)
    (localOut (graphArc G label) u).toNat =
      directCount G (C.A ∪ C.B) (label ⟨u, hu⟩) := by
  dsimp only
  let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
    (fun j => (eX j).1) (fun j => (eR j).1)
    (fun j => (eP j).1) (fun j => (eQ j).1)
  let e := localLabelEquiv G C hx hr hACard hBCard eA1 eX eR eP eQ
  have h := toNat_sumN_equiv G (C.A ∪ C.B) e (label ⟨u, hu⟩)
    (by omega) (by omega)
  rw [localOut]
  rw [← h]
  apply congrArg BitVec.toNat
  apply congrArg (sumN 14)
  funext j
  simp [graphArc, localAt, e, label, localLabelEquiv_apply,
    Nat.mod_eq_of_lt hu]

omit [Fintype V] [DecidableEq V] in
theorem toNat_externalRow {r actual w : Nat} (P W : Finset V)
    (eP : Fin r ≃ {v : V // v ∈ P})
    (eW : Fin actual ≃ {v : V // v ∈ W})
    (hActual : actual ≤ w) (i : Nat) (hi : i < r) (hw : w < 256) :
    (sumN w (graphExternalArc G (fun j => (eP j).1)
      (fun j => (eW j).1) i)).toNat = directCount G W (eP ⟨i, hi⟩).1 := by
  classical
  by_cases hPos : 0 < actual
  · have hActualDecode := toNat_sumN_equiv G W eW (eP ⟨i, hi⟩).1
      hPos (by omega)
    rw [← hActualDecode, toNat_sumN _ _ hw,
      toNat_sumN _ _ (by omega)]
    rw [show w = actual + (w - actual) by omega, Finset.sum_range_add]
    have hTail : (∑ j ∈ Finset.range (w - actual),
        (bitCount (graphExternalArc G (fun j => (eP j).1)
          (fun j => (eW j).1) i (actual + j))).toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp [graphExternalArc, show ¬actual + j < actual by omega, bitCount]
    rw [hTail, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [graphExternalArc_of_lt G _ _ i j hi hj']
    simp [Nat.mod_eq_of_lt hj']
  · have hZero : actual = 0 := by omega
    subst actual
    have hWCard : W.card = 0 := by
      simpa using (Fintype.card_congr eW).symm
    have hDirectZero : directCount G W (eP ⟨i, hi⟩).1 = 0 := by
      unfold directCount internalFirstNeighbors
      have hle := Finset.card_le_card (Finset.filter_subset (G.Adj (eP ⟨i, hi⟩).1) W)
      omega
    rw [hDirectZero, toNat_sumN _ _ hw]
    apply Finset.sum_eq_zero
    intro j hj
    simp [graphExternalArc, bitCount]

omit [DecidableEq V] in
theorem outdegree_eq_directCount_of_captured (u : V) (S : Finset V)
    (hCaptured : G.outNeighborFinset u ⊆ S) :
    G.outdegree u = directCount G S u := by
  classical
  unfold Digraph.outdegree directCount internalFirstNeighbors
  apply congrArg Finset.card
  ext v
  simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter]
  constructor
  · intro huv
    exact ⟨hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩
  · exact fun h => h.2

theorem outdegree_H_eq_local (C : G.LocalConfiguration) (hG : G.IsOriented)
    (u : V) (hu : u ∈ C.H) :
    G.outdegree u = directCount G (C.A ∪ C.B) u :=
  outdegree_eq_directCount_of_captured G u _
    (BSixKThree.H_outgoingCaptured_general G C hG u hu)

theorem disjoint_local_external (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    Disjoint (C.A ∪ C.B) (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvAB hvW
  rcases Finset.mem_union.mp hvAB with hvA | hvB
  · rcases Finset.mem_union.mp hvW with hvZ | hvRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
          (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
        exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 (hs ▸ hvA)
      · simp [rootSecondFinset, hReach] at hvRoot
  · exact (Finset.disjoint_left.mp
      (BSixKThree.disjoint_B_externalTargets G C)) hvB hvW

theorem outdegree_P_eq_local_external (C : G.LocalConfiguration)
    (hG : G.IsOriented) (p : V) (hp : p ∈ C.P) :
    G.outdegree p = directCount G (C.A ∪ C.B) p +
      directCount G (externalTargets G C) p := by
  have hCaptured := BSixKThree.P_outgoingCaptured_general G C hG p hp
  have hCaptured' : G.outNeighborFinset p ⊆
      (C.A ∪ C.B) ∪ externalTargets G C := by
    intro v hv
    have h := hCaptured hv
    rcases Finset.mem_union.mp h with hLocal | hW
    · rcases Finset.mem_union.mp hLocal with hHP | hQ
      · rcases Finset.mem_union.mp hHP with hH | hP
        · exact Finset.mem_union_left _ (Finset.mem_union_left C.B
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hH))
        · exact Finset.mem_union_left _ (Finset.mem_union_right C.A
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hP))
      · exact Finset.mem_union_left _ (Finset.mem_union_right C.A
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hQ))
    · exact Finset.mem_union_right _ hW
  have hDisjoint := disjoint_local_external G C hG
  rw [outdegree_eq_directCount_of_captured G p _ hCaptured',
    Shared.directCount_union_of_disjoint G (C.A ∪ C.B)
      (externalTargets G C) p hDisjoint]

theorem A1_not_adj_R (C : G.LocalConfiguration) (_hG : G.IsOriented)
    (u v : V) (hu : u ∈ C.A1) (hv : v ∈ C.R) : ¬G.Adj u v := by
  intro huv
  have hvX : v ∈ C.X := Finset.mem_inter.mpr ⟨
    (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      ⟨u, Finset.mem_union_left C.P hu, huv⟩,
    Finset.mem_sdiff.mpr ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hv,
      by
        intro hvOld
        rcases Finset.mem_union.mp hvOld with hvA1 | hva1
        · exact (Finset.mem_sdiff.mp hv).2
            (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hvA1))
        · exact (Finset.mem_sdiff.mp hv).2
            (Finset.mem_union_right (C.A1 ∪ C.X) hva1)⟩⟩
  exact (Finset.mem_sdiff.mp hv).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hvX))

theorem P_not_adj_R (C : G.LocalConfiguration) (p v : V)
    (hp : p ∈ C.P) (hv : v ∈ C.R) : ¬G.Adj p v := by
  intro hpv
  have hvX : v ∈ C.X := Finset.mem_inter.mpr ⟨
    (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      ⟨p, Finset.mem_union_right C.A1 hp, hpv⟩,
    Finset.mem_sdiff.mpr ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hv,
      by
        intro hvOld
        exact (Finset.mem_sdiff.mp hv).2 (by
          rcases Finset.mem_union.mp hvOld with hvA1 | hva1
          · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hvA1)
          · exact Finset.mem_union_right (C.A1 ∪ C.X) hva1)⟩⟩
  exact (Finset.mem_sdiff.mp hv).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hvX))

theorem toNat_internalA {x r : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hr : r ≤ 6) (hACard : C.A.card = 8)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R})
    (p : Fin r → V) (q : Fin (6 - r) → V) (u : Nat) (hu : u < 14) :
    let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1) p q
    (internalA (graphArc G label) u).toNat =
      directCount G C.A (label ⟨u, hu⟩) := by
  dsimp only
  let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
    (fun j => (eX j).1) (fun j => (eR j).1) p q
  let eA := aLabelEquiv G C hx hACard eA1 eX eR
  have h := toNat_sumN_equiv G C.A eA (label ⟨u, hu⟩)
    (by omega) (by omega)
  rw [internalA, ← h]
  apply congrArg BitVec.toNat
  apply sumN_congr
  intro j hj
  rw [graphArc, localAt_of_lt _ u hu, localAt_of_lt _ j (by omega)]
  rw [localLabel_A hx hr C.a1 (fun j => (eA1 j).1)
    (fun j => (eX j).1) (fun j => (eR j).1) p q j hj]
  simp [label, eA, aLabelEquiv_apply, Nat.mod_eq_of_lt hj]

theorem toNat_outB {x r : Nat} (C : G.LocalConfiguration)
    (hx : x ≤ 4) (hr : r ≤ 6) (hBCard : C.B.card = 6)
    (a1 : V) (a : Fin 3 → V) (xv : Fin x → V) (rv : Fin (4 - x) → V)
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q}) (u : Nat) (hu : u < 14) :
    let label := localLabel hx hr a1 a xv rv (fun j => (eP j).1)
      (fun j => (eQ j).1)
    (outB (graphArc G label) u).toNat =
      directCount G C.B (label ⟨u, hu⟩) := by
  dsimp only
  let label := localLabel hx hr a1 a xv rv (fun j => (eP j).1)
    (fun j => (eQ j).1)
  let eB := bLabelEquiv G C hr hBCard eP eQ
  have h := toNat_sumN_equiv G C.B eB (label ⟨u, hu⟩)
    (by omega) (by omega)
  rw [outB, ← h]
  apply congrArg BitVec.toNat
  apply sumN_congr
  intro j hj
  rw [graphArc, localAt_of_lt _ u hu,
    localAt_of_lt _ (8 + j) (by omega)]
  rw [localLabel_B hx hr a1 a xv rv (fun j => (eP j).1)
    (fun j => (eQ j).1) j hj]
  simp [label, eB, bLabelEquiv_apply, Nat.mod_eq_of_lt hj]

/-- Every second neighbor counted by the local and (unpadded) external blocks
is a genuine strict second neighbor in the graph. -/
theorem representedSecondCount_le_secondOutdegree {x r actual w : Nat}
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hx : x ≤ 4) (hr : r ≤ 6) (hACard : C.A.card = 8)
    (hBCard : C.B.card = 6) (hActual : actual ≤ w) (hw : w < 242)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R})
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q})
    (eW : Fin actual ≃ {v : V // v ∈ externalTargets G C})
    (u : Nat) (hu : u < 3) :
    let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1)
    let arc := graphArc G label
    let externalArc := graphExternalArc G (fun j => (eP j).1)
      (fun j => (eW j).1)
    (representedSecondCount r w arc externalArc (1 + u)).toNat ≤
      G.secondOutdegree (eA1 ⟨u, hu⟩).1 := by
  dsimp only
  let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
    (fun j => (eX j).1) (fun j => (eR j).1)
    (fun j => (eP j).1) (fun j => (eQ j).1)
  let arc := graphArc G label
  let externalArc := graphExternalArc G (fun j => (eP j).1)
    (fun j => (eW j).1)
  let source := (eA1 ⟨u, hu⟩).1
  have hSource : label ⟨1 + u, by omega⟩ = source := by
    rw [show label ⟨1 + u, by omega⟩ =
      aLabel hx C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
        (fun j => (eR j).1) ⟨1 + u, by omega⟩ by
      exact localLabel_A hx hr C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1)
        (fun j => (eP j).1) (fun j => (eQ j).1) (1 + u) (by omega)]
    exact aLabel_A1 hx C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1) u hu
  rw [toNat_representedSecondCount r w arc externalArc (1 + u) hw]
  have hPad : trueCount w (reachedExternal r arc externalArc (1 + u)) =
      trueCount actual (reachedExternal r arc externalArc (1 + u)) := by
    apply trueCount_padded actual w _ hActual (by omega)
    intro j hj hjw
    rw [reachedExternal]
    have hPoint : ∀ i < r, externalArc i j = false := by
      intro i hi
      simp [externalArc, hj]
    apply anyN_eq_false_of
    intro i hi
    simp [hPoint i hi]
  rw [hPad]
  change _ ≤ (G.secondOutNeighborFinset source).card
  let eLocal := localLabelEquiv G C hx hr hACard hBCard eA1 eX eR eP eQ
  have hInjective : Function.Injective
      (Sum.elim label (fun j : Fin actual => (eW j).1) :
        Fin 14 ⊕ Fin actual → V) := by
    apply Sum.elim_injective.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      apply eLocal.injective
      apply Subtype.ext
      simpa [eLocal, label, localLabelEquiv_apply] using hij
    · intro i j hij
      exact eW.injective (Subtype.ext hij)
    · intro i j hij
      have hiMem : label i ∈ C.A ∪ C.B := by
        have := (eLocal i).2
        simpa [eLocal, label, localLabelEquiv_apply] using this
      exact (Finset.disjoint_left.mp (disjoint_local_external G C hG))
        hiMem (hij ▸ (eW j).2)
  apply two_trueCounts_le_card
    (label₁ := label) (label₂ := fun j : Fin actual => (eW j).1)
    (hInjective := hInjective)
  · intro target hSelected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hSelected
    rcases hSelected with ⟨⟨hTargetNe, hNotArc⟩, hReached⟩
    rw [reachedLocal, anyN_eq_true_iff] at hReached
    rcases hReached with ⟨middle, hm, hPath⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
    rcases hPath with ⟨⟨⟨_, _⟩, hsm⟩, hmt⟩
    have hsm' : G.Adj source (label ⟨middle, hm⟩) := by
      change decide (G.Adj (localAt label (1 + u))
        (localAt label middle)) = true at hsm
      rw [decide_eq_true_eq, localAt_of_lt _ (1 + u) (by omega),
        localAt_of_lt _ middle hm, hSource] at hsm
      exact hsm
    have hmt' : G.Adj (label ⟨middle, hm⟩) (label target) := by
      change decide (G.Adj (localAt label middle)
        (localAt label target)) = true at hmt
      rw [decide_eq_true_eq, localAt_of_lt _ middle hm,
        localAt_of_lt _ target target.isLt] at hmt
      exact hmt
    have hNotDirect : ¬G.Adj source (label target) := by
      intro hst
      have : arc (1 + u) target = true := by
        change decide (G.Adj (localAt label (1 + u))
          (localAt label target)) = true
        rw [decide_eq_true_eq, localAt_of_lt _ (1 + u) (by omega),
          localAt_of_lt _ target target.isLt, hSource]
        exact hst
      simp [this] at hNotArc
    have hTargetSource : label target ≠ source := by
      intro hEq
      have hIdx : target = ⟨1 + u, by omega⟩ := by
        have hSum := hInjective (show
          Sum.elim label (fun j : Fin actual => (eW j).1) (Sum.inl target) =
            Sum.elim label (fun j : Fin actual => (eW j).1)
              (Sum.inl ⟨1 + u, by omega⟩) by
          simpa [hSource] using hEq)
        exact Sum.inl.inj hSum
      exact hTargetNe (Fin.ext_iff.mp hIdx)
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨label ⟨middle, hm⟩, hsm', hmt'⟩, hNotDirect, hTargetSource⟩
  · intro target hReached
    rw [reachedExternal, anyN_eq_true_iff] at hReached
    rcases hReached with ⟨middle, hm, hPath⟩
    simp only [Bool.and_eq_true] at hPath
    rcases hPath with ⟨hsm, hmt⟩
    have hsm' : G.Adj source (eP ⟨middle, hm⟩).1 := by
      have hPLabel : label ⟨8 + middle, by omega⟩ = (eP ⟨middle, hm⟩).1 := by
        rw [show label ⟨8 + middle, by omega⟩ =
          bLabel hr (fun j => (eP j).1) (fun j => (eQ j).1)
            ⟨middle, by omega⟩ by
          exact localLabel_B hx hr C.a1 (fun j => (eA1 j).1)
            (fun j => (eX j).1) (fun j => (eR j).1)
            (fun j => (eP j).1) (fun j => (eQ j).1) middle (by omega)]
        exact bLabel_P hr (fun j => (eP j).1) (fun j => (eQ j).1) middle hm
      change decide (G.Adj (localAt label (1 + u))
        (localAt label (8 + middle))) = true at hsm
      rw [decide_eq_true_eq, localAt_of_lt _ (1 + u) (by omega),
        localAt_of_lt _ (8 + middle) (by omega), hSource, hPLabel] at hsm
      exact hsm
    have hmt' : G.Adj (eP ⟨middle, hm⟩).1 (eW target).1 := by
      simpa [externalArc, graphExternalArc, hm, target.isLt] using hmt
    have hNoDirect : ¬G.Adj source (eW target).1 := by
      intro hst
      have hCaptured := BSixKThree.H_outgoingCaptured_general G C hG source
        (Finset.mem_union_left C.X (eA1 ⟨u, hu⟩).2)
      have hLocal := hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr hst)
      exact (Finset.disjoint_left.mp (disjoint_local_external G C hG))
        hLocal (eW target).2
    have hTargetSource : (eW target).1 ≠ source := by
      intro hEq
      have := hInjective (show
        Sum.elim label (fun j : Fin actual => (eW j).1) (Sum.inr target) =
          Sum.elim label (fun j : Fin actual => (eW j).1)
            (Sum.inl ⟨1 + u, by omega⟩) by
        simpa [hSource] using hEq)
      exact Sum.inr_ne_inl this
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨_, hsm', hmt'⟩, hNoDirect, hTargetSource⟩

theorem toNat_localOut_add_external (arc externalArc : Nat → Nat → Bool)
    (w i ei : Nat) (hw : w ≤ 20) :
    (localOut arc i + sumN w (externalArc ei)).toNat =
      (localOut arc i).toNat + (sumN w (externalArc ei)).toNat := by
  have hLocal := trueCount_le 14 (arc i)
  have hExternal := trueCount_le w (externalArc ei)
  rw [localOut, BitVec.toNat_add,
    toNat_sumN_eq_trueCount _ _ (by omega),
    toNat_sumN_eq_trueCount _ _ (by omega)]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  omega

/-- A labelled graph configuration satisfying a surviving parameter row
produces a satisfying assignment of the common finite core. -/
theorem core_of_graphData {x r actual w : Nat} (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 6) (hk : C.k = 3)
    (hxEq : C.x = x) (hrEq : C.r = r)
    (_hActualCard : (externalTargets G C).card = actual)
    (hActual : actual ≤ w) (hw : w ≤ 20)
    (eA1 : Fin 3 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eR : Fin (4 - x) ≃ {v : V // v ∈ C.R})
    (eP : Fin r ≃ {v : V // v ∈ C.P})
    (eQ : Fin (6 - r) ≃ {v : V // v ∈ C.Q})
    (eW : Fin actual ≃ {v : V // v ∈ externalTargets G C}) :
    let hx : x ≤ 4 := by
      have := BSixKThree.x_le_four G C hG hRootDegree hk
      omega
    let hr : r ≤ 6 := by
      have hle := Finset.card_le_card
        (Digraph.LocalConfiguration.P_subset_B (G := G) C)
      change C.r ≤ C.B.card at hle
      omega
    let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1)
    core r x w (graphArc G label)
      (graphExternalArc G (fun j => (eP j).1) (fun j => (eW j).1)) = true := by
  dsimp only
  have hx : x ≤ 4 := by
    have := BSixKThree.x_le_four G C hG hRootDegree hk
    omega
  have hr : r ≤ 6 := by
    have hle := Finset.card_le_card
      (Digraph.LocalConfiguration.P_subset_B (G := G) C)
    change C.r ≤ C.B.card at hle
    omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hRCard : C.R.card = 4 - x := by
    have := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hQCard : C.Q.card = 6 - r := by
    have := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  let label := localLabel hx hr C.a1 (fun j => (eA1 j).1)
    (fun j => (eX j).1) (fun j => (eR j).1)
    (fun j => (eP j).1) (fun j => (eQ j).1)
  let arc := graphArc G label
  let externalArc := graphExternalArc G (fun j => (eP j).1)
    (fun j => (eW j).1)
  have hLabel0 : label 0 = C.a1 := by
    exact localLabel_zero hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1)
  have hLabelA1 (i : Nat) (hi : i < 3) :
      label ⟨1 + i, by omega⟩ = (eA1 ⟨i, hi⟩).1 := by
    exact localLabel_A1 hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelX (i : Nat) (hi : i < x) :
      label ⟨4 + i, by omega⟩ = (eX ⟨i, hi⟩).1 := by
    exact localLabel_X hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelR (i : Nat) (hi : i < 4 - x) :
      label ⟨4 + x + i, by omega⟩ = (eR ⟨i, hi⟩).1 := by
    exact localLabel_R hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelP (i : Nat) (hi : i < r) :
      label ⟨8 + i, by omega⟩ = (eP ⟨i, hi⟩).1 := by
    exact localLabel_P hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have hLabelQ (i : Nat) (hi : i < 6 - r) :
      label ⟨8 + r + i, by omega⟩ = (eQ ⟨i, hi⟩).1 := by
    exact localLabel_Q hx hr C.a1 (fun j => (eA1 j).1)
      (fun j => (eX j).1) (fun j => (eR j).1)
      (fun j => (eP j).1) (fun j => (eQ j).1) i hi
  have ha1Adj : ∀ v, G.Adj C.a1 v ↔ v ∈ C.A1 ∪ C.P := by
    intro v
    rw [← Digraph.mem_outNeighborFinset,
      Shared.outNeighborFinset_a1_eq_A1_union_P G C hG]
  apply core_true_of r x w arc externalArc
  · intro i hi
    constructor
    · change decide (G.Adj (localAt label i) (localAt label i)) = false
      rw [decide_eq_false_iff_not]
      simpa [localAt_of_lt _ i hi] using hG.1 (label ⟨i, hi⟩)
    · intro j hj
      by_cases hij : i = j
      · simp [hij]
      · by_cases hForward : G.Adj (label ⟨i, hi⟩) (label ⟨j, hj⟩)
        · have hReverse := hG.2 hForward
          simp [arc, graphArc, localAt_of_lt _ i hi, localAt_of_lt _ j hj,
            hij, hForward, hReverse]
        · simp [arc, graphArc, localAt_of_lt _ i hi, localAt_of_lt _ j hj,
            hij, hForward]
  · intro j hj
    have hIff : G.Adj C.a1 (label ⟨j, hj⟩) ↔
        (1 ≤ j ∧ j ≤ 3 ∨ 8 ≤ j ∧ j < 8 + r) := by
      by_cases h0 : j = 0
      · subst j
        have hn := hG.1 C.a1
        simp [hLabel0, hn]
      by_cases hA1 : j ≤ 3
      · have hj3 : j - 1 < 3 := by omega
        have hLab : label ⟨j, hj⟩ = (eA1 ⟨j - 1, hj3⟩).1 := by
          have hidx : (⟨j, hj⟩ : Fin 14) =
              ⟨1 + (j - 1), by omega⟩ := by
            apply Fin.ext
            change j = 1 + (j - 1)
            omega
          rw [hidx]
          exact hLabelA1 (j - 1) hj3
        rw [hLab, ha1Adj]
        constructor
        · intro _
          exact Or.inl ⟨by omega, by omega⟩
        · intro _
          exact Finset.mem_union_left C.P (eA1 _).2
      by_cases hA : j < 8
      · have hNot : ¬G.Adj C.a1 (label ⟨j, hj⟩) := by
          intro hadj
          have hMem := (ha1Adj _).mp hadj
          rcases Finset.mem_union.mp hMem with hvA1 | hvP
          · by_cases hXj : j < 4 + x
            · have hxj : j - 4 < x := by omega
              have hLab : label ⟨j, hj⟩ = (eX ⟨j - 4, hxj⟩).1 := by
                have hidx : (⟨j, hj⟩ : Fin 14) =
                    ⟨4 + (j - 4), by omega⟩ := by
                  apply Fin.ext
                  change j = 4 + (j - 4)
                  omega
                rw [hidx]
                exact hLabelX (j - 4) hxj
              exact (Finset.disjoint_left.mp
                (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hvA1
                  (hLab ▸ (eX _).2)
            · have hrj : j - (4 + x) < 4 - x := by omega
              have hLab : label ⟨j, hj⟩ = (eR ⟨j - (4 + x), hrj⟩).1 := by
                have hidx : (⟨j, hj⟩ : Fin 14) =
                    ⟨4 + x + (j - (4 + x)), by omega⟩ := by
                  apply Fin.ext
                  change j = 4 + x + (j - (4 + x))
                  omega
                rw [hidx]
                exact hLabelR (j - (4 + x)) hrj
              exact (Finset.mem_sdiff.mp (eR _).2).2 (by
                exact Finset.mem_union_left {C.a1}
                  (Finset.mem_union_left C.X (hLab ▸ hvA1)))
          · have hvB := Digraph.LocalConfiguration.P_subset_B (G := G) C hvP
            have hvA : label ⟨j, hj⟩ ∈ C.A := by
              let eA := aLabelEquiv G C hx hACard eA1 eX eR
              have hm := (eA ⟨j, hA⟩).2
              have hval : (eA ⟨j, hA⟩).1 = label ⟨j, hj⟩ := by
                rw [aLabelEquiv_apply]
                symm
                exact localLabel_A hx hr C.a1 (fun j => (eA1 j).1)
                  (fun j => (eX j).1) (fun j => (eR j).1)
                  (fun j => (eP j).1) (fun j => (eQ j).1) j hA
              exact hval ▸ hm
            exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA hvB
        simp [hNot]
        omega
      by_cases hPj : j < 8 + r
      · have hpj : j - 8 < r := by omega
        have hLab : label ⟨j, hj⟩ = (eP ⟨j - 8, hpj⟩).1 := by
          have hidx : (⟨j, hj⟩ : Fin 14) =
              ⟨8 + (j - 8), by omega⟩ := by
            apply Fin.ext
            change j = 8 + (j - 8)
            omega
          rw [hidx]
          exact hLabelP (j - 8) hpj
        rw [hLab, ha1Adj]
        constructor
        · intro _
          exact Or.inr ⟨by omega, by omega⟩
        · intro _
          exact Finset.mem_union_right C.A1 (eP _).2
      · have hqj : j - (8 + r) < 6 - r := by omega
        have hLab : label ⟨j, hj⟩ = (eQ ⟨j - (8 + r), hqj⟩).1 := by
          have hidx : (⟨j, hj⟩ : Fin 14) =
              ⟨8 + r + (j - (8 + r)), by omega⟩ := by
            apply Fin.ext
            change j = 8 + r + (j - (8 + r))
            omega
          rw [hidx]
          exact hLabelQ (j - (8 + r)) hqj
        have hNot : ¬G.Adj C.a1 (label ⟨j, hj⟩) := by
          intro hadj
          rcases Finset.mem_union.mp ((ha1Adj _).mp hadj) with hvA1 | hvP
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
                (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA1)
                (Digraph.LocalConfiguration.Q_subset_B (G := G) C (hLab ▸ (eQ _).2))
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
                (hLab ▸ (eQ _).2)
        simp [hNot]
        omega
    simp [arc, graphArc,
      localAt_of_lt _ j hj, hLabel0, hIff]
  · intro i hi j hj
    have hA1Mem : label ⟨1 + i, by omega⟩ ∈ C.A1 := by
      rw [hLabelA1 i hi]
      exact (eA1 ⟨i, hi⟩).2
    have hRMem : label ⟨4 + x + j, by omega⟩ ∈ C.R := by
      rw [hLabelR j hj]
      exact (eR ⟨j, hj⟩).2
    change decide (G.Adj (localAt label (1 + i))
      (localAt label (4 + x + j))) = false
    rw [decide_eq_false_iff_not, localAt_of_lt _ (1 + i) (by omega),
      localAt_of_lt _ (4 + x + j) (by omega)]
    exact A1_not_adj_R G C hG _ _ hA1Mem hRMem
  · intro i hi j hj
    have hPMem : label ⟨8 + i, by omega⟩ ∈ C.P := by
      rw [hLabelP i hi]
      exact (eP ⟨i, hi⟩).2
    have hRMem : label ⟨4 + x + j, by omega⟩ ∈ C.R := by
      rw [hLabelR j hj]
      exact (eR ⟨j, hj⟩).2
    change decide (G.Adj (localAt label (8 + i))
      (localAt label (4 + x + j))) = false
    rw [decide_eq_false_iff_not, localAt_of_lt _ (8 + i) (by omega),
      localAt_of_lt _ (4 + x + j) (by omega)]
    exact P_not_adj_R G C _ _ hPMem hRMem
  · intro i hi
    have hMem : (eA1 ⟨i, hi⟩).1 ∈ C.A1 := (eA1 ⟨i, hi⟩).2
    have hp := hPivot _
      (Digraph.LocalConfiguration.A1_subset_A (G := G) C hMem)
    rw [pivotRow]
    simp only [Bool.and_eq_true, Bool.or_eq_true, BitVec.ule_eq_decide,
      BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [toNat_internalA G C hx hr hACard eA1 eX eR
      (fun j => (eP j).1) (fun j => (eQ j).1) (1 + i) (by omega),
      toNat_outB G C hx hr hBCard C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1) eP eQ (1 + i) (by omega),
      localLabel_A1 hx hr C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1)
        (fun j => (eP j).1) (fun j => (eQ j).1) i hi]
    have hA : 3 ≤ directCount G C.A (eA1 ⟨i, hi⟩).1 := by
      simpa [directCount, internalFirstNeighbors, hk] using hp.1
    constructor
    · simpa [BitVec.toNat_ofNat] using hA
    · by_cases hEq : directCount G C.A (eA1 ⟨i, hi⟩).1 = 3
      · right
        have := hp.2 (by simpa [directCount, internalFirstNeighbors, hk] using hEq)
        simpa [directCount, internalFirstNeighbors, hrEq,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r < 256)] using this
      · left
        have hlt : 3 < directCount G C.A (eA1 ⟨i, hi⟩).1 := by omega
        simpa [BitVec.toNat_ofNat] using hlt
  · intro i hi
    have hMemX : (eX ⟨i, hi⟩).1 ∈ C.X := (eX ⟨i, hi⟩).2
    have hp := hPivot _ (Digraph.LocalConfiguration.X_subset_A (G := G) C hMemX)
    rw [pivotRow]
    simp only [Bool.and_eq_true, Bool.or_eq_true, BitVec.ule_eq_decide,
      BitVec.ult_eq_decide, decide_eq_true_eq]
    rw [toNat_internalA G C hx hr hACard eA1 eX eR
      (fun j => (eP j).1) (fun j => (eQ j).1) (4 + i) (by omega),
      toNat_outB G C hx hr hBCard C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1) eP eQ (4 + i) (by omega),
      localLabel_X hx hr C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1)
        (fun j => (eP j).1) (fun j => (eQ j).1) i hi]
    have hA : 3 ≤ directCount G C.A (eX ⟨i, hi⟩).1 := by
      simpa [directCount, internalFirstNeighbors, hk] using hp.1
    constructor
    · simpa [BitVec.toNat_ofNat] using hA
    · by_cases hEq : directCount G C.A (eX ⟨i, hi⟩).1 = 3
      · right
        have := hp.2 (by simpa [directCount, internalFirstNeighbors, hk] using hEq)
        simpa [directCount, internalFirstNeighbors, hrEq,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r < 256)] using this
      · left
        have hlt : 3 < directCount G C.A (eX ⟨i, hi⟩).1 := by omega
        simpa [BitVec.toNat_ofNat] using hlt
  · intro i hi
    rw [toNat_localOut G C hx hr hACard hBCard eA1 eX eR eP eQ
      (4 + i) (by omega),
      localLabel_X hx hr C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1)
        (fun j => (eP j).1) (fun j => (eQ j).1) i hi]
    have hMemX : (eX ⟨i, hi⟩).1 ∈ C.X := (eX ⟨i, hi⟩).2
    rw [← outdegree_H_eq_local G C hG _ (Finset.mem_union_right C.A1 hMemX)]
    simpa using hMin (eX ⟨i, hi⟩).1
  · intro i hi
    rw [toNat_localOut_add_external arc externalArc w (8 + i) i hw,
      toNat_localOut G C hx hr hACard hBCard eA1 eX eR eP eQ
        (8 + i) (by omega),
      toNat_externalRow G C.P (externalTargets G C) eP eW hActual i hi (by omega),
      localLabel_P hx hr C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1)
        (fun j => (eP j).1) (fun j => (eQ j).1) i hi]
    have hPMem : (eP ⟨i, hi⟩).1 ∈ C.P := (eP ⟨i, hi⟩).2
    rw [← outdegree_P_eq_local_external G C hG _ hPMem]
    simpa using hMin (eP ⟨i, hi⟩).1
  · intro i hi
    have hRep := representedSecondCount_le_secondOutdegree G C hG hx hr
      hACard hBCard hActual (by omega) eA1 eX eR eP eQ eW i hi
    have hMemA1 : (eA1 ⟨i, hi⟩).1 ∈ C.A1 := (eA1 ⟨i, hi⟩).2
    have hLabel : label ⟨1 + i, by omega⟩ = (eA1 ⟨i, hi⟩).1 := by
      exact hLabelA1 i hi
    have hNot : ¬G.IsSeymourVertex (eA1 ⟨i, hi⟩).1 := by
      intro hS
      exact hNoSeymour ⟨_, hS⟩
    have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
    rw [toNat_localOut G C hx hr hACard hBCard eA1 eX eR eP eQ
      (1 + i) (by omega),
      localLabel_A1 hx hr C.a1 (fun j => (eA1 j).1)
        (fun j => (eX j).1) (fun j => (eR j).1)
        (fun j => (eP j).1) (fun j => (eQ j).1) i hi,
      ← outdegree_H_eq_local G C hG _ (Finset.mem_union_left C.X hMemA1)]
    exact lt_of_le_of_lt hRep hStrict

end SeymourEight.BSixKThreeCoreGraphBridge
