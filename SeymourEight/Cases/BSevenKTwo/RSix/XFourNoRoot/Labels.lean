import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.GraphFacts
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLabels
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Labels

open CertificateBridge Shared Core
open RSeven.XFourNoRoot.BroadFourLabels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure LowLabels (C : G.LocalConfiguration) (E : Finset V) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  h : Fin 6 ≃ {v : V // v ∈ C.H}
  e : Fin 3 ≃ {v : V // v ∈ E}
  h_aOne : ∀ i : Fin 2, (h ⟨i.val, by omega⟩).1 ∈ C.A1
  h_x : ∀ i : Fin 4, (h ⟨i.val + 2, by omega⟩).1 ∈ C.X
  e_tail_externalTargets : ∀ i : Fin 2,
    (e ⟨i.val + 1, by omega⟩).1 ∈ externalTargets G C

/-- Swap only the two interchangeable `A₁` labels. -/
noncomputable def swapAOne (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) : LowLabels G C E := by
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  refine ⟨L.p, σ.trans L.h, L.e, ?_, ?_, L.e_tail_externalTargets⟩
  · intro i
    have hi : i = 0 ∨ i = 1 := by
      by_cases h0 : i.val = 0
      · left; exact Fin.ext h0
      · right; apply Fin.ext; omega
    rcases hi with rfl | rfl
    · simpa [σ] using L.h_aOne 1
    · simpa [σ] using L.h_aOne 0
  · intro i
    have h0 : (⟨i.val + 2, by omega⟩ : Fin 6) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      norm_num at this
    have h1 : (⟨i.val + 2, by omega⟩ : Fin 6) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      norm_num at this
      omega
    change (L.h ((Equiv.swap 0 1) ⟨i.val + 2, by omega⟩)).1 ∈ C.X
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    exact L.h_x i

@[simp] theorem swapAOne_p (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) : (swapAOne G C E L).p = L.p := rfl

@[simp] theorem swapAOne_e (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) : (swapAOne G C E L).e = L.e := rfl

@[simp] theorem swapAOne_h_zero (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) : (swapAOne G C E L).h 0 = L.h 1 := by
  simp [swapAOne]

@[simp] theorem swapAOne_h_one (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) : (swapAOne G C E L).h 1 = L.h 0 := by
  simp [swapAOne]

def pKey (C : G.LocalConfiguration) (E : Finset V) (v : V) : Nat :=
  4096 * G.outdegree v + 256 * directCount G E v +
    16 * directCount G C.H v + directCount G C.P v

def pSortPermutation (C : G.LocalConfiguration) (E : Finset V)
    (p : Fin 6 → V) : Equiv.Perm (Fin 6) :=
  Tuple.sort fun i => OrderDual.toDual (pKey G C E (p i))

noncomputable def sortedP (C : G.LocalConfiguration) (E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ C.P}) :
    Fin 6 ≃ {v : V // v ∈ C.P} :=
  (pSortPermutation G C E (fun i => (eP i).1)).trans eP

theorem sortedP_key_anti (C : G.LocalConfiguration) (E : Finset V)
    (eP : Fin 6 ≃ {v : V // v ∈ C.P}) {i j : Fin 6} (hij : i ≤ j) :
    pKey G C E (sortedP G C E eP i).1 ≥
      pKey G C E (sortedP G C E eP j).1 := by
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (pKey G C E (eP q).1)) hij

def eIncoming (p : Fin 6 → V) (v : V) : Nat :=
  ∑ i, if G.Adj (p i) v then 1 else 0

def eSortPermutation {n : Nat} (p : Fin 6 → V) (e : Fin n → V) :
    Equiv.Perm (Fin n) :=
  Tuple.sort fun i => OrderDual.toDual (eIncoming G p (e i))

noncomputable def sortedE {n : Nat} (p : Fin 6 → V) (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) : Fin n ≃ {v : V // v ∈ S} :=
  (eSortPermutation G p (fun i => (e i).1)).trans e

omit [Fintype V] [DecidableEq V] in
theorem sortedE_degree_anti {n : Nat} (p : Fin 6 → V) (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) {i j : Fin n} (hij : i ≤ j) :
    eIncoming G p (sortedE G p S e i).1 ≥
      eIncoming G p (sortedE G p S e j).1 := by
  classical
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (eIncoming G p (e q).1)) hij

noncomputable def canonicalH (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 4) : Fin 6 ≃ {v : V // v ∈ C.H} :=
  hLabelEquiv G C hHCard
    (sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hAOneCard))
    (sortedHFinsetEquiv G C C.X (finsetEquivFin C.X hXCard))

theorem canonicalH_aOne (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 4) (i : Fin 2) :
    (canonicalH G C hHCard hAOneCard hXCard ⟨i.val, by omega⟩).1 ∈ C.A1 := by
  rw [canonicalH, hLabelEquiv_aOne]
  exact (sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hAOneCard) i).2

theorem canonicalH_x (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 4) (i : Fin 4) :
    (canonicalH G C hHCard hAOneCard hXCard ⟨i.val + 2, by omega⟩).1 ∈ C.X := by
  rw [canonicalH, hLabelEquiv_x]
  exact (sortedHFinsetEquiv G C C.X (finsetEquivFin C.X hXCard) i).2

theorem canonicalH_a_order (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 4) :
    hDegreeKey G C (canonicalH G C hHCard hAOneCard hXCard 1).1 ≤
      hDegreeKey G C (canonicalH G C hHCard hAOneCard hXCard 0).1 := by
  let a := sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hAOneCard)
  let x := sortedHFinsetEquiv G C C.X (finsetEquivFin C.X hXCard)
  have h1 : (canonicalH G C hHCard hAOneCard hXCard 1).1 = (a 1).1 := by
    simpa [canonicalH, a, x] using hLabelEquiv_aOne G C hHCard a x 1
  have h0 : (canonicalH G C hHCard hAOneCard hXCard 0).1 = (a 0).1 := by
    simpa [canonicalH, a, x] using hLabelEquiv_aOne G C hHCard a x 0
  rw [h1, h0]
  exact sortedH_key_anti G C C.A1 _ (show (0 : Fin 2) ≤ 1 by decide)

theorem canonicalH_x_order (C : G.LocalConfiguration)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 4) (i : Fin 3) :
    hDegreeKey G C
        (canonicalH G C hHCard hAOneCard hXCard ⟨i.val + 3, by omega⟩).1 ≤
      hDegreeKey G C
        (canonicalH G C hHCard hAOneCard hXCard ⟨i.val + 2, by omega⟩).1 := by
  let a := sortedHFinsetEquiv G C C.A1 (finsetEquivFin C.A1 hAOneCard)
  let x := sortedHFinsetEquiv G C C.X (finsetEquivFin C.X hXCard)
  let j : Fin 4 := ⟨i.val + 1, by omega⟩
  have hj :
      (canonicalH G C hHCard hAOneCard hXCard ⟨i.val + 3, by omega⟩).1 =
        (x j).1 := by
    simpa [canonicalH, a, x, j] using hLabelEquiv_x G C hHCard a x j
  have hi :
      (canonicalH G C hHCard hAOneCard hXCard ⟨i.val + 2, by omega⟩).1 =
        (x ⟨i.val, by omega⟩).1 := by
    simpa [canonicalH, a, x] using
      hLabelEquiv_x G C hHCard a x ⟨i.val, by omega⟩
  rw [hj, hi]
  exact sortedH_key_anti G C C.X _ (Fin.mk_le_mk.mpr (by omega))

noncomputable def unreachedLabels (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 3) : LowLabels G C C.Z := by
  let p := sortedP G C C.Z (finsetEquivFin C.P hPCard)
  let h := canonicalH G C hHCard hAOneCard hXCard
  let e := sortedE G (fun i => (p i).1) C.Z (finsetEquivFin C.Z hZCard)
  refine ⟨p, h, e, ?_, ?_, ?_⟩
  · intro i
    exact canonicalH_aOne G C hHCard hAOneCard hXCard i
  · intro i
    exact canonicalH_x G C hHCard hAOneCard hXCard i
  · intro i
    exact Finset.mem_union_left _ (e ⟨i.val + 1, by omega⟩).2

theorem unreachedLabels_p_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 3) (i : Fin 5) :
    pKey G C C.Z
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).p
          ⟨i.val + 1, by omega⟩).1 ≤
      pKey G C C.Z
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).p
          ⟨i.val, by omega⟩).1 := by
  exact sortedP_key_anti G C C.Z _ (Fin.mk_le_mk.mpr (by omega))

theorem unreachedLabels_a_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 3) :
    hDegreeKey G C
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).h 1).1 ≤
      hDegreeKey G C
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).h 0).1 := by
  exact canonicalH_a_order G C hHCard hAOneCard hXCard

theorem unreachedLabels_x_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 3) (i : Fin 3) :
    hDegreeKey G C
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).h
          ⟨i.val + 3, by omega⟩).1 ≤
      hDegreeKey G C
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).h
          ⟨i.val + 2, by omega⟩).1 := by
  exact canonicalH_x_order G C hHCard hAOneCard hXCard i

theorem unreachedLabels_e_order (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 3) :
    eIncoming G
        (fun i => ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).p i).1)
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).e 2).1 ≤
      eIncoming G
        (fun i => ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).p i).1)
        ((unreachedLabels G C hPCard hHCard hAOneCard hXCard hZCard).e 1).1 := by
  exact sortedE_degree_anti G _ C.Z _ (show (1 : Fin 3) ≤ 2 by decide)

noncomputable def reachedLabels (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) : LowLabels G C ({q} ∪ C.Z) := by
  let E := {q} ∪ C.Z
  let p := sortedP G C E (finsetEquivFin C.P hPCard)
  let h := canonicalH G C hHCard hAOneCard hXCard
  let zRaw := finsetEquivFin C.Z hZCard
  let z := sortedE G (fun i => (p i).1) C.Z zRaw
  let f : Fin 3 → {v : V // v ∈ E} := fun i =>
    if hi : i.val = 0 then ⟨q, Finset.mem_union_left C.Z (by simp)⟩
    else ⟨(z ⟨i.val - 1, by omega⟩).1,
      Finset.mem_union_right {q} (z _).2⟩
  have hqNotZ : q ∉ C.Z := by
    intro hqZ
    exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqZ
        (Finset.mem_union_right ({C.s} ∪ C.A)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
  have hECard : E.card = 3 := by
    rw [Finset.card_union_of_disjoint]
    · simp [hZCard]
    · rw [Finset.disjoint_left]
      intro v hvq hvz
      have hvq' : v = q := Finset.mem_singleton.mp hvq
      exact hqNotZ (hvq' ▸ hvz)
  let e : Fin 3 ≃ {v : V // v ∈ E} := by
    apply Equiv.ofBijective f
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hvq | hvz
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hvq).symm
      · obtain ⟨i, hi⟩ := z.surjective ⟨v, hvz⟩
        refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show i.val + 1 ≠ 0 by omega] using
          congrArg Subtype.val hi
    · simp [hECard]
  refine ⟨p, h, e, ?_, ?_, ?_⟩
  · intro i
    exact canonicalH_aOne G C hHCard hAOneCard hXCard i
  · intro i
    exact canonicalH_x G C hHCard hAOneCard hXCard i
  · intro i
    have hi : i.val + 1 ≠ 0 := by omega
    have heval : (e ⟨i.val + 1, by omega⟩).1 = (z i).1 := by
      simp [e, f]
    rw [heval]
    exact Finset.mem_union_left _ (z i).2

theorem reachedLabels_p_order (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) (i : Fin 5) :
    pKey G C ({q} ∪ C.Z)
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).p
          ⟨i.val + 1, by omega⟩).1 ≤
      pKey G C ({q} ∪ C.Z)
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).p
          ⟨i.val, by omega⟩).1 := by
  exact sortedP_key_anti G C ({q} ∪ C.Z) _ (Fin.mk_le_mk.mpr (by omega))

theorem reachedLabels_a_order (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) :
    hDegreeKey G C
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).h 1).1 ≤
      hDegreeKey G C
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).h 0).1 := by
  exact canonicalH_a_order G C hHCard hAOneCard hXCard

theorem reachedLabels_x_order (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) (i : Fin 3) :
    hDegreeKey G C
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).h
          ⟨i.val + 3, by omega⟩).1 ≤
      hDegreeKey G C
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).h
          ⟨i.val + 2, by omega⟩).1 := by
  exact canonicalH_x_order G C hHCard hAOneCard hXCard i

@[simp] theorem reachedLabels_e_zero (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) :
    ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).e 0).1 = q := by
  rfl

theorem reachedLabels_e_order (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) :
    eIncoming G
        (fun i => ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).p i).1)
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).e 2).1 ≤
      eIncoming G
        (fun i => ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).p i).1)
        ((reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard).e 1).1 := by
  exact sortedE_degree_anti G _ C.Z _ (show (0 : Fin 2) ≤ 1 by decide)

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Labels
