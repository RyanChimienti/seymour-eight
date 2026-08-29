import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoNoRoot.Labels

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Labels

open Shared Shared.CertificateLabels CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def finsetEquivAtZero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    Fin n ≃ {w : V // w ∈ S} :=
  let e := finsetEquivFin S hCard
  (Equiv.swap ⟨0, hn⟩ (e.symm ⟨v, hv⟩)).trans e

omit [Fintype V] [DecidableEq V] in
@[simp] theorem finsetEquivAtZero_zero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    (finsetEquivAtZero S hn hCard v hv ⟨0, hn⟩).1 = v := by
  classical
  simp [finsetEquivAtZero]

noncomputable def finEquivSubtypeOfInjective {n : Nat} (E : Finset V)
    (f : Fin n → V) (hMem : ∀ i, f i ∈ E) (hInj : Function.Injective f)
    (hCard : E.card = n) : Fin n ≃ {v : V // v ∈ E} := by
  let g : Fin n → {v : V // v ∈ E} := fun i => ⟨f i, hMem i⟩
  apply Equiv.ofBijective g
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    exact hInj (congrArg Subtype.val hij)
  · simp [hCard]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem finEquivSubtypeOfInjective_apply {n : Nat} (E : Finset V)
    (f : Fin n → V) (hMem : ∀ i, f i ∈ E) (hInj : Function.Injective f)
    (hCard : E.card = n) (i : Fin n) :
    (finEquivSubtypeOfInjective E f hMem hInj hCard i).1 = f i := rfl

structure ReachedLabels (C : G.LocalConfiguration) (q : V) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  e : Fin 5 → V
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 2, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 3, (a ⟨i.val + 5, by omega⟩).1 ∈ C.R

structure UnreachedLabels (C : G.LocalConfiguration) (q : V) where
  p : Fin 6 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 5 ≃ {v : V // v ∈ C.Z}
  q_mem : q ∈ C.Q
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 2, (a ⟨i.val + 3, by omega⟩).1 ∈ C.X
  a_r : ∀ i : Fin 3, (a ⟨i.val + 5, by omega⟩).1 ∈ C.R

private noncomputable def aEquiv (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 2) (hRCard : C.R.card = 3)
    (hHCard : C.H.card = 4) : Fin 8 ≃ {v : V // v ∈ C.A} :=
  let eA1 := finsetEquivFin C.A1 hAOneCard
  let eX := finsetEquivFin C.X hXCard
  let h := RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX
  let eR := finsetEquivFin C.R hRCard
  RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard h eR

private theorem aEquiv_zero (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 2) (hRCard : C.R.card = 3)
    (hHCard : C.H.card = 4) :
    (aEquiv G C hACard hAOneCard hXCard hRCard hHCard 0).1 = C.a1 := by
  classical
  simp [aEquiv]

private theorem aEquiv_aOne (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 2) (hRCard : C.R.card = 3)
    (hHCard : C.H.card = 4) (i : Fin 2) :
    (aEquiv G C hACard hAOneCard hXCard hRCard hHCard
      ⟨i.val + 1, by omega⟩).1 ∈ C.A1 := by
  let eA1 := finsetEquivFin C.A1 hAOneCard
  let eX := finsetEquivFin C.X hXCard
  let h := RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX
  let eR := finsetEquivFin C.R hRCard
  change (RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard h eR
    ⟨i.val + 1, by omega⟩).1 ∈ C.A1
  rw [show (⟨i.val + 1, by omega⟩ : Fin 8) =
      ⟨i.val + 1, by omega⟩ by rfl,
    RSeven.XTwoNoRoot.Labels.aLabelEquiv_h G C hACard h eR
      ⟨i.val, by omega⟩,
    RSeven.XTwoNoRoot.Labels.hLabelEquiv_aOne G C hHCard eA1 eX i]
  exact (eA1 i).2

private theorem aEquiv_x (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 2) (hRCard : C.R.card = 3)
    (hHCard : C.H.card = 4) (i : Fin 2) :
    (aEquiv G C hACard hAOneCard hXCard hRCard hHCard
      ⟨i.val + 3, by omega⟩).1 ∈ C.X := by
  let eA1 := finsetEquivFin C.A1 hAOneCard
  let eX := finsetEquivFin C.X hXCard
  let h := RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX
  let eR := finsetEquivFin C.R hRCard
  change (RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard h eR
    ⟨i.val + 3, by omega⟩).1 ∈ C.X
  rw [show (⟨i.val + 3, by omega⟩ : Fin 8) =
      ⟨(i.val + 2) + 1, by omega⟩ by ext; simp,
    RSeven.XTwoNoRoot.Labels.aLabelEquiv_h G C hACard h eR
      ⟨i.val + 2, by omega⟩,
    RSeven.XTwoNoRoot.Labels.hLabelEquiv_x G C hHCard eA1 eX i]
  exact (eX i).2

private theorem aEquiv_r (C : G.LocalConfiguration)
    (hACard : C.A.card = 8) (hAOneCard : C.A1.card = 2)
    (hXCard : C.X.card = 2) (hRCard : C.R.card = 3)
    (hHCard : C.H.card = 4) (i : Fin 3) :
    (aEquiv G C hACard hAOneCard hXCard hRCard hHCard
      ⟨i.val + 5, by omega⟩).1 ∈ C.R := by
  simp [aEquiv, RSeven.XTwoNoRoot.Labels.aLabelEquiv]

/-- Build the fixed `a₁,A₁,X,R` layout from caller-chosen labels for the two
interchangeable two-vertex classes.  This is used to put the distinguished
`A₁` witness at index zero of the four-row `H` block. -/
noncomputable def labelsFromEquivs (C : G.LocalConfiguration) (q : V)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) (e : Fin 5 → V) :
    ReachedLabels G C q := by
  let p := finsetEquivFin C.P hPCard
  let h := RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX
  let eR := finsetEquivFin C.R hRCard
  let a := RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard h eR
  refine ⟨p, a, e, ?_, ?_, ?_, ?_⟩
  · exact RSeven.XTwoNoRoot.Labels.aLabelEquiv_zero G C hACard h eR
  · intro i
    rw [RSeven.XTwoNoRoot.Labels.aLabelEquiv_h G C hACard h eR
      ⟨i.val, by omega⟩,
      RSeven.XTwoNoRoot.Labels.hLabelEquiv_aOne G C hHCard eA1 eX i]
    exact (eA1 i).2
  · intro i
    rw [RSeven.XTwoNoRoot.Labels.aLabelEquiv_h G C hACard h eR
      ⟨i.val + 2, by omega⟩,
      RSeven.XTwoNoRoot.Labels.hLabelEquiv_x G C hHCard eA1 eX i]
    exact (eX i).2
  · intro i
    rw [RSeven.XTwoNoRoot.Labels.aLabelEquiv_r G C hACard h eR i]
    exact (eR i).2

@[simp] theorem labelsFromEquivs_aOne (C : G.LocalConfiguration) (q : V)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) (e : Fin 5 → V) (i : Fin 2) :
    ((labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e).a
      ⟨i.val + 1, by omega⟩).1 = (eA1 i).1 := by
  change (RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard
    (RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX)
    (finsetEquivFin C.R hRCard) ⟨i.val + 1, by omega⟩).1 = _
  rw [RSeven.XTwoNoRoot.Labels.aLabelEquiv_h G C hACard _ _
      ⟨i.val, by omega⟩,
    RSeven.XTwoNoRoot.Labels.hLabelEquiv_aOne G C hHCard eA1 eX i]

@[simp] theorem labelsFromEquivs_x (C : G.LocalConfiguration) (q : V)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) (e : Fin 5 → V) (i : Fin 2) :
    ((labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e).a
      ⟨i.val + 3, by omega⟩).1 = (eX i).1 := by
  change (RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard
    (RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX)
    (finsetEquivFin C.R hRCard) ⟨i.val + 3, by omega⟩).1 = _
  rw [RSeven.XTwoNoRoot.Labels.aLabelEquiv_h G C hACard _ _
      ⟨i.val + 2, by omega⟩,
    RSeven.XTwoNoRoot.Labels.hLabelEquiv_x G C hHCard eA1 eX i]

@[simp] theorem labelsFromEquivs_r (C : G.LocalConfiguration) (q : V)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (eA1 : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin 2 ≃ {v : V // v ∈ C.X}) (e : Fin 5 → V) (i : Fin 3) :
    ((labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e).a
      ⟨i.val + 5, by omega⟩).1 = (finsetEquivFin C.R hRCard i).1 := by
  change (RSeven.XTwoNoRoot.Labels.aLabelEquiv G C hACard
    (RSeven.XTwoNoRoot.Labels.hLabelEquiv G C hHCard eA1 eX)
    (finsetEquivFin C.R hRCard) ⟨i.val + 5, by omega⟩).1 = _
  rw [RSeven.XTwoNoRoot.Labels.aLabelEquiv_r G C hACard _ _ i]

def reachedExternalFive (q : V) (z : Fin 4 → V) : Fin 5 → V := fun i =>
  if hi : i.val = 0 then q else z ⟨i.val - 1, by omega⟩

def reachedExternalFour (C : G.LocalConfiguration) (q : V)
    (z : Fin 3 → V) : Fin 5 → V := fun i =>
  if hi0 : i.val = 0 then q
  else if hi4 : i.val = 4 then C.s else z ⟨i.val - 1, by omega⟩

def unreachedExternalFive (z : Fin 5 → V) : Fin 5 → V := z

omit [Fintype V] [DecidableEq V] in
@[simp] theorem reachedExternalFive_zero (q : V) (z : Fin 4 → V) :
    reachedExternalFive q z 0 = q := by
  classical
  simp [reachedExternalFive]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem reachedExternalFive_succ (q : V) (z : Fin 4 → V)
    (i : Fin 4) :
    reachedExternalFive q z ⟨i.val + 1, by omega⟩ = z i := by
  classical
  simp [reachedExternalFive]

omit [DecidableEq V] in
@[simp] theorem reachedExternalFour_zero (C : G.LocalConfiguration)
    (q : V) (z : Fin 3 → V) : reachedExternalFour G C q z 0 = q := by
  classical
  simp [reachedExternalFour]

omit [DecidableEq V] in
@[simp] theorem reachedExternalFour_succ (C : G.LocalConfiguration)
    (q : V) (z : Fin 3 → V) (i : Fin 3) :
    reachedExternalFour G C q z ⟨i.val + 1, by omega⟩ = z i := by
  classical
  simp [reachedExternalFour,
    show i.val + 1 ≠ 4 by omega]

omit [DecidableEq V] in
@[simp] theorem reachedExternalFour_last (C : G.LocalConfiguration)
    (q : V) (z : Fin 3 → V) : reachedExternalFour G C q z 4 = C.s := by
  classical
  simp [reachedExternalFour]

theorem reachedExternalFive_injective (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (z : Fin 4 ≃ {v : V // v ∈ C.Z}) :
    Function.Injective (reachedExternalFive q (fun i => (z i).1)) := by
  have hqZ : q ∉ C.Z := by
    intro hqz
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqz
      (Finset.mem_union_right ({C.s} ∪ C.A)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
  intro i j hij
  apply Fin.ext
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    by_cases hj0 : j.val = 0
    · omega
    · let k : Fin 4 := ⟨j.val - 1, by omega⟩
      have hj : j = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [hj, reachedExternalFive_succ] at hij
      have hij' : q = (z k).1 := by
        simpa only [reachedExternalFive_zero] using hij
      have : q ∈ C.Z := by rw [hij']; exact (z k).2
      exact (hqZ this).elim
  · by_cases hj0 : j.val = 0
    · let k : Fin 4 := ⟨i.val - 1, by omega⟩
      have hi : i = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
      have hj : j = 0 := Fin.ext hj0
      have hleft : reachedExternalFive q (fun i => (z i).1) i = (z k).1 := by
        rw [hi, reachedExternalFive_succ]
      have hright : reachedExternalFive q (fun i => (z i).1) j = q := by
        rw [hj, reachedExternalFive_zero]
      have hij' : (z k).1 = q := hleft.symm.trans (hij.trans hright)
      have : q ∈ C.Z := by rw [← hij']; exact (z k).2
      exact (hqZ this).elim
    · let ki : Fin 4 := ⟨i.val - 1, by omega⟩
      let kj : Fin 4 := ⟨j.val - 1, by omega⟩
      have hi : i = ⟨ki.val + 1, by omega⟩ := Fin.ext (by dsimp [ki]; omega)
      have hj : j = ⟨kj.val + 1, by omega⟩ := Fin.ext (by dsimp [kj]; omega)
      have hleft : reachedExternalFive q (fun i => (z i).1) i = (z ki).1 := by
        rw [hi, reachedExternalFive_succ]
      have hright : reachedExternalFive q (fun i => (z i).1) j = (z kj).1 := by
        rw [hj, reachedExternalFive_succ]
      have hij' : (z ki).1 = (z kj).1 := hleft.symm.trans (hij.trans hright)
      have hk : ki = kj := z.injective (Subtype.ext hij')
      have hval := congrArg Fin.val hk
      dsimp [ki, kj] at hval
      omega

theorem reachedExternalFour_injective (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (z : Fin 3 ≃ {v : V // v ∈ C.Z}) :
    Function.Injective (reachedExternalFour G C q (fun i => (z i).1)) := by
  have hqZ : q ∉ C.Z := by
    intro hqz
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqz
      (Finset.mem_union_right ({C.s} ∪ C.A)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
  have hqS : q ≠ C.s := by
    intro hqs
    apply Digraph.LocalConfiguration.s_notMem_B (G := G) C
    rw [← hqs]
    exact Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ
  intro i j hij
  apply Fin.ext
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    by_cases hj0 : j.val = 0
    · omega
    by_cases hj4 : j.val = 4
    · have hj : j = 4 := Fin.ext hj4
      subst j
      simp only [reachedExternalFour_zero, reachedExternalFour_last] at hij
      exact (hqS hij).elim
    · let k : Fin 3 := ⟨j.val - 1, by omega⟩
      have hj : j = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [hj, reachedExternalFour_succ] at hij
      have hij' : q = (z k).1 := by
        simpa only [reachedExternalFour_zero] using hij
      have hqZ' : q ∈ C.Z := by rw [hij']; exact (z k).2
      exact (hqZ hqZ').elim
  · by_cases hi4 : i.val = 4
    · have hi : i = 4 := Fin.ext hi4
      subst i
      by_cases hj0 : j.val = 0
      · have hj : j = 0 := Fin.ext hj0
        subst j
        simp only [reachedExternalFour_last, reachedExternalFour_zero] at hij
        exact (hqS hij.symm).elim
      by_cases hj4 : j.val = 4
      · omega
      · let k : Fin 3 := ⟨j.val - 1, by omega⟩
        have hj : j = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        rw [hj, reachedExternalFour_succ, reachedExternalFour_last] at hij
        have hsZ : C.s ∈ C.Z := by rw [hij]; exact (z k).2
        exact (Digraph.LocalConfiguration.s_notMem_Z (G := G) C hsZ).elim
    · by_cases hj0 : j.val = 0
      · let k : Fin 3 := ⟨i.val - 1, by omega⟩
        have hi : i = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        have hj : j = 0 := Fin.ext hj0
        rw [hi, hj, reachedExternalFour_succ, reachedExternalFour_zero] at hij
        have hqZ' : q ∈ C.Z := by rw [← hij]; exact (z k).2
        exact (hqZ hqZ').elim
      · by_cases hj4 : j.val = 4
        · let k : Fin 3 := ⟨i.val - 1, by omega⟩
          have hi : i = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
          have hj : j = 4 := Fin.ext hj4
          have hleft : reachedExternalFour G C q (fun i => (z i).1) i = (z k).1 := by
            rw [hi, reachedExternalFour_succ]
          have hright : reachedExternalFour G C q (fun i => (z i).1) j = C.s := by
            rw [hj, reachedExternalFour_last]
          have hij' : (z k).1 = C.s := hleft.symm.trans (hij.trans hright)
          have hsZ : C.s ∈ C.Z := by rw [← hij']; exact (z k).2
          exact (Digraph.LocalConfiguration.s_notMem_Z (G := G) C hsZ).elim
        · let ki : Fin 3 := ⟨i.val - 1, by omega⟩
          let kj : Fin 3 := ⟨j.val - 1, by omega⟩
          have hi : i = ⟨ki.val + 1, by omega⟩ := Fin.ext (by dsimp [ki]; omega)
          have hj : j = ⟨kj.val + 1, by omega⟩ := Fin.ext (by dsimp [kj]; omega)
          have hleft : reachedExternalFour G C q (fun i => (z i).1) i = (z ki).1 := by
            rw [hi, reachedExternalFour_succ]
          have hright : reachedExternalFour G C q (fun i => (z i).1) j = (z kj).1 := by
            rw [hj, reachedExternalFour_succ]
          have hij' : (z ki).1 = (z kj).1 := hleft.symm.trans (hij.trans hright)
          have hk : ki = kj := z.injective (Subtype.ext hij')
          have hval := congrArg Fin.val hk
          dsimp [ki, kj] at hval
          omega

noncomputable def reachedLabels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 2)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (hZCard : C.Z.card = 4) : ReachedLabels G C q := by
  let p := finsetEquivFin C.P hPCard
  let a := aEquiv G C hACard hAOneCard hXCard hRCard hHCard
  let z := finsetEquivFin C.Z hZCard
  have hqNotZ : q ∉ C.Z := by
    intro hqZ
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqZ
      (Finset.mem_union_right ({C.s} ∪ C.A)
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))
  let E := {q} ∪ C.Z
  have hECard : E.card = 5 := by
    rw [Finset.card_union_of_disjoint]
    · simp [hZCard]
    · rw [Finset.disjoint_left]
      intro v hvq hvz
      exact hqNotZ (Finset.mem_singleton.mp hvq ▸ hvz)
  let f : Fin 5 → {v : V // v ∈ E} := fun i =>
    if hi : i.val = 0 then ⟨q, Finset.mem_union_left C.Z (by simp)⟩
    else ⟨(z ⟨i.val - 1, by omega⟩).1,
      Finset.mem_union_right {q} (z _).2⟩
  let e : Fin 5 ≃ {v : V // v ∈ E} := by
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
        simpa [f, show i.val + 1 ≠ 0 by omega] using congrArg Subtype.val hi
    · simp [hECard]
  refine ⟨p, a, (fun i => (e i).1), ?_, ?_, ?_, ?_⟩
  · exact aEquiv_zero G C hACard hAOneCard hXCard hRCard hHCard
  · exact aEquiv_aOne G C hACard hAOneCard hXCard hRCard hHCard
  · exact aEquiv_x G C hACard hAOneCard hXCard hRCard hHCard
  · exact aEquiv_r G C hACard hAOneCard hXCard hRCard hHCard

noncomputable def unreachedLabels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 2)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (hZCard : C.Z.card = 5) : UnreachedLabels G C q :=
  { p := finsetEquivFin C.P hPCard
    a := aEquiv G C hACard hAOneCard hXCard hRCard hHCard
    z := finsetEquivFin C.Z hZCard
    q_mem := hqQ
    a_zero := aEquiv_zero G C hACard hAOneCard hXCard hRCard hHCard
    a_aOne := aEquiv_aOne G C hACard hAOneCard hXCard hRCard hHCard
    a_x := aEquiv_x G C hACard hAOneCard hXCard hRCard hHCard
    a_r := aEquiv_r G C hACard hAOneCard hXCard hRCard hHCard }

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Labels
