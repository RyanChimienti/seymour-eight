import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.LowCoreBridge
import SeymourEight.Shared.CertificateLabels

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XFourRoot.Labels

open Shared Shared.CertificateLabels CertificateBridge
open RSix.XFourNoRoot RSix.XFourNoRoot.Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def unreachedLabels (C : G.LocalConfiguration)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hECard : (externalTargets G C).card = 3) :
    LowLabels G C (externalTargets G C) := by
  let p := sortedP G C (externalTargets G C) (finsetEquivFin C.P hPCard)
  let h := canonicalH G C hHCard hAOneCard hXCard
  let e := sortedE G (fun i => (p i).1) (externalTargets G C)
    (finsetEquivFin (externalTargets G C) hECard)
  exact ⟨p, h, e,
    canonicalH_aOne G C hHCard hAOneCard hXCard,
    canonicalH_x G C hHCard hAOneCard hXCard,
    fun i => (e ⟨i.val + 1, by omega⟩).2⟩

noncomputable def reachedLabels (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hECard : (externalTargets G C).card = 2) :
    LowLabels G C ({q} ∪ externalTargets G C) := by
  let E := {q} ∪ externalTargets G C
  let p := sortedP G C E (finsetEquivFin C.P hPCard)
  let h := canonicalH G C hHCard hAOneCard hXCard
  let eRaw := finsetEquivFin (externalTargets G C) hECard
  let eTail := sortedE G (fun i => (p i).1) (externalTargets G C) eRaw
  let f : Fin 3 → {v : V // v ∈ E} := fun i =>
    if hi : i.val = 0 then
      ⟨q, Finset.mem_union_left _ (by simp)⟩
    else
      ⟨(eTail ⟨i.val - 1, by omega⟩).1,
        Finset.mem_union_right _ (eTail _).2⟩
  have hqB : q ∈ C.B :=
    Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ
  have hqNotE : q ∉ externalTargets G C := fun hqE =>
    (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C)) hqB hqE
  have hCard : E.card = 3 := by
    rw [Finset.card_union_of_disjoint]
    · simp [hECard]
    · rw [Finset.disjoint_left]
      intro v hvq hvE
      exact hqNotE (Finset.mem_singleton.mp hvq ▸ hvE)
  let e : Fin 3 ≃ {v : V // v ∈ E} := by
    apply Equiv.ofBijective f
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hvq | hvE
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using (Finset.mem_singleton.mp hvq).symm
      · obtain ⟨i, hi⟩ := eTail.surjective ⟨v, hvE⟩
        refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show i.val + 1 ≠ 0 by omega] using congrArg Subtype.val hi
    · simp [hCard]
  refine ⟨p, h, e,
    canonicalH_aOne G C hHCard hAOneCard hXCard,
    canonicalH_x G C hHCard hAOneCard hXCard, ?_⟩
  intro i
  have hi : i.val + 1 ≠ 0 := by omega
  have heval : (e ⟨i.val + 1, by omega⟩).1 = (eTail i).1 := by
    simp [e, f]
  rw [heval]
  exact (eTail i).2

end SeymourEight.BSevenKTwo.RSix.XFourRoot.Labels
