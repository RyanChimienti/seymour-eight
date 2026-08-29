import SeymourEight.Cases.BSixKThree.XFourBridge

/-! # Closure of the `(|B|, k) = (6, 3)` leaf -/

namespace SeymourEight.BSixKThree

open Shared BSixKThreeCore BSixKThreeCoreGraphBridge

/-- The fully checked `(6,3)` leaf. -/
theorem bSixKThreeCase : BSixKThreeCase := by
  intro V _ _ _hBound G _ C hG hMin hRoot hPivot hBCard hk
  by_contra hNoSeymour
  have hA1Card : C.A1.card = 3 := by
    simpa [Digraph.LocalConfiguration.k] using hk
  have hRows := parameterRows G C hG hMin hNoSeymour hRoot hPivot hBCard hk
  rcases hRows with row | row | row | row
  · rcases row with ⟨hr, hx, hw⟩
    have hRCard : C.R.card = 2 := by
      have := card_R_eq_four_sub_x G C hG hRoot hk
      omega
    have hQCard : C.Q.card = 1 := by
      have := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
      omega
    have hPCard : C.P.card = 5 := hr
    have hWLe : (externalTargets G C).card ≤ 4 := by
      rw [Shared.card_externalTargets G C]
      exact hw
    let eA1 := finsetEquivFin C.A1 hA1Card
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eR := finsetEquivFin C.R hRCard
    let eP := finsetEquivFin C.P hPCard
    let eQ := finsetEquivFin C.Q hQCard
    let eW := finsetEquivFin (externalTargets G C) rfl
    let label := localLabel (by omega : 2 ≤ 4) (by omega : 5 ≤ 6)
      C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1)
    let arc := graphArc G label
    let externalArc := graphExternalArc G (fun j => (eP j).1)
      (fun j => (eW j).1)
    have hTrue : core 5 2 4 arc externalArc = true := by
      simpa [arc, externalArc, label] using
        core_of_graphData G C hG hMin hNoSeymour hPivot hRoot hBCard hk
          hx hr rfl hWLe (by omega) eA1 eX eR eP eQ eW
    have hFalse := rFiveXTwoCore_unsat arc externalArc
    rw [hFalse] at hTrue
    contradiction
  · rcases row with ⟨hr, hx, hw⟩
    have hRCard : C.R.card = 2 := by
      have := card_R_eq_four_sub_x G C hG hRoot hk
      omega
    have hQCard : C.Q.card = 0 := by
      have := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
      omega
    have hPCard : C.P.card = 6 := hr
    have hWLe : (externalTargets G C).card ≤ 6 := by
      rw [Shared.card_externalTargets G C]
      exact hw
    let eA1 := finsetEquivFin C.A1 hA1Card
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eR := finsetEquivFin C.R hRCard
    let eP := finsetEquivFin C.P hPCard
    let eQ := finsetEquivFin C.Q hQCard
    let eW := finsetEquivFin (externalTargets G C) rfl
    let label := localLabel (by omega : 2 ≤ 4) (by omega : 6 ≤ 6)
      C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1)
    let arc := graphArc G label
    let externalArc := graphExternalArc G (fun j => (eP j).1)
      (fun j => (eW j).1)
    have hTrue : core 6 2 6 arc externalArc = true := by
      simpa [arc, externalArc, label] using
        core_of_graphData G C hG hMin hNoSeymour hPivot hRoot hBCard hk
          hx hr rfl hWLe (by omega) eA1 eX eR eP eQ eW
    have hFalse := rSixXTwoCore_unsat arc externalArc
    rw [hFalse] at hTrue
    contradiction
  · rcases row with ⟨hr, hx, hw⟩
    have hRCard : C.R.card = 1 := by
      have := card_R_eq_four_sub_x G C hG hRoot hk
      omega
    have hQCard : C.Q.card = 0 := by
      have := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
      omega
    have hPCard : C.P.card = 6 := hr
    have hWLe : (externalTargets G C).card ≤ 5 := by
      rw [Shared.card_externalTargets G C]
      exact hw
    let eA1 := finsetEquivFin C.A1 hA1Card
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eR := finsetEquivFin C.R hRCard
    let eP := finsetEquivFin C.P hPCard
    let eQ := finsetEquivFin C.Q hQCard
    let eW := finsetEquivFin (externalTargets G C) rfl
    let label := localLabel (by omega : 3 ≤ 4) (by omega : 6 ≤ 6)
      C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1)
    let arc := graphArc G label
    let externalArc := graphExternalArc G (fun j => (eP j).1)
      (fun j => (eW j).1)
    have hTrue : core 6 3 5 arc externalArc = true := by
      simpa [arc, externalArc, label] using
        core_of_graphData G C hG hMin hNoSeymour hPivot hRoot hBCard hk
          hx hr rfl hWLe (by omega) eA1 eX eR eP eQ eW
    have hFalse := rSixXThreeCore_unsat arc externalArc
    rw [hFalse] at hTrue
    contradiction
  · rcases row with ⟨hr, hx, hw⟩
    have hBounds := x_four_aggregate_bounds G C hG hMin hRoot hBCard hk hr hx hw
    have hRCard : C.R.card = 0 := by
      have := card_R_eq_four_sub_x G C hG hRoot hk
      omega
    have hQCard : C.Q.card = 0 := by
      have := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
      omega
    have hPCard : C.P.card = 6 := hr
    let eA1 := finsetEquivFin C.A1 hA1Card
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eR := finsetEquivFin C.R hRCard
    let eP := finsetEquivFin C.P hPCard
    let eQ := finsetEquivFin C.Q hQCard
    let eW := finsetEquivFin (externalTargets G C) hBounds.1
    let label := localLabel (by omega : 4 ≤ 4) (by omega : 6 ≤ 6)
      C.a1 (fun j => (eA1 j).1) (fun j => (eX j).1)
      (fun j => (eR j).1) (fun j => (eP j).1) (fun j => (eQ j).1)
    let arc := graphArc G label
    let externalArc := graphExternalArc G (fun j => (eP j).1)
      (fun j => (eW j).1)
    have hTrue : xFourCore arc externalArc = true := by
      simpa [arc, externalArc, label] using
        xFourCore_of_graphData G C hG hMin hNoSeymour hPivot hRoot hBCard hk
          hx hr hBounds.1 hBounds.2.1 hBounds.2.2 eA1 eX eR eP eQ eW
    have hFalse := rSixXFourCore_unsat arc externalArc
    rw [hFalse] at hTrue
    contradiction

end SeymourEight.BSixKThree
