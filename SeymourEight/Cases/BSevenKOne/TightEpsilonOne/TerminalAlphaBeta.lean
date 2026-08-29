import SeymourEight.Shared.AlmostTournamentKing

set_option linter.style.header false

/-!
# The `(alpha, beta) = (2, 0)` terminal argument

This file proves the `(alpha, beta) = (2, 0)` terminal row.  It builds the
case-specific counts on the shared counting layer, establishes a
subtraction-free local degree identity, and combines it with the
certificate-checked tournament theorem.
-/

namespace SeymourEight.TerminalAlphaBeta

open CertificateBridge Shared

variable {V : Type*} (G : Digraph V)
variable [DecidableRel G.Adj] [DecidableEq V]

/--
Strict second outneighbors in `targets` witnessed through an intermediate
vertex in `via`.
-/
def secondNeighborsThrough (targets via : Finset V) (p : V) : Finset V :=
  targets.filter fun v ↦ ¬G.Adj p v ∧ v ≠ p ∧
    ∃ w ∈ via, G.Adj p w ∧ G.Adj w v

/-- The count `q_p` for targets `P` and intermediates `P ∪ H`. -/
def qCount (P H : Finset V) (p : V) : Nat :=
  (secondNeighborsThrough G P (P ∪ H) p).card

/-- Paths witnessed entirely inside `P` are also witnessed inside `P ∪ H`. -/
theorem internalSecondNeighbors_subset_secondNeighborsThrough
    (P H : Finset V) (p : V) :
    internalSecondNeighbors (G := G) P p ⊆
      secondNeighborsThrough G P (P ∪ H) p := by
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvP, hNotAdj, hvp, w, hwP, hpw, hwv⟩
  apply Finset.mem_filter.mpr
  exact ⟨hvP, hNotAdj, hvp, w, Finset.mem_union_left H hwP, hpw, hwv⟩

/-- Every counted `q_p` target is a genuine strict second outneighbor. -/
theorem secondNeighborsThrough_subset_secondOutNeighborFinset [Fintype V]
    (targets via : Finset V) (p : V) :
    secondNeighborsThrough G targets via p ⊆ G.secondOutNeighborFinset p := by
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨_targets, hNotAdj, hvp, w, _hwVia, hpw, hwv⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨w, hpw, hwv⟩, hNotAdj, hvp⟩

/--
The subtraction-free arithmetic step used in the terminal row.  The hypotheses
are the exact degree identity and
`q_p + 7 ≤ t_p + 2 h_p + 2 e_p`, respectively.
-/
theorem direct_add_q_le_five_of_degree_and_equation18
    (e h t q : Nat) (hDegree : 2 + e + h + t = 8)
    (hEquation18 : q + 7 ≤ t + 2 * h + 2 * e) :
    t + q ≤ 5 := by
  omega

/--
The common-`Z` counting identity.  `W` is the outneighborhood of the selected
common `Z`-vertex `z0`; the hypotheses expose exactly the properties of `W`
used by the proof.
-/
theorem equation18_of_commonZ [Fintype V]
    (P H W : Finset V) (p s z0 : V)
    (hpP : p ∈ P) (hpz0 : G.Adj p z0)
    (hz0W : ∀ w ∈ W, G.Adj z0 w)
    (hWP : Disjoint W P) (hWCard : 8 ≤ W.card)
    (hDirectW : (W.filter (G.Adj p)).card ≤
      directCount G H p + epsilonAt G p s)
    (hNotSeymour : ¬G.IsSeymourVertex p)
    (hDegree : G.outdegree p =
      2 + epsilonAt G p s + directCount G H p + directCount G P p) :
    qCount G P H p + 7 ≤ directCount G P p +
      2 * directCount G H p + 2 * epsilonAt G p s := by
  let Wnew : Finset V := W.filter fun v ↦ ¬G.Adj p v
  have hWnewSecond : Wnew ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvW, hNotAdj⟩
    have hvp : v ≠ p := by
      intro hvp
      subst v
      exact (Finset.disjoint_left.mp hWP) hvW hpP
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨z0, hpz0, hz0W v hvW⟩, hNotAdj, hvp⟩
  have hQSecond : secondNeighborsThrough G P (P ∪ H) p ⊆
      G.secondOutNeighborFinset p :=
    secondNeighborsThrough_subset_secondOutNeighborFinset G P (P ∪ H) p
  have hWnewQDisjoint :
      Disjoint Wnew (secondNeighborsThrough G P (P ∪ H) p) := by
    rw [Finset.disjoint_left]
    intro v hvWnew hvQ
    have hvW : v ∈ W := (Finset.mem_filter.mp hvWnew).1
    have hvP : v ∈ P := (Finset.mem_filter.mp hvQ).1
    exact (Finset.disjoint_left.mp hWP) hvW hvP
  have hSecondCard : Wnew.card + qCount G P H p ≤
      G.secondOutdegree p := by
    have hUnionSubset :
        Wnew ∪ secondNeighborsThrough G P (P ∪ H) p ⊆
          G.secondOutNeighborFinset p :=
      Finset.union_subset hWnewSecond hQSecond
    have hCard := Finset.card_le_card hUnionSubset
    rw [Finset.card_union_of_disjoint hWnewQDisjoint] at hCard
    exact hCard
  have hWSplit :
      (W.filter (G.Adj p)).card + Wnew.card = W.card := by
    exact Finset.card_filter_add_card_filter_not (G.Adj p)
  have hSecondLt : G.secondOutdegree p < G.outdegree p := by
    unfold Digraph.IsSeymourVertex at hNotSeymour
    omega
  omega

/--
Once the local counting identity and the exact degree identities hold on a
seven-vertex tournament `P`, the `(alpha, beta) = (2, 0)` terminal row is
impossible.
-/
theorem alphaBetaTwoZero_impossible_of_equation18
    (P H : Finset V) (s : V) (hPCard : P.card = 7)
    (hG : G.IsOriented)
    (hTournament : ∀ {u : V}, u ∈ P → ∀ {v : V}, v ∈ P → u ≠ v →
      G.Adj u v ∨ G.Adj v u)
    (hDegree : ∀ p ∈ P,
      2 + epsilonAt G p s + directCount G H p + directCount G P p = 8)
    (hEquation18 : ∀ p ∈ P,
      qCount G P H p + 7 ≤ directCount G P p +
        2 * directCount G H p + 2 * epsilonAt G p s) :
    False := by
  have hPNonempty : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp, hReach⟩ :=
    exists_internalReachWithinTwo_eq_card_sub_one_of_complete
      G P hPNonempty hG hTournament
  have hQSubset :=
    internalSecondNeighbors_subset_secondNeighborsThrough G P H p
  have hQCard :
      (internalSecondNeighbors (G := G) P p).card ≤ qCount G P H p :=
    Finset.card_le_card hQSubset
  have hBound : directCount G P p + qCount G P H p ≤ 5 :=
    direct_add_q_le_five_of_degree_and_equation18
      (epsilonAt G p s) (directCount G H p) (directCount G P p)
      (qCount G P H p) (hDegree p hp) (hEquation18 p hp)
  have hReachSix : directCount G P p +
      (internalSecondNeighbors (G := G) P p).card = 6 := by
    rw [← card_internalReachWithinTwo G P p hG, hReach, hPCard]
  have hAtMostFive : directCount G P p +
      (internalSecondNeighbors (G := G) P p).card ≤ 5 :=
    (Nat.add_le_add_left hQCard _).trans hBound
  omega

/--
Common-`Z` form of the complete terminal contradiction.  All graph counting,
the local degree identity, and the tournament certificate are composed here;
callers supply the structural facts about the selected `z0` and its
outneighborhood `W`.
-/
theorem alphaBetaTwoZero_impossible_of_commonZ [Fintype V]
    (P H W : Finset V) (s z0 : V) (hPCard : P.card = 7)
    (hG : G.IsOriented)
    (hTournament : ∀ {u : V}, u ∈ P → ∀ {v : V}, v ∈ P → u ≠ v →
      G.Adj u v ∨ G.Adj v u)
    (hCommonZ : ∀ p ∈ P, G.Adj p z0)
    (hz0W : ∀ w ∈ W, G.Adj z0 w)
    (hWP : Disjoint W P) (hWCard : 8 ≤ W.card)
    (hDirectW : ∀ p ∈ P, (W.filter (G.Adj p)).card ≤
      directCount G H p + epsilonAt G p s)
    (hNotSeymour : ∀ p ∈ P, ¬G.IsSeymourVertex p)
    (hOutDegreeEight : ∀ p ∈ P, G.outdegree p = 8)
    (hDegree : ∀ p ∈ P,
      G.outdegree p =
        2 + epsilonAt G p s + directCount G H p + directCount G P p) :
    False := by
  have hDegreeCounts : ∀ p ∈ P,
      2 + epsilonAt G p s + directCount G H p + directCount G P p = 8 := by
    intro p hp
    exact (hDegree p hp).symm.trans (hOutDegreeEight p hp)
  apply alphaBetaTwoZero_impossible_of_equation18
    G P H s hPCard hG hTournament hDegreeCounts
  intro p hp
  exact equation18_of_commonZ G P H W p s z0 hp (hCommonZ p hp)
    hz0W hWP hWCard (hDirectW p hp) (hNotSeymour p hp) (hDegree p hp)

end SeymourEight.TerminalAlphaBeta
