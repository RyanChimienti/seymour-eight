import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.MTwoSmallProbe
import SeymourEight.Reduction

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoProjectedBridge

open CertificateBridge Shared Labels
open MTwoCore
open Shared.FiniteCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (C : G.LocalConfiguration) (q : V) where
  low : LowLabels G C ({q} ∪ C.Z)
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  w : Fin 7 → Option V
  a_zero : (a 0).1 = C.a1
  a_h : ∀ i : Fin 6, (a ⟨i.val + 1, by omega⟩).1 = (low.h i).1
  a_r : (a 7).1 ∈ C.R

@[simp] theorem Labels.a_zero_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 0).1 = C.a1 := L.a_zero

@[simp] theorem Labels.a_h_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (i : Fin 6) :
    (L.a ⟨i.val + 1, by omega⟩).1 = (L.low.h i).1 := L.a_h i

@[simp] theorem Labels.a_one_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 1).1 = (L.low.h 0).1 := by
  simpa using L.a_h 0
@[simp] theorem Labels.a_two_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 2).1 = (L.low.h 1).1 := by
  simpa using L.a_h 1
@[simp] theorem Labels.a_three_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 3).1 = (L.low.h 2).1 := by
  simpa using L.a_h 2
@[simp] theorem Labels.a_four_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 4).1 = (L.low.h 3).1 := by
  simpa using L.a_h 3
@[simp] theorem Labels.a_five_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 5).1 = (L.low.h 4).1 := by
  simpa using L.a_h 4
@[simp] theorem Labels.a_six_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) : (L.a 6).1 = (L.low.h 5).1 := by
  simpa using L.a_h 5

noncomputable def labels (C : G.LocalConfiguration) (q : V) (hqQ : q ∈ C.Q)
    (hPCard : C.P.card = 6) (hHCard : C.H.card = 6)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hZCard : C.Z.card = 2) (hRCard : C.R.card = 1)
    (hACard : C.A.card = 8) (w : Fin 7 → Option V) : Labels G C q := by
  let low := reachedLabels G C q hqQ hPCard hHCard hAOneCard hXCard hZCard
  let er := finsetEquivFin C.R hRCard
  let a := RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv G C hACard low.h er
  refine ⟨low, a, w, ?_, ?_, ?_⟩
  · exact RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv_zero G C
      hACard low.h er
  · intro i
    exact RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv_h G C
      hACard low.h er i
  · rw [RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv_r G C hACard low.h er]
    exact (er 0).2

/-- Extend any admissible low-level labeling to the full projected labeling.
This is useful when a unique graph-theoretic witness (such as the sole
`A₁ → q` source) is named before the otherwise interchangeable `A₁`
vertices. -/
noncomputable def labelsFromLow (C : G.LocalConfiguration) (q : V)
    (low : LowLabels G C ({q} ∪ C.Z))
    (hRCard : C.R.card = 1) (hACard : C.A.card = 8)
    (w : Fin 7 → Option V) : Labels G C q := by
  let er := finsetEquivFin C.R hRCard
  let a := RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv G C hACard low.h er
  refine ⟨low, a, w, ?_, ?_, ?_⟩
  · exact RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv_zero G C
      hACard low.h er
  · intro i
    exact RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv_h G C
      hACard low.h er i
  · rw [RSeven.XFourNoRoot.BroadFourLabels.aLabelEquiv_r G C hACard low.h er]
    exact (er 0).2

def localVertex (C : G.LocalConfiguration) (q : V) (L : Labels G C q)
    (target : Nat) : V :=
  if htA : target < 8 then
    if target = 0 then (L.a 0).1
    else if target = 1 then (L.a 7).1
    else (L.a ⟨target - 1, by omega⟩).1
  else if htP : target < 14 then (L.low.p ⟨target - 8, by omega⟩).1
  else if htE : target < 17 then (L.low.e ⟨target - 14, by omega⟩).1
  else C.s

def retainedVertexSet (C : G.LocalConfiguration) (q : V) : Finset V :=
  (C.A ∪ C.P ∪ ({q} ∪ C.Z)) ∪ {C.s}

theorem localVertex_mem_A (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (target : Nat) (ht : target < 8) :
    localVertex G C q L target ∈ C.A := by
  by_cases h0 : target = 0
  · simp [localVertex, h0]
  by_cases h1 : target = 1
  · simp [localVertex, h1]
  · simp [localVertex, ht, h0, h1]

noncomputable def retainedLabelEquiv (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented) :
    Fin 18 ≃ {v : V // v ∈ retainedVertexSet G C q} := by
  let f : Fin 18 → {v : V // v ∈ retainedVertexSet G C q} := fun i =>
    if hiA : i.val < 8 then
      ⟨localVertex G C q L i,
        Finset.mem_union_left {C.s} (Finset.mem_union_left ({q} ∪ C.Z)
          (Finset.mem_union_left C.P
            (localVertex_mem_A G C q L i hiA)))⟩
    else if hiP : i.val < 14 then
      ⟨(L.low.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left {C.s} (Finset.mem_union_left ({q} ∪ C.Z)
          (Finset.mem_union_right C.A (L.low.p _).2))⟩
    else if hiE : i.val < 17 then
      ⟨(L.low.e ⟨i.val - 14, by omega⟩).1,
        Finset.mem_union_left {C.s} (Finset.mem_union_right (C.A ∪ C.P)
          (L.low.e _).2)⟩
    else ⟨C.s, Finset.mem_union_right _ (by simp)⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAPE | hvs
    · rcases Finset.mem_union.mp hvAPE with hvAP | hvE
      · rcases Finset.mem_union.mp hvAP with hvA | hvP
        · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
          by_cases hi0 : i.val = 0
          · have hiFin : i = 0 := Fin.ext hi0
            subst i
            refine ⟨0, ?_⟩
            apply Subtype.ext
            simpa [f, localVertex] using congrArg Subtype.val hi
          by_cases hi7 : i.val = 7
          · have hiFin : i = 7 := Fin.ext hi7
            subst i
            refine ⟨1, ?_⟩
            apply Subtype.ext
            simpa [f, localVertex] using congrArg Subtype.val hi
          · refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
            apply Subtype.ext
            simpa [f, localVertex, hi0, hi7,
              show i.val + 1 < 8 by omega] using congrArg Subtype.val hi
        · obtain ⟨i, hi⟩ := L.low.p.surjective ⟨v, hvP⟩
          refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
          apply Subtype.ext
          simpa [f, localVertex, show ¬i.val + 8 < 8 by omega,
            show i.val + 8 < 14 by omega] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := L.low.e.surjective ⟨v, hvE⟩
        refine ⟨⟨i.val + 14, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, localVertex, show ¬i.val + 14 < 8 by omega,
          show ¬i.val + 14 < 14 by omega,
          show i.val + 14 < 17 by omega] using congrArg Subtype.val hi
    · refine ⟨17, ?_⟩
      apply Subtype.ext
      simpa [f] using (Finset.mem_singleton.mp hvs).symm
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hAPE : Disjoint (C.A ∪ C.P) ({q} ∪ C.Z) := by
      rw [Finset.disjoint_left]
      intro v hvAP hvE
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · rcases Finset.mem_union.mp hvE with hvq | hvZ
        · have hvQ : v ∈ C.Q := Finset.mem_singleton.mp hvq ▸ hqQ
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
              (Digraph.LocalConfiguration.Q_subset_B (G := G) C hvQ)
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
      · rcases Finset.mem_union.mp hvE with hvq | hvZ
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
              (Finset.mem_singleton.mp hvq ▸ hqQ)
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
              (Finset.mem_union_right ({C.s} ∪ C.A)
                (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP))
    have hS : Disjoint (C.A ∪ C.P ∪ ({q} ∪ C.Z)) {C.s} := by
      rw [Finset.disjoint_singleton_right]
      intro hs
      rcases Finset.mem_union.mp hs with hsAP | hsE
      · rcases Finset.mem_union.mp hsAP with hsA | hsP
        · exact Digraph.LocalConfiguration.s_notMem_A (G := G) C
            hG.1 hsA
        · exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hsP
      · rcases Finset.mem_union.mp hsE with hsq | hsZ
        · exact Digraph.LocalConfiguration.s_notMem_B (G := G) C
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C
              (Finset.mem_singleton.mp hsq ▸ hqQ))
        · exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C hsZ
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C q} =
        (retainedVertexSet G C q).card by simp,
      retainedVertexSet, Finset.card_union_of_disjoint hS,
      Finset.card_union_of_disjoint hAPE,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.low.p).symm
    have he : ({q} ∪ C.Z).card = 3 := by
      rw [← Fintype.card_coe]
      exact (Fintype.card_congr L.low.e).symm
    rw [ha, hp, he]
    simp

@[simp] theorem retainedLabelEquiv_val (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (i : Fin 18) :
    (retainedLabelEquiv G C q L hqQ hG i).1 = localVertex G C q L i := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, localVertex, hiA]
  by_cases hiP : i.val < 14
  · simp [retainedLabelEquiv, localVertex, hiA, hiP]
  by_cases hiE : i.val < 17
  · simp [retainedLabelEquiv, localVertex, hiA, hiP, hiE]
  · simp [retainedLabelEquiv, localVertex, hiA, hiP, hiE]

@[simp] theorem localVertex_zero (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    localVertex G C q L 0 = C.a1 := by
  simp [localVertex, L.a_zero]

@[simp] theorem localVertex_r (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    localVertex G C q L 1 = (L.a 7).1 := by
  simp [localVertex]

@[simp] theorem localVertex_h (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (i : Fin 6) :
    localVertex G C q L (2 + i.val) = (L.low.h i).1 := by
  simp [localVertex, show 2 + i.val < 8 by omega]
  simp [Nat.add_comm]

@[simp] theorem localVertex_p (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (i : Fin 6) :
    localVertex G C q L (8 + i.val) = (L.low.p i).1 := by
  simp [localVertex, show ¬8 + i.val < 8 by omega,
    show 8 + i.val < 14 by omega]

@[simp] theorem localVertex_e (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (i : Fin 3) :
    localVertex G C q L (14 + i.val) = (L.low.e i).1 := by
  simp [localVertex, show ¬14 + i.val < 8 by omega,
    show ¬14 + i.val < 14 by omega, show 14 + i.val < 17 by omega]

@[simp] theorem localVertex_root (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    localVertex G C q L 17 = C.s := by
  simp [localVertex]

def graphBits (C : G.LocalConfiguration) (q : V) (L : Labels G C q) :
    Encoding := fun n =>
  if hnLow : n < 120 then
    (Bridge.coreBits G.Adj (fun i => (L.low.p i).1)
      (fun i => (L.low.h i).1) (fun i => (L.low.e i).1)).getLsbD n
  else if hnHH : n < 150 then
    (Bridge.coreBits G.Adj (fun i => (L.low.h i).1)
      (fun i => (L.low.p i).1) (fun i => (L.low.e i).1)).getLsbD (n - 120)
  else if hnHA : n < 156 then
    decide (G.Adj (L.low.h ⟨n - 150, by omega⟩).1 C.a1)
  else if hnHR : n < 162 then
    decide (G.Adj (L.low.h ⟨n - 156, by omega⟩).1 (L.a 7).1)
  else if hnHQ : n < 168 then
    decide (G.Adj (L.low.h ⟨n - 162, by omega⟩).1 q)
  else if hnEP : n < 186 then
    let k := n - 168
    decide (G.Adj (L.low.e ⟨k / 6, by omega⟩).1
      (L.low.p ⟨k % 6, Nat.mod_lt _ (by omega)⟩).1)
  else if hnEH : n < 204 then
    let k := n - 186
    decide (G.Adj (L.low.e ⟨k / 6, by omega⟩).1
      (L.low.h ⟨k % 6, Nat.mod_lt _ (by omega)⟩).1)
  else if hnEA : n < 207 then
    decide (G.Adj (L.low.e ⟨n - 204, by omega⟩).1 C.a1)
  else if hnER : n < 210 then
    decide (G.Adj (L.low.e ⟨n - 207, by omega⟩).1 (L.a 7).1)
  else if hnES : n < 213 then
    decide (G.Adj (L.low.e ⟨n - 210, by omega⟩).1 C.s)
  else if hnEE : n < 219 then
    let k := n - 213
    let e := k / 2
    let j := k % 2
    let ei : Fin 3 := ⟨e, by omega⟩
    decide (G.Adj (L.low.e ei).1
      (L.low.e (ei.succAbove ⟨j, Nat.mod_lt _ (by omega)⟩)).1)
  else if hnW : n < 240 then
    let k := n - 219
    match L.w ⟨k / 3, by omega⟩ with
    | some v => decide (G.Adj (L.low.e ⟨k % 3, Nat.mod_lt _ (by omega)⟩).1 v)
    | none => false
  else if hnRP : n < 253 then
    if hn : 247 ≤ n then
      decide (G.Adj (L.a 7).1 (L.low.p ⟨n - 247, by omega⟩).1)
    else false
  else if hnRQ : n < 254 then decide (G.Adj (L.a 7).1 q)
  else if hnRA : n < 255 then decide (G.Adj (L.a 7).1 C.a1)
  else if hnRH : n < 261 then
    decide (G.Adj (L.a 7).1 (L.low.h ⟨n - 255, by omega⟩).1)
  else false

private theorem div_index (i j w : Nat) (hj : j < w) :
    (i * w + j) / w = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

set_option linter.flexible false in
private theorem mod_index (i j w : Nat) (hj : j < w) :
    (i * w + j) % w = j := Nat.mul_add_mod_of_lt hj

@[simp] theorem pArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (i j : Nat) (hi : i < 6) (hj : j < 6) :
    pArc (graphBits G C q L) i j =
      decide (G.Adj (L.low.p ⟨i, hi⟩).1 (L.low.p ⟨j, hj⟩).1) := by
  rw [pArc]
  have hn : directedIndex i j 6 < 120 := by
    unfold directedIndex
    split <;> omega
  rw [show graphBits G C q L (directedIndex i j 6) =
      (Bridge.coreBits G.Adj (fun k => (L.low.p k).1)
        (fun k => (L.low.h k).1) (fun k => (L.low.e k).1)).getLsbD
          (directedIndex i j 6) by simp [graphBits, hn]]
  change Core.pArc (Bridge.coreBits G.Adj (fun k => (L.low.p k).1)
    (fun k => (L.low.h k).1) (fun k => (L.low.e k).1)) i j = _
  rw [Bridge.pArc_coreBits G.Adj _ _ _ i j hi hj]
  by_cases hij : i = j
  · subst j
    simp only [ne_eq, not_true_eq_false, Finset.singleton_union, false_and,
      decide_false, false_eq_decide_iff]
    exact hG.1 _
  · simp [hij]

@[simp] theorem pToH_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (p h : Nat) (hp : p < 6) (hh : h < 6) :
    pToH (graphBits G C q L) p h =
      decide (G.Adj (L.low.p ⟨p, hp⟩).1 (L.low.h ⟨h, hh⟩).1) := by
  rw [pToH]
  have hn : 30 + 6 * p + h < 120 := by omega
  rw [show graphBits G C q L (30 + 6 * p + h) =
      (Bridge.coreBits G.Adj (fun k => (L.low.p k).1)
        (fun k => (L.low.h k).1) (fun k => (L.low.e k).1)).getLsbD
          (30 + 6 * p + h) by simp [graphBits, hn]]
  exact Bridge.pToH_coreBits G.Adj _ _ _ p h hp hh

@[simp] theorem hToP_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (h p : Nat) (hh : h < 6) (hp : p < 6) :
    hToP (graphBits G C q L) h p =
      decide (G.Adj (L.low.h ⟨h, hh⟩).1 (L.low.p ⟨p, hp⟩).1) := by
  rw [hToP]
  have hn : 66 + 6 * h + p < 120 := by omega
  rw [show graphBits G C q L (66 + 6 * h + p) =
      (Bridge.coreBits G.Adj (fun k => (L.low.p k).1)
        (fun k => (L.low.h k).1) (fun k => (L.low.e k).1)).getLsbD
          (66 + 6 * h + p) by simp [graphBits, hn]]
  exact Bridge.hToP_coreBits G.Adj _ _ _ h p hh hp

@[simp] theorem pToE_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (p e : Nat) (hp : p < 6) (he : e < 3) :
    pToE (graphBits G C q L) p e =
      decide (G.Adj (L.low.p ⟨p, hp⟩).1 (L.low.e ⟨e, he⟩).1) := by
  rw [pToE]
  have hn : 102 + 3 * p + e < 120 := by omega
  rw [show graphBits G C q L (102 + 3 * p + e) =
      (Bridge.coreBits G.Adj (fun k => (L.low.p k).1)
        (fun k => (L.low.h k).1) (fun k => (L.low.e k).1)).getLsbD
          (102 + 3 * p + e) by simp [graphBits, hn]]
  exact Bridge.pToE_coreBits G.Adj _ _ _ p e hp he

@[simp] theorem hArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (i j : Nat) (hi : i < 6) (hj : j < 6) :
    hArc (graphBits G C q L) i j =
      decide (G.Adj (L.low.h ⟨i, hi⟩).1 (L.low.h ⟨j, hj⟩).1) := by
  rw [hArc]
  have hn : 120 + directedIndex i j 6 < 150 := by
    unfold directedIndex
    split <;> omega
  have hs : 120 + directedIndex i j 6 - 120 = directedIndex i j 6 := by omega
  rw [show graphBits G C q L (120 + directedIndex i j 6) =
      (Bridge.coreBits G.Adj (fun k => (L.low.h k).1)
        (fun k => (L.low.p k).1) (fun k => (L.low.e k).1)).getLsbD
          (directedIndex i j 6) by
    simp [graphBits, show ¬120 + directedIndex i j 6 < 120 by omega,
      hn, hs]]
  change Core.pArc (Bridge.coreBits G.Adj (fun k => (L.low.h k).1)
    (fun k => (L.low.p k).1) (fun k => (L.low.e k).1)) i j = _
  rw [Bridge.pArc_coreBits G.Adj _ _ _ i j hi hj]
  by_cases hij : i = j
  · subst j
    simp only [ne_eq, not_true_eq_false, Finset.singleton_union, false_and,
      decide_false, false_eq_decide_iff]
    exact hG.1 _
  · simp [hij]

@[simp] theorem hToAOne_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (h : Nat) (hh : h < 6) :
    hToAOne (graphBits G C q L) h =
      decide (G.Adj (L.low.h ⟨h, hh⟩).1 C.a1) := by
  unfold hToAOne
  have h0 : ¬150 + h < 120 := by omega
  have h1 : 150 + h < 156 := by omega
  simp [graphBits, h0, h1]

@[simp] theorem hToR_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (h : Nat) (hh : h < 6) :
    hToR (graphBits G C q L) h =
      decide (G.Adj (L.low.h ⟨h, hh⟩).1 (L.a 7).1) := by
  unfold hToR
  have h0 : ¬156 + h < 120 := by omega
  have h1 : ¬156 + h < 150 := by omega
  have h2 : ¬156 + h < 156 := by omega
  have h3 : 156 + h < 162 := by omega
  simp [graphBits, h0, h1, h2, h3]

@[simp] theorem hToQ_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (h : Nat) (hh : h < 6) :
    hToQ (graphBits G C q L) h =
      decide (G.Adj (L.low.h ⟨h, hh⟩).1 q) := by
  unfold hToQ
  have h0 : ¬162 + h < 120 := by omega
  have h1 : ¬162 + h < 150 := by omega
  have h2 : ¬162 + h < 156 := by omega
  have h3 : ¬162 + h < 162 := by omega
  have h4 : 162 + h < 168 := by omega
  simp [graphBits, h0, h1, h2, h3, h4]

@[simp] theorem eToP_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (e p : Nat) (he : e < 3) (hp : p < 6) :
    eToP (graphBits G C q L) e p =
      decide (G.Adj (L.low.e ⟨e, he⟩).1 (L.low.p ⟨p, hp⟩).1) := by
  unfold eToP
  have hd : (6 * e + p) / 6 = e := by
    simpa [Nat.mul_comm] using div_index e p 6 hp
  have hm : (6 * e + p) % 6 = p := by
    simpa [Nat.mul_comm] using mod_index e p 6 hp
  have h0 : ¬168 + 6 * e + p < 120 := by omega
  have h1 : ¬168 + 6 * e + p < 150 := by omega
  have h2 : ¬168 + 6 * e + p < 156 := by omega
  have h3 : ¬168 + 6 * e + p < 162 := by omega
  have h4 : ¬168 + 6 * e + p < 168 := by omega
  have h5 : 168 + 6 * e + p < 186 := by omega
  have hs : 168 + 6 * e + p - 168 = 6 * e + p := by omega
  simp [graphBits, h0, h1, h2, h3, h4, h5, hs, hd, hm]

@[simp] theorem eToH_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (e h : Nat) (he : e < 3) (hh : h < 6) :
    eToH (graphBits G C q L) e h =
      decide (G.Adj (L.low.e ⟨e, he⟩).1 (L.low.h ⟨h, hh⟩).1) := by
  unfold eToH
  have hd : (6 * e + h) / 6 = e := by
    simpa [Nat.mul_comm] using div_index e h 6 hh
  have hm : (6 * e + h) % 6 = h := by
    simpa [Nat.mul_comm] using mod_index e h 6 hh
  have hs : 186 + 6 * e + h - 186 = 6 * e + h := by omega
  simp [graphBits, show ¬186 + 6 * e + h < 120 by omega,
    show ¬186 + 6 * e + h < 150 by omega,
    show ¬186 + 6 * e + h < 156 by omega,
    show ¬186 + 6 * e + h < 162 by omega,
    show ¬186 + 6 * e + h < 168 by omega,
    show ¬186 + 6 * e + h < 186 by omega,
    show 186 + 6 * e + h < 204 by omega, hs, hd, hm]

@[simp] theorem eToAOne_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (e : Nat) (he : e < 3) :
    eToAOne (graphBits G C q L) e =
      decide (G.Adj (L.low.e ⟨e, he⟩).1 C.a1) := by
  unfold eToAOne
  simp [graphBits, show ¬204 + e < 120 by omega,
    show ¬204 + e < 150 by omega, show ¬204 + e < 156 by omega,
    show ¬204 + e < 162 by omega, show ¬204 + e < 168 by omega,
    show ¬204 + e < 186 by omega, show ¬204 + e < 204 by omega,
    show 204 + e < 207 by omega]

@[simp] theorem eToR_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (e : Nat) (he : e < 3) :
    eToR (graphBits G C q L) e =
      decide (G.Adj (L.low.e ⟨e, he⟩).1 (L.a 7).1) := by
  unfold eToR
  simp [graphBits, show ¬207 + e < 120 by omega,
    show ¬207 + e < 150 by omega, show ¬207 + e < 156 by omega,
    show ¬207 + e < 162 by omega, show ¬207 + e < 168 by omega,
    show ¬207 + e < 186 by omega, show ¬207 + e < 204 by omega,
    show ¬207 + e < 207 by omega, show 207 + e < 210 by omega]

@[simp] theorem eToRoot_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (e : Nat) (he : e < 3) :
    eToRoot (graphBits G C q L) e =
      decide (G.Adj (L.low.e ⟨e, he⟩).1 C.s) := by
  unfold eToRoot
  simp [graphBits, show ¬210 + e < 120 by omega,
    show ¬210 + e < 150 by omega, show ¬210 + e < 156 by omega,
    show ¬210 + e < 162 by omega, show ¬210 + e < 168 by omega,
    show ¬210 + e < 186 by omega, show ¬210 + e < 204 by omega,
    show ¬210 + e < 207 by omega, show ¬210 + e < 210 by omega,
    show 210 + e < 213 by omega]

set_option linter.flexible false in
@[simp] theorem eArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (i j : Nat) (hi : i < 3) (hj : j < 3) :
    eArc (graphBits G C q L) i j =
      decide (G.Adj (L.low.e ⟨i, hi⟩).1 (L.low.e ⟨j, hj⟩).1) := by
  interval_cases i <;> interval_cases j <;>
    simp_all [eArc, directedIndex, graphBits]
  all_goals try
    rw [show (2 : Fin 3).succAbove (1 : Fin 2) = (1 : Fin 3) by decide]
  all_goals first
    | exact hG.1 _

@[simp] theorem outsideAdjSeven_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (w e : Nat) (hw : w < 7) (he : e < 3) :
    outsideAdjSeven (graphBits G C q L) w e =
      match L.w ⟨w, hw⟩ with
      | some v => decide (G.Adj (L.low.e ⟨e, he⟩).1 v)
      | none => false := by
  unfold outsideAdjSeven
  have hd : (3 * w + e) / 3 = w := by
    simpa [Nat.mul_comm] using div_index w e 3 he
  have hm : (3 * w + e) % 3 = e := by
    simpa [Nat.mul_comm] using mod_index w e 3 he
  have hs : 219 + 3 * w + e - 219 = 3 * w + e := by omega
  simp [graphBits, show ¬219 + 3 * w + e < 120 by omega,
    show ¬219 + 3 * w + e < 150 by omega,
    show ¬219 + 3 * w + e < 156 by omega,
    show ¬219 + 3 * w + e < 162 by omega,
    show ¬219 + 3 * w + e < 168 by omega,
    show ¬219 + 3 * w + e < 186 by omega,
    show ¬219 + 3 * w + e < 204 by omega,
    show ¬219 + 3 * w + e < 207 by omega,
    show ¬219 + 3 * w + e < 210 by omega,
    show ¬219 + 3 * w + e < 213 by omega,
    show ¬219 + 3 * w + e < 219 by omega,
    show 219 + 3 * w + e < 240 by omega, hs, hd, hm]

@[simp] theorem rToP_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (p : Nat) (hp : p < 6) :
    rToP (graphBits G C q L) p =
      decide (G.Adj (L.a 7).1 (L.low.p ⟨p, hp⟩).1) := by
  unfold rToP
  simp [graphBits, show ¬247 + p < 120 by omega,
    show ¬247 + p < 150 by omega, show ¬247 + p < 156 by omega,
    show ¬247 + p < 162 by omega, show ¬247 + p < 168 by omega,
    show ¬247 + p < 186 by omega, show ¬247 + p < 204 by omega,
    show ¬247 + p < 207 by omega, show ¬247 + p < 210 by omega,
    show ¬247 + p < 213 by omega, show ¬247 + p < 219 by omega,
    show ¬247 + p < 240 by omega, show 247 + p < 253 by omega]

@[simp] theorem rToQ_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    rToQ (graphBits G C q L) = decide (G.Adj (L.a 7).1 q) := by
  unfold rToQ
  simp [graphBits]

@[simp] theorem rToAOne_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    rToAOne (graphBits G C q L) = decide (G.Adj (L.a 7).1 C.a1) := by
  unfold rToAOne
  simp [graphBits]

@[simp] theorem rToH_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (h : Nat) (hh : h < 6) :
    rToH (graphBits G C q L) h =
      decide (G.Adj (L.a 7).1 (L.low.h ⟨h, hh⟩).1) := by
  unfold rToH
  simp [graphBits, show ¬255 + h < 120 by omega,
    show ¬255 + h < 150 by omega, show ¬255 + h < 156 by omega,
    show ¬255 + h < 162 by omega, show ¬255 + h < 168 by omega,
    show ¬255 + h < 186 by omega, show ¬255 + h < 204 by omega,
    show ¬255 + h < 207 by omega, show ¬255 + h < 210 by omega,
    show ¬255 + h < 213 by omega, show ¬255 + h < 219 by omega,
    show ¬255 + h < 240 by omega, show ¬255 + h < 253 by omega,
    show ¬255 + h < 254 by omega, show ¬255 + h < 255 by omega,
    show 255 + h < 261 by omega]

theorem oriented_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (heZero : (L.low.e 0).1 = q) :
    oriented (graphBits G C q L) = true := by
  simp only [oriented, Bool.and_eq_true]
  have hPP : all 6 (fun i => all 6 fun j => decide (i = j) ||
      !(pArc (graphBits G C q L) i j && pArc (graphBits G C q L) j i)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro i hi
    rw [Bridge.all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [pArc, hij]
    · by_cases ha : G.Adj (L.low.p ⟨i, hi⟩).1 (L.low.p ⟨j, hj⟩).1
      · rw [pArc_graphBits G C q L hG i j hi hj,
          pArc_graphBits G C q L hG j i hj hi]
        simp [hij, ha, hG.2 ha]
      · rw [pArc_graphBits G C q L hG i j hi hj]
        simp [hij, ha]
  have hHH : all 6 (fun i => all 6 fun j => decide (i = j) ||
      !(hArc (graphBits G C q L) i j && hArc (graphBits G C q L) j i)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro i hi
    rw [Bridge.all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hArc, hij]
    · by_cases ha : G.Adj (L.low.h ⟨i, hi⟩).1 (L.low.h ⟨j, hj⟩).1
      · rw [hArc_graphBits G C q L hG i j hi hj,
          hArc_graphBits G C q L hG j i hj hi]
        simp [hij, ha, hG.2 ha]
      · rw [hArc_graphBits G C q L hG i j hi hj]
        simp [hij, ha]
  have hEE : all 3 (fun i => all 3 fun j => decide (i = j) ||
      !(eArc (graphBits G C q L) i j && eArc (graphBits G C q L) j i)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro i hi
    rw [Bridge.all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [eArc, hij]
    · by_cases ha : G.Adj (L.low.e ⟨i, hi⟩).1 (L.low.e ⟨j, hj⟩).1
      · rw [eArc_graphBits G C q L hG i j hi hj,
          eArc_graphBits G C q L hG j i hj hi]
        rw [decide_eq_true ha, decide_eq_false (hG.2 ha)]
        simp [hij]
      · rw [eArc_graphBits G C q L hG i j hi hj]
        rw [decide_eq_false ha]
        simp [hij]
  have hPH : all 6 (fun p => all 6 fun h =>
      !(pToH (graphBits G C q L) p h && hToP (graphBits G C q L) h p)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro p hp
    rw [Bridge.all_eq_true_iff]
    intro h hh
    by_cases ha : G.Adj (L.low.p ⟨p, hp⟩).1 (L.low.h ⟨h, hh⟩).1
    · rw [pToH_graphBits G C q L p h hp hh,
        hToP_graphBits G C q L h p hh hp]
      simp [ha, hG.2 ha]
    · rw [pToH_graphBits G C q L p h hp hh]
      simp [ha]
  have hPE : all 6 (fun p => all 3 fun e =>
      !(pToE (graphBits G C q L) p e && eToP (graphBits G C q L) e p)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro p hp
    rw [Bridge.all_eq_true_iff]
    intro e he
    by_cases ha : G.Adj (L.low.p ⟨p, hp⟩).1 (L.low.e ⟨e, he⟩).1
    · rw [pToE_graphBits G C q L p e hp he,
        eToP_graphBits G C q L e p he hp]
      rw [decide_eq_true ha, decide_eq_false (hG.2 ha)]
      decide
    · rw [pToE_graphBits G C q L p e hp he]
      rw [decide_eq_false ha]
      simp
  have hHQ : all 6 (fun h =>
      !(hToQ (graphBits G C q L) h && eToH (graphBits G C q L) 0 h)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro h hh
    by_cases ha : G.Adj (L.low.h ⟨h, hh⟩).1 q
    · rw [hToQ_graphBits G C q L h hh,
        eToH_graphBits G C q L 0 h (by omega) hh]
      have heZero' : (L.low.e ⟨0, by omega⟩).1 = q := by simpa using heZero
      rw [heZero']
      rw [decide_eq_true ha, decide_eq_false (hG.2 ha)]
      decide
    · rw [hToQ_graphBits G C q L h hh]
      simp [ha]
  have hHR : all 6 (fun h =>
      !(hToR (graphBits G C q L) h && rToH (graphBits G C q L) h)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro h hh
    by_cases ha : G.Adj (L.low.h ⟨h, hh⟩).1 (L.a 7).1
    · rw [hToR_graphBits G C q L h hh,
        rToH_graphBits G C q L h hh]
      simp [ha, hG.2 ha]
    · rw [hToR_graphBits G C q L h hh]
      simp [ha]
  exact ⟨⟨⟨⟨⟨⟨hPP, hHH⟩, hEE⟩, hPH⟩, hPE⟩, hHQ⟩, hHR⟩

theorem P_outdegree_eq_blocks (C : G.LocalConfiguration) (q : V)
    (_L : Labels G C q)
    (hqQ : q ∈ C.Q)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (p : V) (hp : p ∈ C.P) :
    G.outdegree p = directCount G C.P p + directCount G C.H p +
      directCount G ({q} ∪ C.Z) p := by
  have hPH : Disjoint C.P C.H :=
    Digraph.LocalConfiguration.disjoint_H_P (G := G) C |>.symm
  have hPHE : Disjoint (C.P ∪ C.H) ({q} ∪ C.Z) := by
    rw [Finset.disjoint_left]
    intro v hvPH hvE
    rcases Finset.mem_union.mp hvPH with hvP | hvH
    · rcases Finset.mem_union.mp hvE with hvq | hvZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
            (Finset.mem_singleton.mp hvq ▸ hqQ)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
    · rcases Finset.mem_union.mp hvE with hvq | hvZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C
              (Finset.mem_singleton.mp hvq ▸ hqQ))
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
  have h := outdegree_eq_directCount_of_captured G
    (C.P ∪ C.H ∪ ({q} ∪ C.Z)) p (hCaptured p hp)
  rw [directCount_union_of_disjoint G (C.P ∪ C.H) ({q} ∪ C.Z) p hPHE,
    directCount_union_of_disjoint G C.P C.H p hPH] at h
  exact h

theorem hLocalArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (heZero : (L.low.e 0).1 = q)
    (h target : Nat) (hh : h < 6) (ht : target < 18) :
    hLocalArc (graphBits G C q L) h target =
      decide (G.Adj (L.low.h ⟨h, hh⟩).1 (localVertex G C q L target)) := by
  have hhA : (L.low.h ⟨h, hh⟩).1 ∈ C.A :=
    Digraph.LocalConfiguration.H_subset_A (G := G) C (L.low.h _).2
  have hNoS : ¬G.Adj (L.low.h ⟨h, hh⟩).1 C.s :=
    hG.2 ((Digraph.mem_outNeighborFinset (G := G)).mp hhA)
  have hNoZ (i : Fin 2) :
      ¬G.Adj (L.low.h ⟨h, hh⟩).1 (L.low.e ⟨i.val + 1, by omega⟩).1 := by
    rcases Finset.mem_union.mp (L.low.e_tail_externalTargets i) with hvZ | hvRoot
    · exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
        G C hG _ _ hhA hvZ
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : (L.low.e ⟨i.val + 1, by omega⟩).1 = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        rw [hvs]
        exact hNoS
      · simp [rootSecondFinset, hReach] at hvRoot
  interval_cases target <;>
    simp_all [hLocalArc, localVertex]

theorem rLocalArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (heZero : (L.low.e 0).1 = q)
    (target : Nat) (ht : target < 18) :
    rLocalArc (graphBits G C q L) target =
      decide (G.Adj (L.a 7).1 (localVertex G C q L target)) := by
  have hrA : (L.a 7).1 ∈ C.A := (L.a 7).2
  have hLoop : ¬G.Adj (L.a 7).1 (L.a 7).1 := hG.1 _
  have hNoS : ¬G.Adj (L.a 7).1 C.s :=
    hG.2 ((Digraph.mem_outNeighborFinset (G := G)).mp hrA)
  have hNoZ (i : Fin 2) :
      ¬G.Adj (L.a 7).1 (L.low.e ⟨i.val + 1, by omega⟩).1 := by
    rcases Finset.mem_union.mp (L.low.e_tail_externalTargets i) with hvZ | hvRoot
    · exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
        G C hG _ _ hrA hvZ
    · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
      · have hvs : (L.low.e ⟨i.val + 1, by omega⟩).1 = C.s := by
          simpa [rootSecondFinset, hReach] using hvRoot
        rw [hvs]
        exact hNoS
      · simp [rootSecondFinset, hReach] at hvRoot
  interval_cases target <;>
    simp_all [rLocalArc, localVertex]

theorem pLocalArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (target p : Nat) (ht : target < 18) (hp : p < 6) :
    pLocalArc (graphBits G C q L) p target =
      decide (G.Adj (L.low.p ⟨p, hp⟩).1 (localVertex G C q L target)) := by
  have hpP : (L.low.p ⟨p, hp⟩).1 ∈ C.P := (L.low.p _).2
  have hNoAOne : ¬G.Adj (L.low.p ⟨p, hp⟩).1 C.a1 :=
    hG.2 (Finset.mem_filter.mp hpP).2
  have hNoR : ¬G.Adj (L.low.p ⟨p, hp⟩).1 (L.a 7).1 :=
    RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R G C _ _
      hpP L.a_r
  have hNoS : ¬G.Adj (L.low.p ⟨p, hp⟩).1 C.s :=
    RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.root_tail_absent G C
      hRoot hpP
  interval_cases target <;>
    simp_all [pLocalArc, localVertex]

theorem eLocalArc_graphBits (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (e target : Nat) (he : e < 3) (ht : target < 18) :
    eLocalArc (graphBits G C q L) e target =
      decide (G.Adj (L.low.e ⟨e, he⟩).1 (localVertex G C q L target)) := by
  interval_cases target <;>
    simp_all [eLocalArc, localVertex]

theorem count_hArc_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (h : Nat) (hh : h < 6) :
    (count 6 (hArc (graphBits G C q L) h)).toNat =
      directCount G C.H (L.low.h ⟨h, hh⟩).1 := by
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H L.low.h
  intro j
  rw [hArc_graphBits G C q L hG h j hh j.isLt]
  by_cases hij : h = j
  · have hv : (L.low.h ⟨h, hh⟩).1 = (L.low.h j).1 := by
      congr 2
      exact Fin.ext hij
    simp [hij]
  · simp

theorem count_hToP_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (h : Nat) (hh : h < 6) :
    (count 6 (hToP (graphBits G C q L) h)).toNat =
      directCount G C.P (L.low.h ⟨h, hh⟩).1 := by
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.low.p
  intro j
  rw [hToP_graphBits G C q L h j hh j.isLt]
  simp

theorem count_rToH_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    (count 6 (rToH (graphBits G C q L))).toNat =
      directCount G C.H (L.a 7).1 := by
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H L.low.h
  intro j
  rw [rToH_graphBits G C q L j j.isLt]
  simp

theorem count_rToP_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    (count 6 (rToP (graphBits G C q L))).toNat =
      directCount G C.P (L.a 7).1 := by
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.low.p
  intro j
  rw [rToP_graphBits G C q L j j.isLt]
  simp

private theorem bitCount_decide_toNat (P : Prop) [Decidable P] :
    (bitCount (decide P)).toNat = if P then 1 else 0 := by
  by_cases h : P <;> simp [h, bitCount]

private theorem count_toNat_le (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat ≤ n := by
  rw [Bridge.toNat_count n f hn]
  calc
    _ ≤ ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases f i <;> decide
    _ = n := by simp

theorem hInternalOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hRSingleton : C.R = {(L.a 7).1})
    (h : Nat) (hh : h < 6) :
    (hInternalOut (graphBits G C q L) h).toNat =
      directCount G C.A (L.low.h ⟨h, hh⟩).1 := by
  let u := (L.low.h ⟨h, hh⟩).1
  have hHa : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_singleton_right]
    intro haH
    rcases Finset.mem_union.mp haH with haA1 | haX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 haA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C haX
  have hPartsR : Disjoint (C.H ∪ {C.a1}) C.R := by
    simpa [Digraph.LocalConfiguration.H] using
      Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hDirect : directCount G C.A u =
      directCount G C.H u +
        (if G.Adj u C.a1 then 1 else 0) +
        (if G.Adj u (L.a 7).1 then 1 else 0) := by
    have hA : C.H ∪ {C.a1} ∪ C.R = C.A := by
      simpa [Digraph.LocalConfiguration.H] using
        Digraph.LocalConfiguration.local_parts_union_R (G := G) C
    calc
      directCount G C.A u =
          directCount G (C.H ∪ {C.a1} ∪ C.R) u := by rw [hA]
      _ = _ := by
        rw [directCount_union_of_disjoint G (C.H ∪ {C.a1}) C.R u hPartsR,
          directCount_union_of_disjoint G C.H {C.a1} u hHa, hRSingleton,
          directCount_singleton, directCount_singleton]
        simp [epsilonAt]
  have hcLe := count_toNat_le 6 (hArc (graphBits G C q L) h) (by omega)
  have hbOne : (bitCount (hToAOne (graphBits G C q L) h)).toNat ≤ 1 := by
    cases hToAOne (graphBits G C q L) h <;> decide
  have hrOne : (bitCount (hToR (graphBits G C q L) h)).toNat ≤ 1 := by
    cases hToR (graphBits G C q L) h <;> decide
  unfold hInternalOut
  rw [BitVec.toNat_add, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    count_hArc_toNat G C q L hG h hh,
    hToAOne_graphBits G C q L h hh,
    hToR_graphBits G C q L h hh,
    bitCount_decide_toNat, bitCount_decide_toNat]
  exact hDirect.symm

theorem hBOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q)
    (hB : C.B = C.P ∪ {q})
    (h : Nat) (hh : h < 6) :
    (hBOut (graphBits G C q L) h).toNat =
      directCount G C.B (L.low.h ⟨h, hh⟩).1 := by
  let u := (L.low.h ⟨h, hh⟩).1
  have hPq : Disjoint C.P {q} := by
    rw [Finset.disjoint_singleton_right]
    exact fun hqP => (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hqP hqQ
  have hDirect : directCount G C.B u =
      directCount G C.P u + (if G.Adj u q then 1 else 0) := by
    rw [hB, directCount_union_of_disjoint G C.P {q} u hPq]
    rw [directCount_singleton]
    simp [epsilonAt]
  have hcLe := count_toNat_le 6 (hToP (graphBits G C q L) h) (by omega)
  have hbOne : (bitCount (hToQ (graphBits G C q L) h)).toNat ≤ 1 := by
    cases hToQ (graphBits G C q L) h <;> decide
  unfold hBOut
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
    count_hToP_toNat G C q L h hh,
    hToQ_graphBits G C q L h hh, bitCount_decide_toNat]
  exact hDirect.symm

theorem rInternalOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hRSingleton : C.R = {(L.a 7).1}) :
    (rInternalOut (graphBits G C q L)).toNat =
      directCount G C.A (L.a 7).1 := by
  have hHa : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_singleton_right]
    intro haH
    rcases Finset.mem_union.mp haH with haA1 | haX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 haA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C haX
  have hPartsR : Disjoint (C.H ∪ {C.a1}) C.R := by
    simpa [Digraph.LocalConfiguration.H] using
      Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hLoop : ¬G.Adj (L.a 7).1 (L.a 7).1 := hG.1 _
  have hDirect : directCount G C.A (L.a 7).1 =
      (if G.Adj (L.a 7).1 C.a1 then 1 else 0) +
        directCount G C.H (L.a 7).1 := by
    have hA : C.H ∪ {C.a1} ∪ C.R = C.A := by
      simpa [Digraph.LocalConfiguration.H] using
        Digraph.LocalConfiguration.local_parts_union_R (G := G) C
    calc
      directCount G C.A (L.a 7).1 =
          directCount G (C.H ∪ {C.a1} ∪ C.R) (L.a 7).1 := by rw [hA]
      _ = _ := by
        rw [directCount_union_of_disjoint G (C.H ∪ {C.a1}) C.R _ hPartsR,
          directCount_union_of_disjoint G C.H {C.a1} _ hHa, hRSingleton,
          directCount_singleton, directCount_singleton]
        simp [epsilonAt, hLoop, Nat.add_comm]
  have hcLe := count_toNat_le 6 (rToH (graphBits G C q L)) (by omega)
  have hbOne : (bitCount (rToAOne (graphBits G C q L))).toNat ≤ 1 := by
    cases rToAOne (graphBits G C q L) <;> decide
  unfold rInternalOut
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
    rToAOne_graphBits G C q L, count_rToH_toNat G C q L,
    bitCount_decide_toNat]
  exact hDirect.symm

theorem rBOut_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q)
    (hB : C.B = C.P ∪ {q}) :
    (rBOut (graphBits G C q L)).toNat =
      directCount G C.B (L.a 7).1 := by
  have hPq : Disjoint C.P {q} := by
    rw [Finset.disjoint_singleton_right]
    exact fun hqP => (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hqP hqQ
  have hDirect : directCount G C.B (L.a 7).1 =
      directCount G C.P (L.a 7).1 +
        (if G.Adj (L.a 7).1 q then 1 else 0) := by
    rw [hB, directCount_union_of_disjoint G C.P {q} _ hPq]
    rw [directCount_singleton]
    simp [epsilonAt]
  have hcLe := count_toNat_le 6 (rToP (graphBits G C q L)) (by omega)
  have hbOne : (bitCount (rToQ (graphBits G C q L))).toNat ≤ 1 := by
    cases rToQ (graphBits G C q L) <;> decide
  unfold rBOut
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
    count_rToP_toNat G C q L, rToQ_graphBits G C q L,
    bitCount_decide_toNat]
  exact hDirect.symm

theorem A_outdegree_eq_A_add_B (C : G.LocalConfiguration)
    (hG : G.IsOriented) (u : V) (huA : u ∈ C.A) :
    G.outdegree u = directCount G C.A u + directCount G C.B u := by
  have hAB := Digraph.LocalConfiguration.disjoint_A_B (G := G) C
  have hCap :=
    RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
      G C hG u huA
  have h := outdegree_eq_directCount_of_captured G (C.A ∪ C.B) u hCap
  rw [directCount_union_of_disjoint G C.A C.B u hAB] at h
  exact h

theorem hConditions_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPivot : IsMinimalPivot G C)
    (hqQ : q ∈ C.Q) (hB : C.B = C.P ∪ {q})
    (hRSingleton : C.R = {(L.a 7).1}) (hk : C.k = 2) (hr : C.r = 6) :
    hConditions (graphBits G C q L) = true := by
  rw [hConditions, Bridge.all_eq_true_iff]
  intro h hh
  let u := (L.low.h ⟨h, hh⟩).1
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.H_subset_A (G := G) C (L.low.h _).2
  have hI := hInternalOut_toNat G C q L hG hRSingleton h hh
  have hB' := hBOut_toNat G C q L hqQ hB h hh
  have hSplit := A_outdegree_eq_A_add_B G C hG u huA
  have hPiv := hPivot u huA
  have hILe : (hInternalOut (graphBits G C q L) h).toNat ≤ 8 := by
    rw [hI]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.a).symm)
  have hBLe : (hBOut (graphBits G C q L) h).toNat ≤ 7 := by
    rw [hB']
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by
        rw [hB]
        have hPq : Disjoint C.P {q} := by
          rw [Finset.disjoint_singleton_right]
          exact fun hqP => (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hqP hqQ
        rw [Finset.card_union_of_disjoint hPq]
        have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.low.p).symm
        simp [hp])
  have hMinI : 2 ≤ (hInternalOut (graphBits G C q L) h).toNat := by
    rw [hI]
    have hp := hPiv.1
    change C.k ≤ directCount G C.A u at hp
    rw [hk] at hp
    simpa [u] using hp
  have hTotal : 8 ≤ (hInternalOut (graphBits G C q L) h).toNat +
      (hBOut (graphBits G C q L) h).toNat := by
    rw [hI, hB', ← hSplit]
    exact hMin u
  have hTie : (hInternalOut (graphBits G C q L) h).toNat = 2 →
      6 ≤ (hBOut (graphBits G C q L) h).toNat := by
    intro heq
    rw [hI] at heq
    rw [hB']
    have hEq : (C.A.filter (G.Adj u)).card = C.k := by
      change directCount G C.A u = C.k
      rw [hk]
      simpa [u] using heq
    have ht := hPiv.2 hEq
    change C.r ≤ directCount G C.B u at ht
    rw [hr] at ht
    simpa [u] using ht
  simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq,
    Bool.or_eq_true]
  refine ⟨⟨hMinI, ?_⟩, ?_⟩
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact hTotal
  · by_cases heq : hInternalOut (graphBits G C q L) h = 2
    · right
      exact hTie (congrArg BitVec.toNat heq)
    · left
      simpa [heq]

theorem rConditions_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPivot : IsMinimalPivot G C)
    (hqQ : q ∈ C.Q) (hB : C.B = C.P ∪ {q})
    (hRSingleton : C.R = {(L.a 7).1}) (hk : C.k = 2) (hr : C.r = 6) :
    rConditions (graphBits G C q L) = true := by
  let u := (L.a 7).1
  have huA : u ∈ C.A := (L.a 7).2
  have hI := rInternalOut_toNat G C q L hG hRSingleton
  have hB' := rBOut_toNat G C q L hqQ hB
  have hSplit := A_outdegree_eq_A_add_B G C hG u huA
  have hPiv := hPivot u huA
  have hILe : (rInternalOut (graphBits G C q L)).toNat ≤ 8 := by
    rw [hI]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr L.a).symm)
  have hBLe : (rBOut (graphBits G C q L)).toNat ≤ 7 := by
    rw [hB']
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (by
        rw [hB]
        have hPq : Disjoint C.P {q} := by
          rw [Finset.disjoint_singleton_right]
          exact fun hqP => (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hqP hqQ
        rw [Finset.card_union_of_disjoint hPq]
        have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.low.p).symm
        simp [hp])
  have hMinI : 2 ≤ (rInternalOut (graphBits G C q L)).toNat := by
    rw [hI]
    have hp := hPiv.1
    change C.k ≤ directCount G C.A u at hp
    rw [hk] at hp
    simpa [u] using hp
  have hTotal : 8 ≤ (rInternalOut (graphBits G C q L)).toNat +
      (rBOut (graphBits G C q L)).toNat := by
    rw [hI, hB', ← hSplit]
    exact hMin u
  have hTie : (rInternalOut (graphBits G C q L)).toNat = 2 →
      6 ≤ (rBOut (graphBits G C q L)).toNat := by
    intro heq
    rw [hI] at heq
    rw [hB']
    have hEq : (C.A.filter (G.Adj u)).card = C.k := by
      change directCount G C.A u = C.k
      rw [hk]
      simpa [u] using heq
    have ht := hPiv.2 hEq
    change C.r ≤ directCount G C.B u at ht
    rw [hr] at ht
    simpa [u] using ht
  simp only [rConditions, Bool.and_eq_true, BitVec.ule_eq_decide,
    decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨hMinI, ?_⟩, ?_⟩
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact hTotal
  · by_cases heq : rInternalOut (graphBits G C q L) = 2
    · right
      exact hTie (congrArg BitVec.toNat heq)
    · left
      simpa [heq]

theorem everyXReached_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented) (hk : C.k = 2) :
    everyXReached (graphBits G C q L) = true := by
  rw [everyXReached, Bridge.all_eq_true_iff]
  intro x hx
  have hxMem := L.low.h_x ⟨x, hx⟩
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_inter.mp hxMem).1 with ⟨u, hu, hux⟩
  rcases Finset.mem_union.mp hu with huA1 | huP
  · rw [Bool.or_eq_true]
    left
    rw [Bridge.any_eq_true_iff]
    have hPairSubset : ({(L.low.h (0 : Fin 6)).1,
        (L.low.h (1 : Fin 6)).1} : Finset V) ⊆ C.A1 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact L.low.h_aOne 0
      · exact L.low.h_aOne 1
    have hPairCard : ({(L.low.h (0 : Fin 6)).1,
        (L.low.h (1 : Fin 6)).1} : Finset V).card = 2 := by
      have hne : (L.low.h (0 : Fin 6)).1 ≠ (L.low.h (1 : Fin 6)).1 := by
        intro heq
        have := L.low.h.injective (Subtype.ext heq)
        omega
      simp [hne]
    have hEq := Finset.eq_of_subset_of_card_le hPairSubset (by
      rw [hPairCard]
      change C.k ≤ 2
      omega)
    have huCases : u = (L.low.h (0 : Fin 6)).1 ∨
        u = (L.low.h (1 : Fin 6)).1 := by
      rw [← hEq] at huA1
      simpa [eq_comm] using huA1
    rcases huCases with h0 | h1
    · refine ⟨0, by omega, ?_⟩
      rw [hArc_graphBits G C q L hG 0 (2 + x) (by omega) (by omega)]
      apply decide_eq_true
      rw [h0] at hux
      have hfin : (⟨x + 2, by omega⟩ : Fin 6) =
          ⟨2 + x, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      simpa [hfin] using hux
    · refine ⟨1, by omega, ?_⟩
      rw [hArc_graphBits G C q L hG 1 (2 + x) (by omega) (by omega)]
      apply decide_eq_true
      rw [h1] at hux
      have hfin : (⟨x + 2, by omega⟩ : Fin 6) =
          ⟨2 + x, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      simpa [hfin] using hux
  · rw [Bool.or_eq_true]
    right
    rw [Bridge.any_eq_true_iff]
    obtain ⟨pi, hpi⟩ := L.low.p.surjective ⟨u, huP⟩
    refine ⟨pi, pi.isLt, ?_⟩
    rw [pToH_graphBits G C q L pi (2 + x) pi.isLt (by omega)]
    apply decide_eq_true
    have hpval : (L.low.p pi).1 = u := congrArg Subtype.val hpi
    rw [← hpval] at hux
    have hfin : (⟨x + 2, by omega⟩ : Fin 6) =
        ⟨2 + x, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    simpa [hfin] using hux

private theorem sum_fin18_eq_blocks (f : Fin 18 → Nat) :
    (∑ n, f n) = ∑ i : Fin 6, ∑ j : Fin 3,
      f ⟨i.val * 3 + j.val, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 3 ≃ Fin 18).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

private theorem sum_fin36_eq_blocks (f : Fin 36 → Nat) :
    (∑ n, f n) = ∑ i : Fin 6, ∑ j : Fin 6,
      f ⟨i.val * 6 + j.val, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin 36).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

theorem totalPE_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    (count 18 (fun n => pToE (graphBits G C q L) (n / 3) (n % 3))).toNat =
      edgeCount G C.P ({q} ∪ C.Z) := by
  rw [Bridge.toNat_count_eq_fin_sum 18 _ (by omega),
    sum_fin18_eq_blocks, edgeCount_eq_sum_fin G C.P ({q} ∪ C.Z) L.low.p]
  apply Finset.sum_congr rfl
  intro i hi
  rw [directCount_eq_sum_fin G ({q} ∪ C.Z) L.low.e]
  apply Finset.sum_congr rfl
  intro j hj
  have hd : (i.val * 3 + j.val) / 3 = i.val := by omega
  have hm : (i.val * 3 + j.val) % 3 = j.val := by
    simp
  simp only [hd, hm]
  rw [pToE_graphBits G C q L i j i.isLt j.isLt]

theorem totalPH_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    (count 36 (fun n => pToH (graphBits G C q L) (n / 6) (n % 6))).toNat =
      edgeCount G C.P C.H := by
  rw [Bridge.toNat_count_eq_fin_sum 36 _ (by omega),
    sum_fin36_eq_blocks, edgeCount_eq_sum_fin G C.P C.H L.low.p]
  apply Finset.sum_congr rfl
  intro i hi
  rw [directCount_eq_sum_fin G C.H L.low.h]
  apply Finset.sum_congr rfl
  intro j hj
  have hd : (i.val * 6 + j.val) / 6 = i.val := by omega
  have hm : (i.val * 6 + j.val) % 6 = j.val := by
    simp
  simp only [hd, hm]
  rw [pToH_graphBits G C q L i j i.isLt j.isLt]

theorem totalHP_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) :
    (count 36 (fun n => hToP (graphBits G C q L) (n / 6) (n % 6))).toNat =
      edgeCount G C.H C.P := by
  rw [Bridge.toNat_count_eq_fin_sum 36 _ (by omega),
    sum_fin36_eq_blocks, edgeCount_eq_sum_fin G C.H C.P L.low.h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [directCount_eq_sum_fin G C.P L.low.p]
  apply Finset.sum_congr rfl
  intro j hj
  have hd : (i.val * 6 + j.val) / 6 = i.val := by omega
  have hm : (i.val * 6 + j.val) % 6 = j.val := by
    simp
  simp only [hd, hm]
  rw [hToP_graphBits G C q L i j i.isLt j.isLt]

theorem totalPP_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented) :
    (count 30 (fun n =>
      let p := n / 5
      let j := n % 5
      pArc (graphBits G C q L) p (if j < p then j else j + 1))).toNat =
      edgeCount G C.P C.P := by
  let lowBits := Bridge.coreBits G.Adj (fun i => (L.low.p i).1)
    (fun i => (L.low.h i).1) (fun i => (L.low.e i).1)
  have hGraph := Bridge.totalPP_toNat G C.P C.H ({q} ∪ C.Z)
    L.low.p L.low.h L.low.e hG
  change (Core.totalPP lowBits).toNat = edgeCount G C.P C.P at hGraph
  rw [← hGraph]
  change (count 30 (fun n =>
      let p := n / 5
      let j := n % 5
      pArc (graphBits G C q L) p (if j < p then j else j + 1))).toNat =
    (count 30 (fun n =>
      let p := n / 5
      let j := n % 5
      Core.pArc lowBits p (if j < p then j else j + 1))).toNat
  rw [Bridge.toNat_count_eq_fin_sum 30 _ (by omega),
    Bridge.toNat_count_eq_fin_sum 30 _ (by omega)]
  apply Finset.sum_congr rfl
  intro n hn
  have hp : n.val / 5 < 6 := by omega
  have hj : n.val % 5 < 5 := Nat.mod_lt _ (by omega)
  let target := if n.val % 5 < n.val / 5 then n.val % 5 else n.val % 5 + 1
  have ht : target < 6 := by
    dsimp [target]
    split <;> omega
  have hne : n.val / 5 ≠ target := by
    dsimp [target]
    split <;> omega
  rw [pArc_graphBits G C q L hG (n / 5) target hp ht,
    Bridge.pArc_coreBits G.Adj _ _ _ (n / 5) target hp ht]
  simp [target, hne]

theorem totals_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 16)
    (hPP : edgeCount G C.P C.P = 15)
    (hPH : edgeCount G C.P C.H = 17)
    (hHP : 19 ≤ edgeCount G C.H C.P) :
    totals (graphBits G C q L) = true := by
  simp only [totals, Bool.and_eq_true]
  have hPEBool : (count 18 (fun n =>
      pToE (graphBits G C q L) (n / 3) (n % 3)) == 16) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPE_toNat G C q L, hPE]
    decide
  have hPPBool : (count 30 (fun n =>
      let p := n / 5
      let j := n % 5
      pArc (graphBits G C q L) p (if j < p then j else j + 1)) == 15) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPP_toNat G C q L hG, hPP]
    decide
  have hPHBool : (count 36 (fun n =>
      pToH (graphBits G C q L) (n / 6) (n % 6)) == 17) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPH_toNat G C q L, hPH]
    decide
  have hHPBool : (19 : BitVec 8).ule (count 36 fun n =>
      hToP (graphBits G C q L) (n / 6) (n % 6)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [totalHP_toNat G C q L]
    exact hHP
  exact ⟨⟨⟨hPEBool, hPPBool⟩, hPHBool⟩, hHPBool⟩

theorem pDegrees_eight (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 16)
    (hPP : edgeCount G C.P C.P = 15)
    (hPH : edgeCount G C.P C.H = 17) :
    ∀ p ∈ C.P, G.outdegree p = 8 := by
  have hSum : ∑ p ∈ C.P, G.outdegree p = 48 := by
    calc
      _ = ∑ p ∈ C.P, (directCount G C.P p + directCount G C.H p +
          directCount G ({q} ∪ C.Z) p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact P_outdegree_eq_blocks G C q L hqQ hCaptured p hp
      _ = edgeCount G C.P C.P + edgeCount G C.P C.H +
          edgeCount G C.P ({q} ∪ C.Z) := by
        unfold edgeCount
        simp only [Finset.sum_add_distrib]
      _ = 48 := by omega
  apply pointwise_eq_of_sum_eq_card_mul C.P G.outdegree 8
    (fun p hp => hMin p)
  have hpCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.low.p).symm
  simpa [hpCard] using hSum

def outsideSet (C : G.LocalConfiguration) (q : V) : Finset V :=
  G.outNeighborFinsetOf ({q} ∪ C.Z) \ retainedVertexSet G C q

noncomputable def paddedOutsideLabels (W : Finset V) :
    Fin 7 → Option V := fun i =>
  if hi : i.val < W.card then
    some ((finsetEquivFin W rfl) ⟨i.val, hi⟩).1
  else none

omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_some_mem (W : Finset V) (_hW : W.card ≤ 7)
    (i : Fin 7) (v : V)
    (hi : paddedOutsideLabels W i = some v) : v ∈ W := by
  classical
  unfold paddedOutsideLabels at hi
  split at hi
  · simp only [Option.some.injEq] at hi
    rw [← hi]
    exact ((finsetEquivFin W rfl) _).2
  · contradiction

omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_surjective (W : Finset V) (hW : W.card ≤ 7)
    {v : V} (hv : v ∈ W) :
    ∃ i : Fin 7, paddedOutsideLabels W i = some v := by
  classical
  let j : Fin W.card := (finsetEquivFin W rfl).symm ⟨v, hv⟩
  let i : Fin 7 := ⟨j.val, by omega⟩
  refine ⟨i, ?_⟩
  simp [paddedOutsideLabels, i, j]

omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_some_injective (W : Finset V) (_hW : W.card ≤ 7)
    {i j : Fin 7} {v : V}
    (hi : paddedOutsideLabels W i = some v)
    (hj : paddedOutsideLabels W j = some v) : i = j := by
  classical
  unfold paddedOutsideLabels at hi hj
  split at hi
  · split at hj
    · simp only [Option.some.injEq] at hi hj
      apply Fin.ext
      have heq : (⟨i.val, by assumption⟩ : Fin W.card) =
          ⟨j.val, by assumption⟩ := by
        apply (finsetEquivFin W rfl).injective
        apply Subtype.ext
        exact hi.trans hj.symm
      exact congrArg (fun x : Fin W.card => x.val) heq
    · contradiction
  · contradiction

omit [Fintype V] [DecidableEq V] in
theorem paddedOutsideLabels_count (W : Finset V) (hW : W.card ≤ 7)
    (Q : V → Prop) [DecidablePred Q] :
    (count 7 fun i =>
      if hi : i < 7 then
        match paddedOutsideLabels W ⟨i, hi⟩ with
        | some v => decide (Q v)
        | none => false
      else false).toNat = (W.filter Q).card := by
  classical
  let b : Nat → Bool := fun i =>
    if hi : i < 7 then
      match paddedOutsideLabels W ⟨i, hi⟩ with
      | some v => decide (Q v)
      | none => false
    else false
  change (count 7 b).toNat = (W.filter Q).card
  rw [Bridge.toNat_count 7 b (by omega),
    filterCard_eq_sum_fin W (finsetEquivFin W rfl) Q]
  rw [show 7 = W.card + (7 - W.card) by omega, Finset.sum_range_add]
  have hFirst :
      (∑ i ∈ Finset.range W.card,
        (bitCount (b i)).toNat) =
        ∑ i : Fin W.card, if Q ((finsetEquivFin W rfl) i).1 then 1 else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [b, paddedOutsideLabels, show i.val < 7 by omega]
    split <;> simp_all [bitCount]
  rw [hFirst]
  simp only [add_eq_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hiRange := Finset.mem_range.mp hi
  simp [b, paddedOutsideLabels, bitCount]

theorem outsideSet_card_le_seven (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 16)
    (hPP : edgeCount G C.P C.P = 15)
    (hPH : edgeCount G C.P C.H = 17) :
    (outsideSet G C q).card ≤ 7 := by
  let E := {q} ∪ C.Z
  have hECard : E.card = 3 := by
    rw [← Fintype.card_coe]
    simpa [E] using (Fintype.card_congr L.low.e).symm
  have hpFull : ∃ p ∈ C.P, directCount G E p = 3 := by
    by_contra hn
    push Not at hn
    have hEach : ∀ p ∈ C.P, directCount G E p ≤ 2 := by
      intro p hp
      have hle : (E.filter (G.Adj p)).card ≤ E.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      change directCount G E p ≤ E.card at hle
      rw [hECard] at hle
      have hne : directCount G E p ≠ 3 := hn p hp
      omega
    have hUpper : edgeCount G C.P E ≤ 12 := by
      calc
        _ ≤ ∑ _p ∈ C.P, 2 := by
          unfold edgeCount
          apply Finset.sum_le_sum
          exact hEach
        _ = 12 := by
          have hpCard : C.P.card = 6 := by
            simpa using (Fintype.card_congr L.low.p).symm
          simp [hpCard]
    change edgeCount G C.P E = 16 at hPE
    omega
  obtain ⟨p, hpP, hpFull⟩ := hpFull
  have hAllE : ∀ e ∈ E, G.Adj p e := by
    intro e he
    have hEq : E.filter (G.Adj p) = E := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa [directCount, internalFirstNeighbors, hECard] using hpFull.symm.le
    exact (Finset.mem_filter.mp (hEq.symm ▸ he)).2
  have hpDegree := pDegrees_eight G C q L hqQ hMin hCaptured
    hPE hPP hPH p hpP
  have hWSecond : outsideSet G C q ⊆ G.secondOutNeighborFinset p := by
    intro v hvW
    rcases Finset.mem_sdiff.mp hvW with ⟨hvReach, hvOutside⟩
    obtain ⟨e, heE, hev⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hpv : ¬G.Adj p v := by
      intro hpv
      have hvCap := hCaptured p hpP
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv)
      apply hvOutside
      rcases Finset.mem_union.mp hvCap with hvPH | hvE
      · rcases Finset.mem_union.mp hvPH with hvP | hvH
        · exact Finset.mem_union_left {C.s}
            (Finset.mem_union_left E (Finset.mem_union_right C.A hvP))
        · exact Finset.mem_union_left {C.s}
            (Finset.mem_union_left E (Finset.mem_union_left C.P
              (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)))
      · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hvE)
    have hvp : v ≠ p := by
      intro hvp
      subst v
      apply hvOutside
      exact Finset.mem_union_left {C.s}
        (Finset.mem_union_left E (Finset.mem_union_right C.A hpP))
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨e, hAllE e heE, hev⟩, hpv, hvp⟩
  have hCard := Finset.card_le_card hWSecond
  have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    (fun hs => hNoSeymour ⟨p, hs⟩)
  change (outsideSet G C q).card ≤ G.secondOutdegree p at hCard
  omega

theorem eLocalCount_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (e : Nat) (he : e < 3) :
    (count 18 (eLocalArc (graphBits G C q L) e)).toNat =
      directCount G (retainedVertexSet G C q) (L.low.e ⟨e, he⟩).1 := by
  rw [Bridge.toNat_count_eq_fin_sum 18 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (retainedVertexSet G C q)
    (retainedLabelEquiv G C q L hqQ hG)
  intro j
  rw [retainedLabelEquiv_val]
  rw [eLocalArc_graphBits G C q L hG e j he j.isLt]
  simp

theorem outsideForESeven_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (W : Finset V) (hW : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) (e : Nat) (he : e < 3) :
    (outsideForESeven (graphBits G C q L) e).toNat =
      directCount G W (L.low.e ⟨e, he⟩).1 := by
  unfold outsideForESeven directCount internalFirstNeighbors
  rw [Bridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  rw [← paddedOutsideLabels_count W hW
    (fun v => G.Adj (L.low.e ⟨e, he⟩).1 v)]
  rw [Bridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  apply Finset.sum_congr rfl
  intro i _
  rw [outsideAdjSeven_graphBits G C q L i e i.isLt he, hw]
  simp

theorem eConditionsSeven_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) :
    eConditionsSeven (graphBits G C q L) = true := by
  rw [eConditionsSeven, Bridge.all_eq_true_iff]
  intro e he
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  let v := (L.low.e ⟨e, he⟩).1
  have hvE : v ∈ ({q} ∪ C.Z) := (L.low.e _).2
  have hDisjoint : Disjoint (retainedVertexSet G C q) W := by
    rw [Finset.disjoint_left]
    intro u huRet huW
    rw [hW] at huW
    exact (Finset.mem_sdiff.mp huW).2 huRet
  have hCaptured : G.outNeighborFinset v ⊆
      retainedVertexSet G C q ∪ W := by
    intro u hu
    by_cases huRet : u ∈ retainedVertexSet G C q
    · exact Finset.mem_union_left W huRet
    · apply Finset.mem_union_right _
      rw [hW]
      exact Finset.mem_sdiff.mpr
        ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          ⟨v, hvE, (Digraph.mem_outNeighborFinset (G := G)).mp hu⟩, huRet⟩
  have hDegree : G.outdegree v =
      directCount G (retainedVertexSet G C q) v + directCount G W v := by
    have h := outdegree_eq_directCount_of_captured G
      (retainedVertexSet G C q ∪ W) v hCaptured
    rw [directCount_union_of_disjoint G _ _ v hDisjoint] at h
    exact h
  have hLocalLe := count_toNat_le 18
    (eLocalArc (graphBits G C q L) e) (by omega)
  have hOutsideLe := count_toNat_le 7
    (outsideAdjSeven (graphBits G C q L) · e) (by omega)
  change (outsideForESeven (graphBits G C q L) e).toNat ≤ 7 at hOutsideLe
  unfold eDegreeSeven
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
    eLocalCount_toNat G C q L hqQ hG e he,
    outsideForESeven_toNat G C q L W hWCard hw e he,
    ← hDegree]
  exact hMin v

theorem aOneLocalArc_true_adj (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (target : Nat) (ht : target < 18)
    (ha : aOneLocalArc target = true) :
    G.Adj C.a1 (localVertex G C q L target) := by
  have hAOne (i : Fin 2) :
      G.Adj C.a1 (L.low.h ⟨i.val, by omega⟩).1 := by
    have hi := L.low.h_aOne i
    exact (Finset.mem_filter.mp hi).2
  have hP (i : Fin 6) : G.Adj C.a1 (L.low.p i).1 :=
    (Finset.mem_filter.mp (L.low.p i).2).2
  interval_cases target <;>
    simp_all [aOneLocalArc, localVertex]

theorem hReachesLocal_true_path (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q)
    (h target : Nat) (hh : h < 6) (ht : target < 18)
    (hReach : hReachesLocal (graphBits G C q L) h target = true) :
    ∃ middle, G.Adj (L.low.h ⟨h, hh⟩).1 middle ∧
      G.Adj middle (localVertex G C q L target) := by
  simp only [hReachesLocal, Bool.or_eq_true, Bool.and_eq_true] at hReach
  rcases hReach with (((hA | hR) | hH) | hP) | hQ
  · refine ⟨C.a1, ?_, aOneLocalArc_true_adj G C q L target ht hA.2⟩
    rw [hToAOne_graphBits G C q L h hh] at hA
    exact of_decide_eq_true hA.1
  · refine ⟨(L.a 7).1, ?_, ?_⟩
    · rw [hToR_graphBits G C q L h hh] at hR
      exact of_decide_eq_true hR.1
    · rw [rLocalArc_graphBits G C q L hG heZero target ht] at hR
      exact of_decide_eq_true hR.2
  · obtain ⟨middle, hm, hBoth⟩ :=
      (Bridge.any_eq_true_iff 6 _).mp hH
    rw [Bool.and_eq_true] at hBoth
    rcases hBoth with ⟨hmArc, hLast⟩
    refine ⟨(L.low.h ⟨middle, hm⟩).1, ?_, ?_⟩
    · rw [hArc_graphBits G C q L hG h middle hh hm] at hmArc
      exact of_decide_eq_true hmArc
    · rw [hLocalArc_graphBits G C q L hG heZero middle target hm ht] at hLast
      exact of_decide_eq_true hLast
  · obtain ⟨p, hp, hBoth⟩ :=
      (Bridge.any_eq_true_iff 6 _).mp hP
    rw [Bool.and_eq_true] at hBoth
    rcases hBoth with ⟨hpArc, hLast⟩
    refine ⟨(L.low.p ⟨p, hp⟩).1, ?_, ?_⟩
    · rw [hToP_graphBits G C q L h p hh hp] at hpArc
      exact of_decide_eq_true hpArc
    · rw [pLocalArc_graphBits G C q L hG hRoot target p ht hp] at hLast
      exact of_decide_eq_true hLast
  · refine ⟨q, ?_, ?_⟩
    · rw [hToQ_graphBits G C q L h hh] at hQ
      exact of_decide_eq_true hQ.1
    · have heZero' : (L.low.e ⟨0, by omega⟩).1 = q := by simpa using heZero
      rw [eLocalArc_graphBits G C q L hG 0 target (by omega) ht,
        heZero'] at hQ
      exact of_decide_eq_true hQ.2

theorem hStrictSecondLocal_true_mem (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q)
    (h target : Nat) (hh : h < 6) (ht : target < 18)
    (hSecond : hStrictSecondLocal (graphBits G C q L) h target = true) :
    localVertex G C q L target ∈
      G.secondOutNeighborFinset (L.low.h ⟨h, hh⟩).1 := by
  simp only [hStrictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hFirst, hLast⟩ := hReachesLocal_true_path G C q L hG
    hRoot heZero h target hh ht hReach
  have hVertexNe : localVertex G C q L target ≠ (L.low.h ⟨h, hh⟩).1 := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 18) = ⟨2 + h, by omega⟩ := by
      apply (retainedLabelEquiv G C q L hqQ hG).injective
      apply Subtype.ext
      rw [retainedLabelEquiv_val, retainedLabelEquiv_val]
      change localVertex G C q L target = localVertex G C q L (2 + h)
      rw [localVertex_h G C q L ⟨h, hh⟩]
      exact heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  refine ⟨⟨middle, hFirst, hLast⟩, ?_, hVertexNe⟩
  rw [hLocalArc_graphBits G C q L hG heZero h target hh ht] at hNotArc
  simpa using hNotArc

theorem hLocalCount_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (heZero : (L.low.e 0).1 = q) (h : Nat) (hh : h < 6) :
    (count 18 (hLocalArc (graphBits G C q L) h)).toNat =
      directCount G (retainedVertexSet G C q) (L.low.h ⟨h, hh⟩).1 := by
  rw [Bridge.toNat_count_eq_fin_sum 18 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (retainedVertexSet G C q)
    (retainedLabelEquiv G C q L hqQ hG)
  intro j
  rw [retainedLabelEquiv_val]
  rw [hLocalArc_graphBits G C q L hG heZero h j hh j.isLt]
  simp

theorem hOutDegree_eq_localCount (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (heZero : (L.low.e 0).1 = q) (hB : C.B = C.P ∪ {q})
    (h : Nat) (hh : h < 6) :
    G.outdegree (L.low.h ⟨h, hh⟩).1 =
      (count 18 (hLocalArc (graphBits G C q L) h)).toNat := by
  let u := (L.low.h ⟨h, hh⟩).1
  have huA : u ∈ C.A :=
    Digraph.LocalConfiguration.H_subset_A (G := G) C (L.low.h _).2
  have hCap : G.outNeighborFinset u ⊆ retainedVertexSet G C q := by
    intro v hv
    rcases Finset.mem_union.mp
        (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
          G C hG u huA hv) with hvA | hvB
    · exact Finset.mem_union_left {C.s}
        (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P hvA))
    · rw [hB] at hvB
      rcases Finset.mem_union.mp hvB with hvP | hvq
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hvP))
      · exact Finset.mem_union_left {C.s}
          (Finset.mem_union_right (C.A ∪ C.P) (Finset.mem_union_left C.Z hvq))
  rw [hLocalCount_toNat G C q L hqQ hG heZero h hh]
  exact outdegree_eq_directCount_of_captured G _ u hCap

theorem xConditionsSeven_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q) (hB : C.B = C.P ∪ {q})
    (hNoSeymour : ¬G.HasSeymourVertex)
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) :
    xConditionsSeven (graphBits G C q L) = true := by
  rw [xConditionsSeven, Bridge.all_eq_true_iff]
  intro x hx
  let h := 2 + x
  let source := (L.low.h ⟨h, by omega⟩).1
  let localSecond := (retainedVertexSet G C q).filter
    (fun v => v ∈ G.secondOutNeighborFinset source)
  by_cases hqArc : G.Adj source q
  · let outsideSecond := W.filter (G.Adj q)
    have hLocalLe :
        (hLocalSecondCount (graphBits G C q L) h).toNat ≤ localSecond.card := by
      apply Bridge.count_le_filterCard (retainedVertexSet G C q)
        (retainedLabelEquiv G C q L hqQ hG)
        (hStrictSecondLocal (graphBits G C q L) h)
        (fun v => v ∈ G.secondOutNeighborFinset source) (by omega)
      intro j hj
      rw [retainedLabelEquiv_val]
      exact hStrictSecondLocal_true_mem G C q L hqQ hG hRoot heZero
        h j (by omega) j.isLt hj
    have hOutsideEq :
        (hOutsideSecondSeven (graphBits G C q L) h).toNat =
          outsideSecond.card := by
      unfold hOutsideSecondSeven
      rw [hToQ_graphBits G C q L h (by omega)]
      simp only [source] at hqArc
      rw [decide_eq_true hqArc]
      change (outsideForESeven (graphBits G C q L) 0).toNat = _
      rw [outsideForESeven_toNat G C q L W hWCard hw 0 (by omega)]
      have heZero' : (L.low.e ⟨0, by omega⟩).1 = q := by simpa using heZero
      unfold directCount internalFirstNeighbors outsideSecond
      apply congrArg Finset.card
      ext v
      simp only [Finset.mem_filter]
      rw [heZero']
    have hDisjoint : Disjoint localSecond outsideSecond := by
      rw [Finset.disjoint_left]
      intro v hvLocal hvOutside
      have hvRet := (Finset.mem_filter.mp hvLocal).1
      have hvW := (Finset.mem_filter.mp hvOutside).1
      rw [hW] at hvW
      exact (Finset.mem_sdiff.mp hvW).2 hvRet
    have hOutsideSubset : outsideSecond ⊆ G.secondOutNeighborFinset source := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvW, hqv⟩
      have hvOutside : v ∉ retainedVertexSet G C q := by
        rw [hW] at hvW
        exact (Finset.mem_sdiff.mp hvW).2
      have hsv : ¬G.Adj source v := by
        intro hsv
        have hsA : source ∈ C.A :=
          Digraph.LocalConfiguration.H_subset_A (G := G) C (L.low.h _).2
        have hvCap := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
          G C hG source hsA
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv)
        apply hvOutside
        rcases Finset.mem_union.mp hvCap with hvA | hvB
        · exact Finset.mem_union_left {C.s}
            (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P hvA))
        · rw [hB] at hvB
          rcases Finset.mem_union.mp hvB with hvP | hvq
          · exact Finset.mem_union_left {C.s}
              (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hvP))
          · exact Finset.mem_union_left {C.s}
              (Finset.mem_union_right (C.A ∪ C.P) (Finset.mem_union_left C.Z hvq))
      have hvSource : v ≠ source := by
        intro hv
        apply hvOutside
        rw [hv]
        exact Finset.mem_union_left {C.s}
          (Finset.mem_union_left ({q} ∪ C.Z)
            (Finset.mem_union_left C.P
              (Digraph.LocalConfiguration.H_subset_A (G := G) C (L.low.h _).2)))
      rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨q, hqArc, hqv⟩, hsv, hvSource⟩
    have hUnionSubset : localSecond ∪ outsideSecond ⊆
        G.secondOutNeighborFinset source := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_filter.mp hv).2
      · exact hOutsideSubset hv
    have hCard := Finset.card_le_card hUnionSubset
    rw [Finset.card_union_of_disjoint hDisjoint] at hCard
    have hSecondLt := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hs => hNoSeymour ⟨source, hs⟩)
    have hDirect := hOutDegree_eq_localCount G C q L hqQ hG heZero hB h (by omega)
    have hLocalBound := count_toNat_le 18
      (hStrictSecondLocal (graphBits G C q L) h) (by omega)
    have hOutsideBound :
        (hOutsideSecondSeven (graphBits G C q L) h).toNat ≤ 7 := by
      rw [hOutsideEq]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hWCard
    change (hLocalSecondCount (graphBits G C q L) h).toNat ≤ 18 at hLocalBound
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    dsimp [h] at hLocalLe hOutsideEq hDirect hLocalBound hOutsideBound ⊢
    have hDirect' : G.outdegree source =
        (count 18 (hLocalArc (graphBits G C q L) (2 + x))).toNat := by
      simpa [source, h] using hDirect
    unfold hLocalSecondCount at hLocalBound hLocalLe ⊢
    rw [Nat.mod_eq_of_lt (by omega), hOutsideEq, ← hDirect']
    change localSecond.card + outsideSecond.card ≤ G.secondOutdegree source at hCard
    dsimp [source] at hCard hSecondLt ⊢
    omega
  · have hOutsideZero : hOutsideSecondSeven (graphBits G C q L) h = 0 := by
      unfold hOutsideSecondSeven
      rw [hToQ_graphBits G C q L h (by omega)]
      simp [source] at hqArc
      simp [hqArc]
    have hLocalLe :
        (hLocalSecondCount (graphBits G C q L) h).toNat ≤
          G.secondOutdegree source := by
      have hFiltered := Bridge.count_le_filterCard (retainedVertexSet G C q)
        (retainedLabelEquiv G C q L hqQ hG)
        (hStrictSecondLocal (graphBits G C q L) h)
        (fun v => v ∈ G.secondOutNeighborFinset source) (by omega) (by
          intro j hj
          rw [retainedLabelEquiv_val]
          exact hStrictSecondLocal_true_mem G C q L hqQ hG hRoot heZero
            h j (by omega) j.isLt hj)
      apply hFiltered.trans
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    have hSecondLt := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hs => hNoSeymour ⟨source, hs⟩)
    have hDirect := hOutDegree_eq_localCount G C q L hqQ hG heZero hB h (by omega)
    have hLocalBound := count_toNat_le 18
      (hStrictSecondLocal (graphBits G C q L) h) (by omega)
    change (hLocalSecondCount (graphBits G C q L) h).toNat ≤ 18 at hLocalBound
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
    dsimp [h] at hOutsideZero hLocalLe hDirect hLocalBound ⊢
    rw [hOutsideZero]
    change ((hLocalSecondCount (graphBits G C q L) (2 + x)).toNat + 0) % 256 < _
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [← hDirect]
    simpa [source] using hLocalLe.trans_lt hSecondLt

omit [Fintype V] [DecidableEq V] in
theorem filterCard_le_count {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, Q (e j).1 → b j = true) :
    (S.filter Q).card ≤ (count n b).toNat := by
  classical
  rw [Bridge.toNat_count_eq_fin_sum n b hn,
    filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j _
  by_cases hQ : Q (e j).1
  · simp [hQ, hGood j hQ]
  · simp [hQ]

theorem retainedReachesLocal_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q)
    (p deleted target : Nat) (hp : p < 6) (hd : deleted < 3)
    (ht : target < 18) (middle : V)
    (hm : middle ∈ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hmNeDeleted : middle ≠ (L.low.e ⟨deleted, hd⟩).1)
    (hFirst : G.Adj (L.low.p ⟨p, hp⟩).1 middle)
    (hLast : G.Adj middle (localVertex G C q L target)) :
    retainedReachesLocal (graphBits G C q L) p deleted target = true := by
  unfold retainedReachesLocal
  simp only [Bool.or_eq_true]
  rcases Finset.mem_union.mp hm with hmPH | hmE
  · rcases Finset.mem_union.mp hmPH with hmP | hmH
    · left; left
      rw [Bridge.any_eq_true_iff]
      obtain ⟨i, hi⟩ := L.low.p.surjective ⟨middle, hmP⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [Bool.and_eq_true]
      constructor
      · rw [pArc_graphBits G C q L hG p i hp i.isLt]
        exact decide_eq_true (by simpa [congrArg Subtype.val hi] using hFirst)
      · rw [pLocalArc_graphBits G C q L hG hRoot target i ht i.isLt]
        exact decide_eq_true (by simpa [congrArg Subtype.val hi] using hLast)
    · left; right
      rw [Bridge.any_eq_true_iff]
      obtain ⟨i, hi⟩ := L.low.h.surjective ⟨middle, hmH⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [Bool.and_eq_true]
      constructor
      · rw [pToH_graphBits G C q L p i hp i.isLt]
        exact decide_eq_true (by simpa [congrArg Subtype.val hi] using hFirst)
      · rw [hLocalArc_graphBits G C q L hG heZero i target i.isLt ht]
        exact decide_eq_true (by simpa [congrArg Subtype.val hi] using hLast)
  · right
    rw [Bridge.any_eq_true_iff]
    obtain ⟨i, hi⟩ := L.low.e.surjective ⟨middle, hmE⟩
    have hival : (L.low.e i).1 = middle := congrArg Subtype.val hi
    have hine : i.val ≠ deleted := by
      intro hieq
      apply hmNeDeleted
      rw [← hival]
      congr 2
      exact Fin.ext hieq
    refine ⟨i, i.isLt, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hine, ?_⟩, ?_⟩
    · rw [pToE_graphBits G C q L p i hp i.isLt]
      apply decide_eq_true
      rw [hival]
      exact hFirst
    · rw [eLocalArc_graphBits G C q L hG i target i.isLt ht]
      apply decide_eq_true
      rw [hival]
      exact hLast

theorem pLocalCount_toNat (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hRoot : edgeCount G C.P {C.s} = 0) (p : Nat) (hp : p < 6) :
    (pOut (graphBits G C q L) p).toNat =
      directCount G (retainedVertexSet G C q) (L.low.p ⟨p, hp⟩).1 := by
  unfold pOut
  rw [Bridge.toNat_count_eq_fin_sum 18 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (retainedVertexSet G C q)
    (retainedLabelEquiv G C q L hqQ hG)
  intro j
  rw [retainedLabelEquiv_val]
  rw [pLocalArc_graphBits G C q L hG hRoot j p j.isLt hp]
  simp

omit [Fintype V] [DecidableEq V] in
theorem paddedOutside_count_le (W : Finset V) (hW : W.card ≤ 7)
    (Q : V → Prop) [DecidablePred Q] (b : Nat → Bool)
    (hGood : ∀ i : Fin 7,
      (match paddedOutsideLabels W i with
        | some v => decide (Q v)
        | none => false) = true → b i = true) :
    (W.filter Q).card ≤ (count 7 b).toNat := by
  classical
  rw [← paddedOutsideLabels_count W hW Q]
  rw [Bridge.toNat_count_eq_fin_sum 7 _ (by omega),
    Bridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  apply Finset.sum_le_sum
  intro i _
  let a := match paddedOutsideLabels W i with
    | some v => decide (Q v)
    | none => false
  by_cases ha : a = true
  · have hb := hGood i ha
    simp [a, ha, hb]
  · have haf : a = false := Bool.eq_false_of_not_eq_true ha
    simp [a, haf]

theorem auxiliaryDeletionPConditionsSeven_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q) (hB : C.B = C.P ∪ {q})
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hDegrees : ∀ p ∈ C.P, G.outdegree p = 8)
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) :
    auxiliaryDeletionPConditionsSeven (graphBits G C q L) = true := by
  rw [auxiliaryDeletionPConditionsSeven, Bridge.all_eq_true_iff]
  intro p hp
  rw [Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [pLocalCount_toNat G C q L hqQ hG hRoot p hp]
    let source := (L.low.p ⟨p, hp⟩).1
    have hpP : source ∈ C.P := (L.low.p _).2
    have hCap : G.outNeighborFinset source ⊆ retainedVertexSet G C q := by
      intro v hv
      rcases Finset.mem_union.mp (hCaptured source hpP hv) with hvPH | hvE
      · rcases Finset.mem_union.mp hvPH with hvP | hvH
        · exact Finset.mem_union_left {C.s}
            (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hvP))
        · exact Finset.mem_union_left {C.s}
            (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P
              (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)))
      · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hvE)
    rw [← outdegree_eq_directCount_of_captured G _ source hCap, hDegrees source hpP]
    decide
  · rw [Bridge.all_eq_true_iff]
    intro deleted hd
    by_cases hArc : pToE (graphBits G C q L) p deleted = true
    · rw [hArc]
      simp only [Bool.not_true, Bool.false_or]
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      let source := (L.low.p ⟨p, hp⟩).1
      let deletedVertex := (L.low.e ⟨deleted, hd⟩).1
      let S := (G.outNeighborFinset source).erase deletedVertex
      let expansion := G.outNeighborFinsetOf S \ (S ∪ {source})
      have hpP : source ∈ C.P := (L.low.p _).2
      have hGraphArc : G.Adj source deletedVertex := by
        rw [pToE_graphBits G C q L p deleted hp hd] at hArc
        exact of_decide_eq_true hArc
      have hExpansion : 7 ≤ expansion.card := by
        simpa [source, deletedVertex, S, expansion] using
          Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour
            (hDegrees source hpP) hGraphArc
      have hExpansionCaptured : expansion ⊆ retainedVertexSet G C q ∪ W := by
        intro v hv
        rcases Finset.mem_sdiff.mp hv with ⟨hvReach, _⟩
        obtain ⟨middle, hmS, hmv⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
        have hmOut : middle ∈ G.outNeighborFinset source := Finset.mem_of_mem_erase hmS
        have hmCap := hCaptured source hpP hmOut
        rcases Finset.mem_union.mp hmCap with hmPH | hmE
        · rcases Finset.mem_union.mp hmPH with hmP | hmH
          · exact Finset.mem_union_left W (by
              rcases Finset.mem_union.mp (hCaptured middle hmP
                  ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)) with hvPH | hvE
              · rcases Finset.mem_union.mp hvPH with hvP | hvH
                · exact Finset.mem_union_left {C.s}
                    (Finset.mem_union_left ({q} ∪ C.Z)
                      (Finset.mem_union_right C.A hvP))
                · exact Finset.mem_union_left {C.s}
                    (Finset.mem_union_left ({q} ∪ C.Z)
                      (Finset.mem_union_left C.P
                        (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)))
              · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hvE))
          · have hmA := Digraph.LocalConfiguration.H_subset_A (G := G) C hmH
            rcases Finset.mem_union.mp
                (RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
                  G C hG middle hmA
                    ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)) with hvA | hvB
            · exact Finset.mem_union_left W (Finset.mem_union_left {C.s}
                (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P hvA)))
            · rw [hB] at hvB
              rcases Finset.mem_union.mp hvB with hvP | hvq
              · exact Finset.mem_union_left W (Finset.mem_union_left {C.s}
                  (Finset.mem_union_left ({q} ∪ C.Z)
                    (Finset.mem_union_right C.A hvP)))
              · exact Finset.mem_union_left W (Finset.mem_union_left {C.s}
                  (Finset.mem_union_right (C.A ∪ C.P)
                    (Finset.mem_union_left C.Z hvq)))
        · by_cases hvRet : v ∈ retainedVertexSet G C q
          · exact Finset.mem_union_left W hvRet
          · apply Finset.mem_union_right _
            rw [hW]
            exact Finset.mem_sdiff.mpr
              ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr
                ⟨middle, hmE, hmv⟩, hvRet⟩
      let localExpansion := (retainedVertexSet G C q).filter (fun v => v ∈ expansion)
      let outsideExpansion := W.filter (fun v => v ∈ expansion)
      have hParts : expansion.card ≤ localExpansion.card + outsideExpansion.card := by
        have hSub : expansion ⊆ localExpansion ∪ outsideExpansion := by
          intro v hv
          rcases Finset.mem_union.mp (hExpansionCaptured hv) with hvRet | hvW'
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvRet, hv⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvW', hv⟩)
        have hCard := Finset.card_le_card hSub
        have hDisjoint : Disjoint localExpansion outsideExpansion := by
          rw [Finset.disjoint_left]
          intro v hvLocal hvOutside
          have hvRet := (Finset.mem_filter.mp hvLocal).1
          have hvW' := (Finset.mem_filter.mp hvOutside).1
          rw [hW] at hvW'
          exact (Finset.mem_sdiff.mp hvW').2 hvRet
        rw [Finset.card_union_of_disjoint hDisjoint] at hCard
        exact hCard
      have hLocalCount : localExpansion.card ≤
          (count 18 (deletionLocalTarget (graphBits G C q L) p deleted)).toNat := by
        apply filterCard_le_count (retainedVertexSet G C q)
          (retainedLabelEquiv G C q L hqQ hG)
          (deletionLocalTarget (graphBits G C q L) p deleted)
          (fun v => v ∈ expansion) (by omega)
        intro target htExpansion
        rw [retainedLabelEquiv_val] at htExpansion
        rcases Finset.mem_sdiff.mp htExpansion with ⟨htReach, htOutside⟩
        obtain ⟨middle, hmS, hmt⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
        have hmOut : middle ∈ G.outNeighborFinset source := Finset.mem_of_mem_erase hmS
        have hmNeDeleted : middle ≠ deletedVertex := (Finset.mem_erase.mp hmS).1
        have hmCap := hCaptured source hpP hmOut
        have hReach := retainedReachesLocal_true G C q L hG hRoot heZero
          p deleted target hp hd target.isLt middle hmCap hmNeDeleted
          ((Digraph.mem_outNeighborFinset (G := G)).mp hmOut) hmt
        have htNeSource : target.val ≠ 8 + p := by
          intro heq
          apply htOutside
          apply Finset.mem_union_right S
          apply Finset.mem_singleton.mpr
          dsimp [source]
          rw [show target.val = 8 + p by exact heq]
          exact localVertex_p G C q L ⟨p, hp⟩
        unfold deletionLocalTarget
        rw [Bool.and_eq_true]
        refine ⟨decide_eq_true htNeSource, ?_⟩
        split
        · exact hReach
        · rw [Bool.and_eq_true]
          refine ⟨?_, hReach⟩
          by_cases hDirect : pLocalArc (graphBits G C q L) p target = true
          · exfalso
            rw [pLocalArc_graphBits G C q L hG hRoot target p target.isLt hp]
              at hDirect
            have hGraphDirect := of_decide_eq_true hDirect
            apply htOutside
            apply Finset.mem_union_left {source}
            apply Finset.mem_erase.mpr
            constructor
            · intro htDeleted
              have hIndex : target.val = 14 + deleted := by
                have hv : localVertex G C q L target = deletedVertex := by
                  simpa [deletedVertex] using htDeleted
                have hFin : target = ⟨14 + deleted, by omega⟩ := by
                  apply (retainedLabelEquiv G C q L hqQ hG).injective
                  apply Subtype.ext
                  rw [retainedLabelEquiv_val, retainedLabelEquiv_val]
                  change localVertex G C q L target = localVertex G C q L (14 + deleted)
                  rw [localVertex_e G C q L ⟨deleted, hd⟩]
                  exact hv
                exact Fin.ext_iff.mp hFin
              contradiction
            · exact (Digraph.mem_outNeighborFinset (G := G)).mpr hGraphDirect
          · have hf := Bool.eq_false_of_not_eq_true hDirect
            simp [hf]
      let outsideQ : V → Prop := fun v => ∃ e : Fin 3,
        e.val ≠ deleted ∧ G.Adj source (L.low.e e).1 ∧ G.Adj (L.low.e e).1 v
      have hOutsideExpansionQ : outsideExpansion ⊆ W.filter outsideQ := by
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvW', hvExpansion⟩
        apply Finset.mem_filter.mpr
        refine ⟨hvW', ?_⟩
        rcases Finset.mem_sdiff.mp hvExpansion with ⟨hvReach, _⟩
        obtain ⟨middle, hmS, hmv⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
        have hmOut : middle ∈ G.outNeighborFinset source := Finset.mem_of_mem_erase hmS
        have hmCap := hCaptured source hpP hmOut
        have hvNotRet : v ∉ retainedVertexSet G C q := by
          rw [hW] at hvW'
          exact (Finset.mem_sdiff.mp hvW').2
        rcases Finset.mem_union.mp hmCap with hmPH | hmE
        · rcases Finset.mem_union.mp hmPH with hmP | hmH
          · have hvCap := hCaptured middle hmP
                ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
            apply (hvNotRet ?_).elim
            rcases Finset.mem_union.mp hvCap with hvPH | hvE
            · rcases Finset.mem_union.mp hvPH with hvP | hvH
              · exact Finset.mem_union_left {C.s}
                  (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hvP))
              · exact Finset.mem_union_left {C.s}
                  (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P
                    (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)))
            · exact Finset.mem_union_left {C.s} (Finset.mem_union_right _ hvE)
          · have hmA := Digraph.LocalConfiguration.H_subset_A (G := G) C hmH
            have hvCap := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
              G C hG middle hmA ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
            apply (hvNotRet ?_).elim
            rcases Finset.mem_union.mp hvCap with hvA | hvB
            · exact Finset.mem_union_left {C.s}
                (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_left C.P hvA))
            · rw [hB] at hvB
              rcases Finset.mem_union.mp hvB with hvP | hvq
              · exact Finset.mem_union_left {C.s}
                  (Finset.mem_union_left ({q} ∪ C.Z) (Finset.mem_union_right C.A hvP))
              · exact Finset.mem_union_left {C.s}
                  (Finset.mem_union_right (C.A ∪ C.P) (Finset.mem_union_left C.Z hvq))
        · obtain ⟨e, he⟩ := L.low.e.surjective ⟨middle, hmE⟩
          have heval : (L.low.e e).1 = middle := congrArg Subtype.val he
          refine ⟨e, ?_, ?_, ?_⟩
          · intro heq
            exact (Finset.mem_erase.mp hmS).1 (by
              rw [← heval]
              congr 2
              exact Fin.ext heq)
          · rw [heval]
            exact (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
          · rw [heval]
            exact hmv
      have hOutsideCount : outsideExpansion.card ≤
          (count 7 (retainedOutsideESeven (graphBits G C q L) p deleted)).toNat := by
        apply (Finset.card_le_card hOutsideExpansionQ).trans
        apply paddedOutside_count_le W hWCard outsideQ
          (retainedOutsideESeven (graphBits G C q L) p deleted)
        intro i hi
        cases hwi : paddedOutsideLabels W i with
        | none => simp [hwi] at hi
        | some v =>
          simp only [hwi, decide_eq_true_eq] at hi
          obtain ⟨e, heNe, hpe, hev⟩ := hi
          unfold retainedOutsideESeven
          rw [Bridge.any_eq_true_iff]
          refine ⟨e, e.isLt, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨heNe, ?_⟩, ?_⟩
          · rw [pToE_graphBits G C q L p e hp e.isLt]
            exact decide_eq_true hpe
          · rw [outsideAdjSeven_graphBits G C q L i e i.isLt e.isLt, hw, hwi]
            exact decide_eq_true hev
      have hLocalBound := count_toNat_le 18
        (deletionLocalTarget (graphBits G C q L) p deleted) (by omega)
      have hOutsideBound := count_toNat_le 7
        (retainedOutsideESeven (graphBits G C q L) p deleted) (by omega)
      change 7 ≤ (deletionCountESeven (graphBits G C q L) p deleted).toNat
      unfold deletionCountESeven
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hf : pToE (graphBits G C q L) p deleted = false :=
        Bool.eq_false_of_not_eq_true hArc
      simp [hf]

theorem pointwise_eq_of_sum_eq_card_mul_upper {W : Type*}
    (S : Finset W) (f : W → Nat) (d : Nat)
    (hUpper : ∀ v ∈ S, f v ≤ d)
    (hSum : ∑ v ∈ S, f v = S.card * d) :
    ∀ v ∈ S, f v = d := by
  classical
  intro v hv
  apply Nat.le_antisymm (hUpper v hv)
  by_contra hn
  have hStrict : f v < d := by omega
  have hSumStrict : (∑ w ∈ S, f w) < ∑ _w ∈ S, d := by
    apply Finset.sum_lt_sum hUpper
    exact ⟨v, hv, hStrict⟩
  simp [hSum] at hSumStrict

omit [Fintype V] [DecidableEq V] in
theorem complete_of_cross_edgeCount_max (S T : Finset V)
    (hG : G.IsOriented)
    (hMax : edgeCount G S T + edgeCount G T S = S.card * T.card)
    {u v : V} (hu : u ∈ S) (hv : v ∈ T) :
    G.Adj u v ∨ G.Adj v u := by
  classical
  let incident := fun v => directCount G S v + internalInDegree G S v
  have hIncident : ∀ v ∈ T, incident v ≤ S.card := by
    intro w hw
    have hDisjoint : Disjoint
        (internalFirstNeighbors G S w) (S.filter fun u => G.Adj u w) := by
      rw [Finset.disjoint_left]
      intro x hxOut hxIn
      exact hG.2 (Finset.mem_filter.mp hxOut).2 (Finset.mem_filter.mp hxIn).2
    change (internalFirstNeighbors G S w).card +
      (S.filter fun u => G.Adj u w).card ≤ S.card
    rw [← Finset.card_union_of_disjoint hDisjoint]
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hSum : ∑ v ∈ T, incident v = T.card * S.card := by
    calc
      _ = edgeCount G S T + edgeCount G T S := by
        dsimp [incident]
        rw [Finset.sum_add_distrib, edgeCount_eq_sum_incoming G S T]
        unfold edgeCount
        omega
      _ = S.card * T.card := hMax
      _ = T.card * S.card := Nat.mul_comm _ _
  have hvFull := pointwise_eq_of_sum_eq_card_mul_upper T incident S.card
    hIncident hSum v hv
  have hDisjoint : Disjoint
      (internalFirstNeighbors G S v) (S.filter fun u => G.Adj u v) := by
    rw [Finset.disjoint_left]
    intro x hxOut hxIn
    exact hG.2 (Finset.mem_filter.mp hxOut).2 (Finset.mem_filter.mp hxIn).2
  have hSubset : internalFirstNeighbors G S v ∪ (S.filter fun u => G.Adj u v) ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hEq : internalFirstNeighbors G S v ∪ (S.filter fun u => G.Adj u v) = S := by
    apply Finset.eq_of_subset_of_card_le hSubset
    rw [Finset.card_union_of_disjoint hDisjoint]
    change S.card ≤ directCount G S v + internalInDegree G S v
    exact hvFull.symm.le
  have huUnion : u ∈ internalFirstNeighbors G S v ∪ (S.filter fun u => G.Adj u v) :=
    hEq.symm ▸ hu
  rcases Finset.mem_union.mp huUnion with hvu | huv
  · exact Or.inr (Finset.mem_filter.mp hvu).2
  · exact Or.inl (Finset.mem_filter.mp huv).2

theorem saturatedPairRectangles_true (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hG : G.IsOriented)
    (hPP : edgeCount G C.P C.P = 15)
    (hPH : edgeCount G C.P C.H = 17)
    (hHP : 19 ≤ edgeCount G C.H C.P) :
    saturatedPairRectangles (graphBits G C q L) = true := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.low.p).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr L.low.h).symm
  have hCrossLe := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard, hPH] at hCrossLe
  have hHPExact : edgeCount G C.H C.P = 19 := by omega
  have hCrossMax : edgeCount G C.P C.H + edgeCount G C.H C.P =
      C.P.card * C.H.card := by
    rw [hPCard, hHCard, hPH, hHPExact]
  have hPPMax : edgeCount G C.P C.P = C.P.card.choose 2 := by
    rw [hPP, hPCard]
    decide
  unfold saturatedPairRectangles
  simp only [Bool.and_eq_true]
  constructor
  · constructor
    · rw [Bridge.all_eq_true_iff]
      intro p hp
      rw [Bridge.all_eq_true_iff]
      intro p' hp'
      by_cases heq : p = p'
      · simp [heq]
      · rw [decide_eq_false heq]
        simp only [Bool.false_or, Bool.or_eq_true]
        rcases RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
            G C.P hG hPPMax (L.low.p ⟨p, hp⟩).2 (L.low.p ⟨p', hp'⟩).2
            (by intro hv
                exact heq (Fin.ext_iff.mp (L.low.p.injective (Subtype.ext hv)))) with h | h
        · left
          rw [pArc_graphBits G C q L hG p p' hp hp']
          exact decide_eq_true h
        · right
          rw [pArc_graphBits G C q L hG p' p hp' hp]
          exact decide_eq_true h
    · rw [Bridge.all_eq_true_iff]
      intro p hp
      rw [Bridge.all_eq_true_iff]
      intro h hh
      rw [Bool.or_eq_true]
      rcases complete_of_cross_edgeCount_max G C.P C.H hG hCrossMax
          (L.low.p ⟨p, hp⟩).2 (L.low.h ⟨h, hh⟩).2 with hph | hhp
      · left
        rw [pToH_graphBits G C q L p h hp hh]
        exact decide_eq_true hph
      · right
        rw [hToP_graphBits G C q L h p hh hp]
        exact decide_eq_true hhp
  · rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalHP_toNat G C q L, hHPExact]
    decide

theorem exactTwo_false
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration) (q : V)
    (L : Labels G C q) (hqQ : q ∈ C.Q) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPivot : IsMinimalPivot G C)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRoot : edgeCount G C.P {C.s} = 0)
    (heZero : (L.low.e 0).1 = q) (hB : C.B = C.P ∪ {q})
    (hRSingleton : C.R = {(L.a 7).1}) (hk : C.k = 2) (hr : C.r = 6)
    (hq0 : G.Adj (L.low.h 0).1 q) (hq1 : G.Adj (L.low.h 1).1 q)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ ({q} ∪ C.Z))
    (hPE : edgeCount G C.P ({q} ∪ C.Z) = 16)
    (hPP : edgeCount G C.P C.P = 15)
    (hPH : edgeCount G C.P C.H = 17)
    (hHP : 19 ≤ edgeCount G C.H C.P)
    (hDegrees : ∀ p ∈ C.P, G.outdegree p = 8)
    (W : Finset V) (hW : W = outsideSet G C q) (hWCard : W.card ≤ 7)
    (hw : L.w = paddedOutsideLabels W) : False := by
  let bits := graphBits G C q L
  have hOriented : oriented bits = true := oriented_true G C q L hG heZero
  have hq0Bits : hToQ bits 0 = true := by
    rw [hToQ_graphBits G C q L 0 (by omega)]
    exact decide_eq_true hq0
  have hq1Bits : hToQ bits 1 = true := by
    rw [hToQ_graphBits G C q L 1 (by omega)]
    exact decide_eq_true hq1
  have hReached := everyXReached_true G C q L hG hk
  have hH := hConditions_true G C q L hG hMin hPivot hqQ hB
    hRSingleton hk hr
  have hR := rConditions_true G C q L hG hMin hPivot hqQ hB
    hRSingleton hk hr
  have hTotals := totals_true G C q L hG hPE hPP hPH hHP
  have hSaturated := saturatedPairRectangles_true G C q L hG hPP hPH hHP
  have hDeletion := auxiliaryDeletionPConditionsSeven_true G hBound C q L
    hqQ hG hNoSeymour hRoot heZero hB hCaptured hDegrees W hW hWCard hw
  have hX := xConditionsSeven_true G C q L hqQ hG hRoot heZero hB
    hNoSeymour W hW hWCard hw
  have hE := eConditionsSeven_true G C q L hqQ hG hMin W hW hWCard hw
  have hCore : projectedMinimalCore bits = true := by
    unfold projectedMinimalCore
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hOriented, hq0Bits⟩, hq1Bits⟩, hReached⟩,
      hH⟩, hR⟩, hTotals⟩, hSaturated⟩, hDeletion⟩, hX⟩, hE⟩
  rw [projectedMinimalCore_unsat bits] at hCore
  contradiction

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoProjectedBridge
