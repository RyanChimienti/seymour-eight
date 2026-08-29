import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XThreeReducedEncoding
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.XThreeAggregate
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XTwoGraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.HighDefect.Labels
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.HighDefect.GraphFacts
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.Assembly
import SeymourEight.Reduction
import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.EpsilonOneXThreeReducedGraphBridge

open BSevenKOne BSevenKOneCounting CertificateBridge Shared
  EpsilonOneXThreeReducedCore EpsilonOneXTwoGraphBridge
  FourZHighDefectGraphBridge FourZUnionEightAssembly TerminalAlphaBeta

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def retainedVertexSet (C : G.LocalConfiguration) : Finset V :=
  C.A ∪ C.P ∪ externalTargets G C

noncomputable def retainedLabelEquiv (C : G.LocalConfiguration)
    (hG : G.IsOriented)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C}) :
    Fin 19 ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin 19 → {v : V // v ∈ retainedVertexSet G C} := fun i =>
    if hiA : i.val < 8 then
      ⟨(a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left _ (Finset.mem_union_left _ (a ⟨i.val, hiA⟩).2)⟩
    else if hiP : i.val < 15 then
      ⟨(p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left _ (Finset.mem_union_right _ (p ⟨i.val - 8, by omega⟩).2)⟩
    else ⟨(e ⟨i.val - 15, by omega⟩).1,
      Finset.mem_union_right _ (e ⟨i.val - 15, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAP | hvE
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · obtain ⟨i, hi⟩ := a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega, show i.val + 8 < 15 by omega]
          using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hvE⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega, show ¬i.val + 15 < 15 by omega]
        using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hLocalE := BSixKThreeCoreGraphBridge.disjoint_local_external G C hG
    have hAPE : Disjoint (C.A ∪ C.P) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvAP hvE
      apply (Finset.disjoint_left.mp hLocalE) ?_ hvE
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · exact Finset.mem_union_left C.B hvA
      · exact Finset.mem_union_right C.A
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp]
    rw [retainedVertexSet, Finset.card_union_of_disjoint hAPE,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr a).symm
    have hp : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
    have he : (externalTargets G C).card = 4 := by
      simpa using (Fintype.card_congr e).symm
    simp only [Fintype.card_fin]
    omega

def labelledVertex (a : Fin 8 → V) (p : Fin 7 → V) (e : Fin 4 → V)
    (i : Nat) : V :=
  if hiA : i < 8 then a ⟨i, hiA⟩
  else if hiP : i < 15 then p ⟨i - 8, by omega⟩
  else if hiE : i < 19 then e ⟨i - 15, by omega⟩ else e 0

theorem protectedFinset_card_eq_four (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hk : C.k = 1) (hx : C.x = 3) :
    (BSevenKOne.protectedFinset G C).card = 4 := by
  have hRCount := x_add_card_R_eq_six G C hG hRootDegree hk
  have hDisjoint : Disjoint ({C.a1} : Finset V) C.R := by
    rw [Finset.disjoint_left]
    intro v hvPivot hvR
    have hv : v = C.a1 := Finset.mem_singleton.mp hvPivot
    subst v
    exact (Finset.mem_sdiff.mp hvR).2 (by simp)
  unfold BSevenKOne.protectedFinset
  rw [Finset.card_union_of_disjoint hDisjoint]
  simp
  omega

noncomputable def protectedLabelEquiv (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4) :
    Fin 4 ≃ {v : V // v ∈ BSevenKOne.protectedFinset G C} := by
  let f : Fin 4 → {v : V // v ∈ BSevenKOne.protectedFinset G C} := fun i =>
    if hi : i.val = 0 then
      ⟨(a 0).1, by simp [BSevenKOne.protectedFinset, hA0]⟩
    else
      ⟨(r ⟨i.val - 1, by omega⟩).1,
        Finset.mem_union_right _ (r ⟨i.val - 1, by omega⟩).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvA1 | hvR
    · have hvEq : v = C.a1 := Finset.mem_singleton.mp hvA1
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [f, hA0, hvEq]
    · obtain ⟨i, hi⟩ := r.surjective ⟨v, hvR⟩
      refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show i.val + 1 ≠ 0 by omega,
        show i.val + 1 - 1 = i.val by omega] using congrArg Subtype.val hi
  · simp [hCard]

@[simp] theorem protectedLabelEquiv_zero (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4) :
    (protectedLabelEquiv G C a r hA0 hCard 0).1 = (a 0).1 := by
  simp [protectedLabelEquiv]

@[simp] theorem protectedLabelEquiv_succ (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4)
    (i : Fin 3) :
    (protectedLabelEquiv G C a r hA0 hCard ⟨i.val + 1, by omega⟩).1 =
      (r i).1 := by
  simp [protectedLabelEquiv,
    show i.val + 1 - 1 = i.val by omega]

@[simp] theorem protectedLabelEquiv_one (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4) :
    (protectedLabelEquiv G C a r hA0 hCard 1).1 = (r 0).1 := by
  simp [protectedLabelEquiv]

@[simp] theorem protectedLabelEquiv_two (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4) :
    (protectedLabelEquiv G C a r hA0 hCard 2).1 = (r 1).1 := by
  simp [protectedLabelEquiv]

@[simp] theorem protectedLabelEquiv_three (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4) :
    (protectedLabelEquiv G C a r hA0 hCard 3).1 = (r 2).1 := by
  simp [protectedLabelEquiv]

@[simp] theorem retainedLabelEquiv_val (C : G.LocalConfiguration)
    (hG : G.IsOriented)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C}) (i : Fin 19) :
    (retainedLabelEquiv G C hG a p e i).1 =
      labelledVertex (fun j => (a j).1) (fun j => (p j).1) (fun j => (e j).1) i := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

omit [Fintype V] [DecidableEq V] in
theorem arc_coreBits
    (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0) (p i))
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i) (a 0))
    (hAH : ∀ i : Fin 4, a ⟨i + 1, by omega⟩ = h i)
    (hAR : ∀ i : Fin 3, a ⟨i + 5, by omega⟩ = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i) (r j))
    (hAE : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i) (e j))
    (u v : Nat) (hu : u < 15) (hv : v < 19) :
    arc (coreBits G.Adj p h e r a z) u v =
      decide (G.Adj (labelledVertex a p e u) (labelledVertex a p e v)) := by
  classical
  let bits := coreBits G.Adj p h e r a z
  have hA1 : a (1 : Fin 8) = h 0 := by simpa using hAH 0
  have hA2 : a (2 : Fin 8) = h 1 := by simpa using hAH 1
  have hA3 : a (3 : Fin 8) = h 2 := by simpa using hAH 2
  have hA4 : a (4 : Fin 8) = h 3 := by simpa using hAH 3
  have hA5 : a (5 : Fin 8) = r 0 := by simpa using hAR 0
  have hA6 : a (6 : Fin 8) = r 1 := by simpa using hAR 1
  have hA7 : a (7 : Fin 8) = r 2 := by simpa using hAR 2
  have hA1' (ph' : 0 < 4) (pa : 1 < 8) : h ⟨0, ph'⟩ = a ⟨1, pa⟩ := by
    simpa using hA1.symm
  have hA2' (ph' : 1 < 4) (pa : 2 < 8) : h ⟨1, ph'⟩ = a ⟨2, pa⟩ := by
    simpa using hA2.symm
  have hA3' (ph' : 2 < 4) (pa : 3 < 8) : h ⟨2, ph'⟩ = a ⟨3, pa⟩ := by
    simpa using hA3.symm
  have hA4' (ph' : 3 < 4) (pa : 4 < 8) : h ⟨3, ph'⟩ = a ⟨4, pa⟩ := by
    simpa using hA4.symm
  have hA5' (pr : 0 < 3) (pa : 5 < 8) : r ⟨0, pr⟩ = a ⟨5, pa⟩ := by
    simpa using hA5.symm
  have hA6' (pr : 1 < 3) (pa : 6 < 8) : r ⟨1, pr⟩ = a ⟨6, pa⟩ := by
    simpa using hA6.symm
  have hA7' (pr : 2 < 3) (pa : 7 < 8) : r ⟨2, pr⟩ = a ⟨7, pa⟩ := by
    simpa using hA7.symm
  by_cases huA : u < 8
  · rw [arc, if_pos huA]
    have hSource : labelledVertex a p e u = a ⟨u, huA⟩ := by
      simp [labelledVertex, huA]
    rw [hSource]
    by_cases hvA : v < 8
    · rw [if_pos hvA, aa_coreBits G.Adj p h e r a z u v huA hvA]
      simp [labelledVertex, hvA]
    by_cases hvP : v < 15
    · rw [if_neg hvA, if_pos hvP]
      have hvP' : v - 8 < 7 := by omega
      have hTarget : labelledVertex a p e v = p ⟨v - 8, hvP'⟩ := by
        simp [labelledVertex, hvA, hvP]
      rw [hTarget]
      rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨
          u = 5 ∨ u = 6 ∨ u = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [aToP] using hA0P ⟨v - 8, hvP'⟩
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hp_coreBits G.Adj p h e r a z 0 (v - 8) (by omega) hvP',
          hA1' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hp_coreBits G.Adj p h e r a z 1 (v - 8) (by omega) hvP',
          hA2' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hp_coreBits G.Adj p h e r a z 2 (v - 8) (by omega) hvP',
          hA3' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hp_coreBits G.Adj p h e r a z 3 (v - 8) (by omega) hvP',
          hA4' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rp_coreBits G.Adj p h e r a z 0 (v - 8) (by omega) hvP',
          hA5' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rp_coreBits G.Adj p h e r a z 1 (v - 8) (by omega) hvP',
          hA6' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rp_coreBits G.Adj p h e r a z 2 (v - 8) (by omega) hvP',
          hA7' (by omega) (by omega)]
    · rw [if_neg hvA, if_neg hvP]
      have hvE : v - 15 < 4 := by omega
      have hTarget : labelledVertex a p e v = e ⟨v - 15, hvE⟩ := by
        simp [labelledVertex, hvA, hvP, hv]
      rw [hTarget]
      simp [hAE]
  · rw [arc, if_neg huA, if_pos hu]
    have huP : u - 8 < 7 := by omega
    have hSource : labelledVertex a p e u = p ⟨u - 8, huP⟩ := by
      simp [labelledVertex, huA, hu]
    rw [hSource]
    by_cases hvA : v < 8
    · rw [if_pos hvA]
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨
          v = 5 ∨ v = 6 ∨ v = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [pToA, labelledVertex, huA, hu] using hP0 ⟨u - 8, huP⟩
      · rw [pToA, ph_coreBits G.Adj p h e r a z (u - 8) 0 huP (by omega),
          hA1' (by omega) (by omega)]
        simp [labelledVertex]
      · rw [pToA, ph_coreBits G.Adj p h e r a z (u - 8) 1 huP (by omega),
          hA2' (by omega) (by omega)]
        simp [labelledVertex]
      · rw [pToA, ph_coreBits G.Adj p h e r a z (u - 8) 2 huP (by omega),
          hA3' (by omega) (by omega)]
        simp [labelledVertex]
      · rw [pToA, ph_coreBits G.Adj p h e r a z (u - 8) 3 huP (by omega),
          hA4' (by omega) (by omega)]
        simp [labelledVertex]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (5 : Fin 8)) := by
          rw [hA5]
          exact hPR ⟨u - 8, huP⟩ 0
        simp [pToA, labelledVertex, hnot]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (6 : Fin 8)) := by
          rw [hA6]
          exact hPR ⟨u - 8, huP⟩ 1
        simp [pToA, labelledVertex, hnot]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (7 : Fin 8)) := by
          rw [hA7]
          exact hPR ⟨u - 8, huP⟩ 2
        simp [pToA, labelledVertex, hnot]
    by_cases hvP : v < 15
    · rw [if_neg hvA, if_pos hvP,
        pp_coreBits G.Adj p h e r a z (u - 8) (v - 8) huP (by omega)]
      simp [labelledVertex, hvA, hvP]
    · rw [if_neg hvA, if_neg hvP, if_pos hv,
        pe_coreBits G.Adj p h e r a z (u - 8) (v - 15) huP (by omega)]
      simp [labelledVertex, hvA, hvP, hv]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem reduced_toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (EpsilonOneXThreeReducedCore.count n f).toNat =
      ∑ i ∈ Finset.range n,
        (EpsilonOneXThreeReducedCore.bitCount (f i)).toNat := by
  induction n with
  | zero => simp [EpsilonOneXThreeReducedCore.count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hs : (∑ i ∈ Finset.range n,
          (EpsilonOneXThreeReducedCore.bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [EpsilonOneXThreeReducedCore.count, BitVec.toNat_add, ih hn',
        Finset.sum_range_succ]
      have hlt0 : (∑ i ∈ Finset.range n,
          (if f i then (1 : BitVec 8) else 0).toNat) < 256 := by
        simpa [EpsilonOneXThreeReducedCore.bitCount] using
          (show (∑ i ∈ Finset.range n,
            (EpsilonOneXThreeReducedCore.bitCount (f i)).toNat) < 256 by omega)
      have hlt1 : (∑ i ∈ Finset.range n,
          (if f i then (1 : BitVec 8) else 0).toNat) + 1 < 256 := by
        simpa [EpsilonOneXThreeReducedCore.bitCount] using
          (show (∑ i ∈ Finset.range n,
            (EpsilonOneXThreeReducedCore.bitCount (f i)).toNat) + 1 < 256 by omega)
      cases hfn : f n
      · simp only [EpsilonOneXThreeReducedCore.bitCount]
        exact Nat.mod_eq_of_lt hlt0
      · simp only [EpsilonOneXThreeReducedCore.bitCount]
        exact Nat.mod_eq_of_lt hlt1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem reduced_toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool)
    (hn : n < 256) :
    (EpsilonOneXThreeReducedCore.count n f).toNat =
      ∑ i : Fin n, if f i then 1 else 0 := by
  rw [reduced_toNat_count n f hn, ← Fin.sum_univ_eq_sum_range
    (fun i => (EpsilonOneXThreeReducedCore.bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [EpsilonOneXThreeReducedCore.bitCount]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem reduced_toNat_sumCount (n : Nat) (f : Nat → BitVec 8)
    (hlt : ∑ i ∈ Finset.range n, (f i).toNat < 256) :
    (EpsilonOneXThreeReducedCore.sumCount n f).toNat =
      ∑ i ∈ Finset.range n, (f i).toNat := by
  induction n with
  | zero => simp [EpsilonOneXThreeReducedCore.sumCount]
  | succ n ih =>
      have hprefix : ∑ i ∈ Finset.range n, (f i).toNat < 256 := by
        rw [Finset.sum_range_succ] at hlt
        omega
      rw [EpsilonOneXThreeReducedCore.sumCount, BitVec.toNat_add, ih hprefix,
        Finset.sum_range_succ]
      simp only [Nat.reducePow]
      apply Nat.mod_eq_of_lt
      simpa [Finset.sum_range_succ] using hlt

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem reduced_any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    EpsilonOneXThreeReducedCore.any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [EpsilonOneXThreeReducedCore.any]
  | succ n ih =>
      simp only [EpsilonOneXThreeReducedCore.any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hlast)
        · exact ⟨i, by omega, hfi⟩
        · exact ⟨n, by omega, hlast⟩
      · rintro ⟨i, hi, hfi⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hfi⟩
        · exact Or.inr (show i = n by omega ▸ hfi)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem reduced_all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    EpsilonOneXThreeReducedCore.all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [EpsilonOneXThreeReducedCore.all]
  | succ n ih =>
      simp only [EpsilonOneXThreeReducedCore.all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        by_cases hin : i < n
        · exact hprev i hin
        · simpa [show i = n by omega] using hlast
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

omit [Fintype V] [DecidableEq V] in
theorem pp_toNat (P : Finset V) (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 4 → V) (e : Fin 4 → V) (r : Fin 3 → V)
    (a : Fin 8 → V) (z : Fin 3 → V) (i : Nat) (hi : i < 7) :
    (pPOut (coreBits G.Adj (fun j => (p j).1) h e r a z) i).toNat =
      directCount G P (p ⟨i, hi⟩).1 := by
  classical
  rw [pPOut, reduced_toNat_count_eq_fin_sum 7 _ (by omega),
    Shared.directCount_eq_sum_fin G P p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pp_coreBits G.Adj (fun k => (p k).1) h e r a z i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem ph_toNat (H : Finset V) (p : Fin 7 → V)
    (h : Fin 4 ≃ {v : V // v ∈ H}) (e : Fin 4 → V) (r : Fin 3 → V)
    (a : Fin 8 → V) (z : Fin 3 → V) (i : Nat) (hi : i < 7) :
    (pHOut (coreBits G.Adj p (fun j => (h j).1) e r a z) i).toNat =
      directCount G H (p ⟨i, hi⟩) := by
  classical
  rw [pHOut, reduced_toNat_count_eq_fin_sum 4 _ (by omega),
    Shared.directCount_eq_sum_fin G H h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ph_coreBits G.Adj p (fun k => (h k).1) e r a z i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem hp_toNat (P : Finset V) (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 4 → V) (e : Fin 4 → V) (r : Fin 3 → V)
    (a : Fin 8 → V) (z : Fin 3 → V) (i : Nat) (hi : i < 4) :
    (EpsilonOneXThreeReducedCore.count 7 (hp
      (coreBits G.Adj (fun j => (p j).1) h e r a z) i)).toNat =
      directCount G P (h ⟨i, hi⟩) := by
  classical
  rw [reduced_toNat_count_eq_fin_sum 7 _ (by omega),
    Shared.directCount_eq_sum_fin G P p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hp_coreBits G.Adj (fun k => (p k).1) h e r a z i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem pe_toNat (E : Finset V) (p : Fin 7 → V) (h : Fin 4 → V)
    (e : Fin 4 ≃ {v : V // v ∈ E}) (r : Fin 3 → V)
    (a : Fin 8 → V) (z : Fin 3 → V) (i : Nat) (hi : i < 7) :
    (pEOut (coreBits G.Adj p h (fun j => (e j).1) r a z) i).toNat =
      directCount G E (p ⟨i, hi⟩) := by
  classical
  rw [pEOut, reduced_toNat_count_eq_fin_sum 4 _ (by omega),
    Shared.directCount_eq_sum_fin G E e]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pe_coreBits G.Adj p h (fun k => (e k).1) r a z i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem aa_toNat (A : Finset V) (p : Fin 7 → V) (h : Fin 4 → V)
    (e : Fin 4 → V) (r : Fin 3 → V)
    (a : Fin 8 ≃ {v : V // v ∈ A}) (z : Fin 3 → V)
    (i : Nat) (hi : i < 8) :
    (aOut (coreBits G.Adj p h e r (fun j => (a j).1) z) i).toNat =
      directCount G A (a ⟨i, hi⟩).1 := by
  classical
  rw [aOut, reduced_toNat_count_eq_fin_sum 8 _ (by omega),
    Shared.directCount_eq_sum_fin G A a]
  apply Finset.sum_congr rfl
  intro j hj
  rw [aa_coreBits G.Adj p h e r (fun k => (a k).1) z i j hi j.isLt]

omit [Fintype V] [DecidableEq V] in
theorem aP_toNat (P : Finset V) (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 4 → V) (e : Fin 4 → V) (r : Fin 3 → V)
    (a : Fin 8 → V) (z : Fin 3 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0) (p i).1)
    (hAH : ∀ i : Fin 4, a ⟨i + 1, by omega⟩ = h i)
    (hAR : ∀ i : Fin 3, a ⟨i + 5, by omega⟩ = r i)
    (source : Nat) (hs : source < 8) :
    (aPOut (coreBits G.Adj (fun i => (p i).1) h e r a z) source).toNat =
      directCount G P (a ⟨source, hs⟩) := by
  classical
  rw [aPOut, reduced_toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G P p
  intro j
  by_cases hs0 : source = 0
  · subst source
    simp [aToP, hA0P]
  by_cases hs5 : source < 5
  · have hi : source - 1 < 4 := by omega
    rw [aToP, if_neg hs0, if_pos hs5,
      hp_coreBits G.Adj (fun i => (p i).1) h e r a z
        (source - 1) j hi j.isLt]
    have heq := hAH ⟨source - 1, hi⟩
    have heq' : a ⟨source, hs⟩ = h ⟨source - 1, hi⟩ := by
      simpa [show source - 1 + 1 = source by omega] using heq
    rw [heq']
    simp
  · have hi : source - 5 < 3 := by omega
    rw [aToP, if_neg hs0, if_neg hs5,
      rp_coreBits G.Adj (fun i => (p i).1) h e r a z
        (source - 5) j hi j.isLt]
    have heq := hAR ⟨source - 5, hi⟩
    have heq' : a ⟨source, hs⟩ = r ⟨source - 5, hi⟩ := by
      simpa [show source - 5 + 5 = source by omega] using heq
    rw [heq']
    simp

omit [Fintype V] [DecidableEq V] in
theorem oriented_true (p : Fin 7 → V) (h : Fin 4 → V) (e : Fin 4 → V)
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (hG : G.IsOriented) :
    oriented (coreBits G.Adj p h e r a z) = true := by
  classical
  let bits := coreBits G.Adj p h e r a z
  have hPDiag : ∀ i : Fin 7, ¬G.Adj (p i) (p i) := fun i => hG.1 _
  have hADiag : ∀ i : Fin 8, ¬G.Adj (a i) (a i) := fun i => hG.1 _
  have hPP : ∀ i j : Fin 7,
      ¬G.Adj (p i) (p j) ∨ ¬G.Adj (p j) (p i) := by
    intro i j
    by_cases hij : G.Adj (p i) (p j)
    · exact Or.inr (fun hji => hG.2 hij hji)
    · exact Or.inl hij
  have hPH : ∀ i : Fin 7, ∀ j : Fin 4,
      ¬G.Adj (p i) (h j) ∨ ¬G.Adj (h j) (p i) := by
    intro i j
    by_cases hij : G.Adj (p i) (h j)
    · exact Or.inr (fun hji => hG.2 hij hji)
    · exact Or.inl hij
  have hAA : ∀ i j : Fin 8,
      ¬G.Adj (a i) (a j) ∨ ¬G.Adj (a j) (a i) := by
    intro i j
    by_cases hij : G.Adj (a i) (a j)
    · exact Or.inr (fun hji => hG.2 hij hji)
    · exact Or.inl hij
  have hPDiagBits : all 7 (fun i => !pp bits i i) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    rw [pp_coreBits G.Adj p h e r a z i i hi hi]
    simp [hPDiag ⟨i, hi⟩]
  have hPPBits : all 7 (fun i => all 7 (fun j =>
      decide (i = j) || !(pp bits i j && pp bits j i))) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    rw [reduced_all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · rw [pp_coreBits G.Adj p h e r a z i j hi hj,
        pp_coreBits G.Adj p h e r a z j i hj hi]
      rcases hPP ⟨i, hi⟩ ⟨j, hj⟩ with h | h <;> simp [hij, h]
  have hPHBits : all 7 (fun i => all 4 (fun j =>
      !(ph bits i j && hp bits j i))) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    rw [reduced_all_eq_true_iff]
    intro j hj
    rw [ph_coreBits G.Adj p h e r a z i j hi hj,
      hp_coreBits G.Adj p h e r a z j i hj hi]
    rcases hPH ⟨i, hi⟩ ⟨j, hj⟩ with h | h <;> simp [h]
  have hADiagBits : all 8 (fun i => !aa bits i i) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    rw [aa_coreBits G.Adj p h e r a z i i hi hi]
    simp [hADiag ⟨i, hi⟩]
  have hAABits : all 8 (fun i => all 8 (fun j =>
      decide (i = j) || !(aa bits i j && aa bits j i))) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    rw [reduced_all_eq_true_iff]
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · rw [aa_coreBits G.Adj p h e r a z i j hi hj,
        aa_coreBits G.Adj p h e r a z j i hj hi]
      rcases hAA ⟨i, hi⟩ ⟨j, hj⟩ with h | h <;> simp [hij, h]
  simp only [oriented, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hPDiagBits, hPPBits⟩, hPHBits⟩, hADiagBits⟩, hAABits⟩

set_option linter.flexible false in
theorem fixedStructure_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B) (hk : C.k = 1)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 → V) (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (a : Fin 8 ≃ {v : V // v ∈ C.A}) (z : Fin 3 → V)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hH3X : (h 3).1 ∈ C.X)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = (r i).1) :
    fixedStructure (coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1)
      e (fun i => (r i).1) (fun i => (a i).1) z) = true := by
  let bits := coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1)
    e (fun i => (r i).1) (fun i => (a i).1) z
  have hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1 := by
    intro i
    rw [hA0]
    exact (Finset.mem_filter.mp (p i).2).2
  have hA01 : aa bits 0 1 = true := by
    rw [aa_coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e
      (fun i => (r i).1) (fun i => (a i).1) z 0 1 (by omega) (by omega)]
    have ha1 : (a 1).1 = (h 0).1 := by simpa using hAH 0
    simpa [hA0, ha1] using (Finset.mem_filter.mp hH0A1).2
  have hA0Tail : all 6 (fun q => !aa bits 0 (q + 2)) = true := by
    rw [reduced_all_eq_true_iff]
    intro q hq
    rw [aa_coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e
      (fun i => (r i).1) (fun i => (a i).1) z 0 (q + 2) (by omega) (by omega)]
    have hNot : ¬G.Adj (a 0).1 (a ⟨q + 2, by omega⟩).1 := by
      rw [hA0]
      intro hadj
      have hm : (a ⟨q + 2, by omega⟩).1 ∈ C.A1 :=
        Finset.mem_filter.mpr ⟨(a ⟨q + 2, by omega⟩).2, hadj⟩
      have hEq : (a ⟨q + 2, by omega⟩).1 = (h 0).1 := by
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hk
        have ht : (a ⟨q + 2, by omega⟩).1 = u := by simpa [hu] using hm
        have h0 : (h 0).1 = u := by simpa [hu] using hH0A1
        exact ht.trans h0.symm
      have hIndex : (⟨q + 2, by omega⟩ : Fin 8) = 1 := by
        apply a.injective
        apply Subtype.ext
        exact hEq.trans (by simpa using (hAH 0).symm)
      have hVal : q + 2 = 1 := Fin.ext_iff.mp hIndex
      omega
    simpa using hNot
  have hA1R : all 3 (fun q => !aa bits 1 (q + 5)) = true := by
    rw [reduced_all_eq_true_iff]
    intro q hq
    rw [aa_coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e
      (fun i => (r i).1) (fun i => (a i).1) z 1 (q + 5) (by omega) (by omega)]
    have hs : (a 1).1 = (h 0).1 := by simpa using hAH 0
    have ht : (a ⟨q + 5, by omega⟩).1 = (r ⟨q, hq⟩).1 := by
      simpa using hAR ⟨q, hq⟩
    simpa [hs, ht] using A1_not_adj_R G C (h 0).1 (r ⟨q, hq⟩).1
      hH0A1 (r ⟨q, hq⟩).2
  have hRows : all 4 (fun i =>
      (1 : BitVec 8).ule (aOut bits (i + 1)) &&
      (8 : BitVec 8).ule (aDegree bits (i + 1)) &&
      (!(aOut bits (i + 1) == 1) || aPOut bits (i + 1) == 7)) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    let u := (h ⟨i, hi⟩).1
    have huH := (h ⟨i, hi⟩).2
    have huA := Digraph.LocalConfiguration.H_subset_A (G := G) C huH
    have hANat := aa_toNat G C.A (fun j => (p j).1) (fun j => (h j).1) e
      (fun j => (r j).1) a z (i + 1) (by omega)
    have hPNat := aP_toNat G C.P p (fun j => (h j).1) e
      (fun j => (r j).1) (fun j => (a j).1) z hA0P hAH hAR
      (i + 1) (by omega)
    have hADegree : (a ⟨i + 1, by omega⟩).1 = u := hAH ⟨i, hi⟩
    rw [hADegree] at hANat hPNat
    change (aOut bits (i + 1)).toNat = directCount G C.A u at hANat
    change (aPOut bits (i + 1)).toNat = directCount G C.P u at hPNat
    have hDegreeEq := H_degree_eq_A_add_P G C hG hPB u huH
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hANat]
      simpa [hk, directCount, internalFirstNeighbors] using (hPivot u huA).1
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      have hALe : directCount G C.A u ≤ 8 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr a).symm)
      have hPLe : directCount G C.P u ≤ 7 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
          simpa using (Fintype.card_congr p).symm)
      change (aOut bits (i + 1) + aPOut bits (i + 1)).toNat ≥ 8
      simp only [BitVec.toNat_add, Nat.reducePow, hANat, hPNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [← hDegreeEq]
      exact hMin u
    · by_cases hTie : directCount G C.A u = 1
      · rw [Bool.or_eq_true]
        apply Or.inr
        apply beq_iff_eq.mpr
        apply BitVec.eq_of_toNat_eq
        rw [hPNat]
        have hLower := (hPivot u huA).2 (by
          simpa [hk, directCount, internalFirstNeighbors] using hTie)
        have hPLe : directCount G C.P u ≤ 7 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
            simpa using (Fintype.card_congr p).symm)
        have hr : C.r = 7 := by
          change C.P.card = 7
          simpa using (Fintype.card_congr p).symm
        rw [← hPB] at hLower
        have hLower' : 7 ≤ directCount G C.P u := by
          change 7 ≤ (C.P.filter (G.Adj u)).card
          simpa [hr] using hLower
        have hEq : directCount G C.P u = 7 := by omega
        simp [hEq]
      · rw [Bool.or_eq_true]
        apply Or.inl
        simp only [Bool.not_eq_true']
        apply Bool.eq_false_iff.mpr
        intro hb
        have heq := congrArg BitVec.toNat (beq_iff_eq.mp hb)
        rw [hANat] at heq
        simp at heq
        exact hTie heq
  have hCoverage : all 3 (fun x => aa bits 1 (x + 2) ||
      any 7 (fun i => ph bits i (x + 1))) = true := by
    rw [reduced_all_eq_true_iff]
    intro x hx
    have hxMem : (h ⟨x + 1, by omega⟩).1 ∈ C.X := by
      rcases (show x = 0 ∨ x = 1 ∨ x = 2 by omega) with rfl | rfl | rfl
      · exact hH1X
      · exact hH2X
      · exact hH3X
    rcases Finset.mem_inter.mp hxMem with ⟨hReach, _⟩
    obtain ⟨u, hu, hut⟩ := (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReach
    rcases Finset.mem_union.mp hu with huA1 | huP
    · rw [Bool.or_eq_true]
      apply Or.inl
      rw [aa_coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e
        (fun i => (r i).1) (fun i => (a i).1) z 1 (x + 2) (by omega) (by omega)]
      have huEq : u = (h 0).1 := by
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hk
        have huV : u = v := by simpa [hv] using huA1
        have h0V : (h 0).1 = v := by simpa [hv] using hH0A1
        exact huV.trans h0V.symm
      have hs : (a 1).1 = (h 0).1 := by simpa using hAH 0
      have ht : (a ⟨x + 2, by omega⟩).1 = (h ⟨x + 1, by omega⟩).1 := by
        simpa using hAH ⟨x + 1, by omega⟩
      simpa [hs, ht, huEq] using hut
    · rw [Bool.or_eq_true]
      apply Or.inr
      rw [reduced_any_eq_true_iff]
      obtain ⟨j, hj⟩ := p.surjective ⟨u, huP⟩
      refine ⟨j, j.isLt, ?_⟩
      rw [ph_coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e
        (fun i => (r i).1) (fun i => (a i).1) z j (x + 1) j.isLt (by omega)]
      simpa [congrArg Subtype.val hj] using hut
  change fixedStructure bits = true
  simp only [fixedStructure, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hA01, hA0Tail⟩, hA1R⟩, hRows⟩, hCoverage⟩

theorem covered_true (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 4 → V)
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V) :
    covered (coreBits G.Adj (fun i => (p i).1) h (fun i => (e i).1) r a z) = true := by
  rw [covered, reduced_all_eq_true_iff]
  intro t ht
  rw [reduced_any_eq_true_iff]
  obtain ⟨u, huP, hut⟩ := EpsilonOneXTwoGraphBridge.external_has_P_predecessor
    G C (e ⟨t, ht⟩).1 (e ⟨t, ht⟩).2
  obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
  refine ⟨i, i.isLt, ?_⟩
  rw [pe_coreBits G.Adj (fun i => (p i).1) h (fun i => (e i).1) r a z
    i t i.isLt ht]
  simpa [congrArg Subtype.val hi] using hut

theorem pDegree_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i : Nat) (hi : i < 7) :
    (EpsilonOneXThreeReducedCore.pDegree
      (coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
        (fun j => (e j).1) r a z) i).toNat = G.outdegree (p ⟨i, hi⟩).1 := by
  let bits := coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) r a z
  let u := (p ⟨i, hi⟩).1
  have hPP := pp_toNat G C.P p (fun j => (h j).1) (fun j => (e j).1)
    r a z i hi
  have hPH := ph_toNat G C.H (fun j => (p j).1) h (fun j => (e j).1)
    r a z i hi
  have hPE := pe_toNat G (externalTargets G C) (fun j => (p j).1)
    (fun j => (h j).1) e r a z i hi
  change (pPOut bits i).toNat = directCount G C.P u at hPP
  change (pHOut bits i).toNat = directCount G C.H u at hPH
  change (pEOut bits i).toNat = directCount G (externalTargets G C) u at hPE
  have hGraph := BSixKTwoCoreGraphBridge.outdegree_P_eq_blocks
    G C hG hPB u (p ⟨i, hi⟩).2
  change G.outdegree u = directCount G (externalTargets G C) u +
    directCount G C.A1 u + directCount G C.X u + directCount G C.P u at hGraph
  have hH : directCount G C.H u =
      directCount G C.A1 u + directCount G C.X u := by
    rw [Digraph.LocalConfiguration.H,
      directCount_union_of_disjoint G C.A1 C.X u
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)]
  have hPPLe : directCount G C.P u ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr p).symm)
  have hPHLe : directCount G C.H u ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr h).symm)
  have hPELe : directCount G (externalTargets G C) u ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr e).symm)
  change (pPOut bits i + pHOut bits i + pEOut bits i).toNat = G.outdegree u
  simp only [BitVec.toNat_add, Nat.reducePow, hPP, hPH, hPE]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

omit [Fintype V] in
theorem secondP_true_mem (P H : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P}) (h : Fin 4 ≃ {v : V // v ∈ H})
    (e : Fin 4 → V) (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i j : Nat) (hi : i < 7) (hj : j < 7)
    (hSecond : (decide (j ≠ i) &&
      !pp (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z) i j &&
      reachedP (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z) i j) = true) :
    (p ⟨j, hj⟩).1 ∈ secondNeighborsThrough G P (P ∪ H) (p ⟨i, hi⟩).1 := by
  classical
  let bits := coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hji, hNotArcBool⟩, hReach⟩
  have hNotArc : ¬G.Adj (p ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 := by
    have hFalse := Bool.eq_false_of_not_eq_true' hNotArcBool
    rw [pp_coreBits G.Adj _ _ _ _ _ _ i j hi hj] at hFalse
    simpa only [decide_eq_false_iff_not] using hFalse
  have hTargetNe : (p ⟨j, hj⟩).1 ≠ (p ⟨i, hi⟩).1 := by
    intro hEq
    have hFin : (⟨j, hj⟩ : Fin 7) = ⟨i, hi⟩ := by
      apply p.injective
      exact Subtype.ext hEq
    exact hji (Fin.ext_iff.mp hFin)
  have hWitness : ∃ w ∈ P ∪ H,
      G.Adj (p ⟨i, hi⟩).1 w ∧ G.Adj w (p ⟨j, hj⟩).1 := by
    simp only [reachedP, Bool.or_eq_true] at hReach
    rcases hReach with hViaP | hViaH
    · rw [reduced_any_eq_true_iff] at hViaP
      obtain ⟨m, hm, hPath⟩ := hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmi, _hmj⟩, hFirst⟩, hLast⟩
      rw [pp_coreBits G.Adj _ _ _ _ _ _ i m hi hm] at hFirst
      rw [pp_coreBits G.Adj _ _ _ _ _ _ m j hm hj] at hLast
      exact ⟨(p ⟨m, hm⟩).1, Finset.mem_union_left H (p ⟨m, hm⟩).2,
        of_decide_eq_true hFirst, of_decide_eq_true hLast⟩
    · rw [reduced_any_eq_true_iff] at hViaH
      obtain ⟨m, hm, hPath⟩ := hViaH
      simp only [Bool.and_eq_true] at hPath
      rw [ph_coreBits G.Adj _ _ _ _ _ _ i m hi hm] at hPath
      rw [hp_coreBits G.Adj _ _ _ _ _ _ m j hm hj] at hPath
      exact ⟨(h ⟨m, hm⟩).1, Finset.mem_union_right P (h ⟨m, hm⟩).2,
        of_decide_eq_true hPath.1, of_decide_eq_true hPath.2⟩
  unfold secondNeighborsThrough
  apply Finset.mem_filter.mpr
  exact ⟨(p ⟨j, hj⟩).2, hNotArc, hTargetNe, hWitness⟩

omit [Fintype V] in
theorem secondP_toNat_le_qCount (P H : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P}) (h : Fin 4 ≃ {v : V // v ∈ H})
    (e : Fin 4 → V) (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (i : Nat) (hi : i < 7) :
    (secondP (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1)
      e r a z) i).toNat ≤ qCount G P H (p ⟨i, hi⟩).1 := by
  classical
  rw [secondP, reduced_toNat_count_eq_fin_sum 7 _ (by omega)]
  unfold qCount secondNeighborsThrough
  rw [filterCard_eq_sum_fin P p]
  let b : Nat → Bool := fun j => decide (j ≠ i) &&
    !pp (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z) i j &&
    reachedP (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z) i j
  let Q : V → Prop := fun v =>
    ¬G.Adj (p ⟨i, hi⟩).1 v ∧ v ≠ (p ⟨i, hi⟩).1 ∧
      ∃ w ∈ P ∪ H, G.Adj (p ⟨i, hi⟩).1 w ∧ G.Adj w v
  change (∑ j : Fin 7, if b j then 1 else 0) ≤
    ∑ j : Fin 7, if Q (p j).1 then 1 else 0
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · have hb' : (decide (j.val ≠ i) &&
        !pp (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z) i j.val &&
        reachedP (coreBits G.Adj (fun k => (p k).1) (fun k => (h k).1) e r a z)
          i j.val) = true := hb
    have hmem := secondP_true_mem G P H p h e r a z i j hi j.isLt hb'
    have hpred := (Finset.mem_filter.mp hmem).2
    have hQ : Q (p j).1 := hpred
    simp [hb, hQ]
  · have hbf := Bool.eq_false_of_not_eq_true hb
    simp [hbf]

theorem rootEquation_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRootDegree : G.outdegree C.s = 8)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (hE0 : (e 0).1 = C.s) (i : Nat) (hi : i < 7) :
    rootEquation (coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) r a z) i = true := by
  let bits := coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) r a z
  let u := (p ⟨i, hi⟩).1
  have hRootBit : pe bits i 0 = decide (G.Adj u C.s) := by
    rw [pe_coreBits G.Adj _ _ _ _ _ _ i 0 hi (by omega)]
    rw [show (e ⟨0, by omega⟩).1 = (e 0).1 by rfl, hE0]
  by_cases hps : G.Adj u C.s
  · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
      G C hG hPB hNoSeymour hRootDegree u (p ⟨i, hi⟩).2 hps
    have hSecond := secondP_toNat_le_qCount G C.P C.H p h
      (fun j => (e j).1) r a z i hi
    have hPP := pp_toNat G C.P p (fun j => (h j).1) (fun j => (e j).1)
      r a z i hi
    have hPH := ph_toNat G C.H (fun j => (p j).1) h (fun j => (e j).1)
      r a z i hi
    have hPE := pe_toNat G (externalTargets G C) (fun j => (p j).1)
      (fun j => (h j).1) e r a z i hi
    change (secondP bits i).toNat ≤ qCount G C.P C.H u at hSecond
    change (pPOut bits i).toNat = directCount G C.P u at hPP
    change (pHOut bits i).toNat = directCount G C.H u at hPH
    change (pEOut bits i).toNat = directCount G (externalTargets G C) u at hPE
    have hExternal := BSixKTwoCoreGraphBridge.directCount_externalTargets
      G C u (p ⟨i, hi⟩).2
    have hEpsilon : epsilonAt G u C.s = 1 := by simp [epsilonAt, hps]
    have hQLe : qCount G C.P C.H u ≤ 7 := by
      unfold qCount secondNeighborsThrough
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr p).symm)
    have hPPLe : directCount G C.P u ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr p).symm)
    have hPHLe : directCount G C.H u ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr h).symm)
    have hPELe : directCount G (externalTargets G C) u ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
        simpa using (Fintype.card_congr e).symm)
    have hLeft : (secondP bits i + 9).toNat = (secondP bits i).toNat + 9 := by
      simp only [BitVec.toNat_add, Nat.reducePow]
      rw [show (9 : BitVec 8).toNat = 9 by decide, Nat.mod_eq_of_lt (by omega)]
    have hMul : (2 * pHOut bits i).toNat = 2 * (pHOut bits i).toNat := by
      simp only [BitVec.toNat_mul, Nat.reducePow]
      rw [show (2 : BitVec 8).toNat = 2 by decide, Nat.mod_eq_of_lt (by omega)]
    have hRight : (pEOut bits i + 2 * pHOut bits i + pPOut bits i).toNat =
        (pEOut bits i).toNat + 2 * (pHOut bits i).toNat +
          (pPOut bits i).toNat := by
      simp only [BitVec.toNat_add, Nat.reducePow, hMul]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    change rootEquation bits i = true
    simp only [rootEquation, hRootBit, hps, decide_true, Bool.not_true,
      Bool.false_or, BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hLeft, hRight, hPE, hPH, hPP, hExternal]
    rw [hEpsilon] at hEquation
    omega
  · change rootEquation bits i = true
    simp [rootEquation, hRootBit, hps]

theorem secondFromA_true_mem (C : G.LocalConfiguration)
    (hG : G.IsOriented)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 4 → V)
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 3 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = h i)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i).1 (r j))
    (hAE : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i).1 (e j).1)
    (source target : Nat) (hs : source < 15) (ht : target < 19)
    (hSecond : secondFromA
      (coreBits G.Adj (fun i => (p i).1) h (fun i => (e i).1) r
        (fun i => (a i).1) z) source target = true) :
    labelledVertex (fun i => (a i).1) (fun i => (p i).1) (fun i => (e i).1)
      target ∈ G.secondOutNeighborFinset
        (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
          (fun i => (e i).1) source) := by
  let bits := coreBits G.Adj (fun i => (p i).1) h (fun i => (e i).1) r
    (fun i => (a i).1) z
  simp only [secondFromA, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hNotArcBool⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (reduced_any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩, hSecondBool⟩
  have hFirst : G.Adj
      (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
        (fun i => (e i).1) source)
      (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
        (fun i => (e i).1) middle) := by
    rw [arc_coreBits G (fun i => (p i).1) h (fun i => (e i).1) r
      (fun i => (a i).1) z hA0P hP0 hAH hAR hPR hAE source middle
      (by omega) (by omega)] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj
      (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
        (fun i => (e i).1) middle)
      (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
        (fun i => (e i).1) target) := by
    rw [arc_coreBits G (fun i => (p i).1) h (fun i => (e i).1) r
      (fun i => (a i).1) z hA0P hP0 hAH hAR hPR hAE middle target hm ht]
      at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj
      (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
        (fun i => (e i).1) source)
      (labelledVertex (fun i => (a i).1) (fun i => (p i).1)
        (fun i => (e i).1) target) := by
    rw [arc_coreBits G (fun i => (p i).1) h (fun i => (e i).1) r
      (fun i => (a i).1) z hA0P hP0 hAH hAR hPR hAE source target
      (by omega) ht] at hNotArcBool
    simpa using hNotArcBool
  have hVertexNe :
      labelledVertex (fun i => (a i).1) (fun i => (p i).1) (fun i => (e i).1)
        target ≠
      labelledVertex (fun i => (a i).1) (fun i => (p i).1) (fun i => (e i).1)
        source := by
    intro heq
    let lab := retainedLabelEquiv G C hG a p e
    have hFin : (⟨target, ht⟩ : Fin 19) = ⟨source, by omega⟩ := by
      apply lab.injective
      apply Subtype.ext
      simpa [lab, retainedLabelEquiv_val] using heq
    exact hTargetNe (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, hFirst, hSecond'⟩, hNotArc, hVertexNe⟩

theorem hNonSeymour_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 3 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1)
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i).1 (r j))
    (hAE : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i).1 (e j).1) :
    hNonSeymour (coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1)
      (fun i => (e i).1) r (fun i => (a i).1) z) = true := by
  let bits := coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1)
    (fun i => (e i).1) r (fun i => (a i).1) z
  rw [hNonSeymour, reduced_all_eq_true_iff]
  intro source hs
  let u := (h ⟨source, hs⟩).1
  have hRep : (aSecond bits (source + 1)).toNat ≤ G.secondOutdegree u := by
    let lab := retainedLabelEquiv G C hG a p e
    rw [aSecond, reduced_toNat_count_eq_fin_sum 19 _ (by omega)]
    have hFiltered : (∑ j : Fin 19, if secondFromA bits (source + 1) j then 1 else 0) ≤
        ((retainedVertexSet G C).filter
          (fun v => v ∈ G.secondOutNeighborFinset u)).card := by
      rw [filterCard_eq_sum_fin (retainedVertexSet G C) lab]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hb : secondFromA bits (source + 1) j = true
      · have hmem := secondFromA_true_mem G C hG p (fun i => (h i).1) e r a z
          hA0P hP0 hAH hAR hPR hAE (source + 1) j (by omega) j.isLt hb
        have hu : labelledVertex (fun i => (a i).1) (fun i => (p i).1)
            (fun i => (e i).1) (source + 1) = u := by
          have hLabel : labelledVertex (fun i => (a i).1) (fun i => (p i).1)
              (fun i => (e i).1) (source + 1) =
              (a ⟨source + 1, by omega⟩).1 := by
            simp [labelledVertex, show source + 1 < 8 by omega]
          rw [hLabel, hAH ⟨source, hs⟩]
        rw [retainedLabelEquiv_val]
        have hGood : labelledVertex (fun i => (a i).1) (fun i => (p i).1)
            (fun i => (e i).1) j ∈ G.secondOutNeighborFinset u := by
          rw [← hu]
          exact hmem
        rw [if_pos hb, if_pos hGood]
      · have hbf := Bool.eq_false_of_not_eq_true hb
        simp [hbf]
    unfold Digraph.secondOutdegree
    exact hFiltered.trans (Finset.card_le_card (by
      intro v hv
      exact (Finset.mem_filter.mp hv).2))
  have hStrict : G.secondOutdegree u < G.outdegree u :=
    Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun hS => hNoSeymour ⟨u, hS⟩)
  have hANat := aa_toNat G C.A (fun i => (p i).1) (fun i => (h i).1)
    (fun i => (e i).1) r a z (source + 1) (by omega)
  have hPNat := aP_toNat G C.P p (fun i => (h i).1) (fun i => (e i).1)
    r (fun i => (a i).1) z hA0P hAH hAR (source + 1) (by omega)
  have hSource : (a ⟨source + 1, by omega⟩).1 = u := hAH ⟨source, hs⟩
  rw [hSource] at hANat hPNat
  change (aOut bits (source + 1)).toNat = directCount G C.A u at hANat
  change (aPOut bits (source + 1)).toNat = directCount G C.P u at hPNat
  have hDegree := A_outdegree_eq_A_add_P G C hG hPB u
    (Digraph.LocalConfiguration.H_subset_A (G := G) C (h ⟨source, hs⟩).2)
  have hALe : directCount G C.A u ≤ 8 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr a).symm)
  have hPLe : directCount G C.P u ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr p).symm)
  have hDegreeNat : (aDegree bits (source + 1)).toNat = G.outdegree u := by
    change (aOut bits (source + 1) + aPOut bits (source + 1)).toNat = _
    simp only [BitVec.toNat_add, Nat.reducePow, hANat, hPNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hDegree.symm
  have hLeft : (aSecond bits (source + 1) + 1).toNat =
      (aSecond bits (source + 1)).toNat + 1 := by
    have hSecondLe : (aSecond bits (source + 1)).toNat ≤ 19 := by
      rw [aSecond, reduced_toNat_count_eq_fin_sum 19 _ (by omega)]
      calc
        _ ≤ ∑ _j : Fin 19, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          split <;> omega
        _ = 19 := by simp
    simp only [BitVec.toNat_add, Nat.reducePow]
    rw [show (1 : BitVec 8).toNat = 1 by decide, Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hLeft, hDegreeNat]
  omega

theorem totalPE_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 4 → V)
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V) :
    (sumCount 7 (pEOut (coreBits G.Adj (fun i => (p i).1) h
      (fun i => (e i).1) r a z))).toNat =
      edgeCount G C.P (externalTargets G C) := by
  let bits := coreBits G.Adj (fun i => (p i).1) h (fun i => (e i).1) r a z
  have hSum : (∑ i ∈ Finset.range 7, (pEOut bits i).toNat) =
      edgeCount G C.P (externalTargets G C) := by
    rw [← Fin.sum_univ_eq_sum_range,
      edgeCount_eq_sum_fin G C.P (externalTargets G C) p]
    apply Finset.sum_congr rfl
    intro i hi
    exact pe_toNat G (externalTargets G C) (fun j => (p j).1) h e r a z
      i i.isLt
  have hCap := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  have hpCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have heCard : (externalTargets G C).card = 4 := by
    simpa using (Fintype.card_congr e).symm
  have hlt : ∑ i ∈ Finset.range 7, (pEOut bits i).toNat < 256 := by
    rw [hSum]
    rw [hpCard, heCard] at hCap
    omega
  rw [reduced_toNat_sumCount 7 _ hlt, hSum]

theorem totalPH_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 → V) (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V) :
    (sumCount 7 (pHOut (coreBits G.Adj (fun i => (p i).1)
      (fun i => (h i).1) e r a z))).toNat = edgeCount G C.P C.H := by
  let bits := coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e r a z
  have hSum : (∑ i ∈ Finset.range 7, (pHOut bits i).toNat) =
      edgeCount G C.P C.H := by
    rw [← Fin.sum_univ_eq_sum_range, edgeCount_eq_sum_fin G C.P C.H p]
    apply Finset.sum_congr rfl
    intro i hi
    exact ph_toNat G C.H (fun j => (p j).1) h e r a z i i.isLt
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hpCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hhCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hlt : ∑ i ∈ Finset.range 7, (pHOut bits i).toNat < 256 := by
    rw [hSum]
    rw [hpCard, hhCard] at hCap
    omega
  rw [reduced_toNat_sumCount 7 _ hlt, hSum]

theorem totalHP_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 → V) (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V) :
    (sumCount 4 (fun q => count 7 (hp
      (coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e r a z) q))).toNat =
      edgeCount G C.H C.P := by
  let bits := coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1) e r a z
  have hSum : (∑ i ∈ Finset.range 4, (count 7 (hp bits i)).toNat) =
      edgeCount G C.H C.P := by
    rw [← Fin.sum_univ_eq_sum_range, edgeCount_eq_sum_fin G C.H C.P h]
    apply Finset.sum_congr rfl
    intro i hi
    exact hp_toNat G C.P p (fun j => (h j).1) e r a z i i.isLt
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hpCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hhCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hlt : ∑ i ∈ Finset.range 4, (count 7 (hp bits i)).toNat < 256 := by
    rw [hSum]
    rw [hpCard, hhCard] at hCap
    omega
  rw [reduced_toNat_sumCount 4 _ hlt, hSum]

theorem orderedP_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (hOrder : ∀ i j : Fin 7, i ≤ j → G.outdegree (p j).1 ≤ G.outdegree (p i).1) :
    orderedP (coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1)
      (fun i => (e i).1) r a z) = true := by
  rw [orderedP, reduced_all_eq_true_iff]
  intro i hi
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pDegree_toNat G C hG hPB p h e r a z (i + 1) (by omega),
    pDegree_toNat G C hG hPB p h e r a z i (by omega)]
  apply hOrder
  exact Fin.mk_le_mk.mpr (by omega)

theorem aggregateOrderedP_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 → V) (a : Fin 8 → V) (z : Fin 3 → V)
    (hE0 : (e 0).1 = C.s)
    (hDegreeOrder : ∀ i j : Fin 7, i ≤ j →
      G.outdegree (p j).1 ≤ G.outdegree (p i).1)
    (hRootOrder : ∀ i j : Fin 7, i ≤ j →
      G.outdegree (p i).1 = G.outdegree (p j).1 →
      epsilonAt G (p j).1 C.s ≤ epsilonAt G (p i).1 C.s)
    (hHOrder : ∀ i j : Fin 7, i ≤ j →
      G.outdegree (p i).1 = G.outdegree (p j).1 →
      epsilonAt G (p i).1 C.s = epsilonAt G (p j).1 C.s →
      directCount G C.H (p j).1 ≤ directCount G C.H (p i).1) :
    aggregateOrderedP (coreBits G.Adj (fun i => (p i).1)
      (fun i => (h i).1) (fun i => (e i).1) r a z) = true := by
  let bits := coreBits G.Adj (fun i => (p i).1) (fun i => (h i).1)
    (fun i => (e i).1) r a z
  rw [aggregateOrderedP, reduced_all_eq_true_iff]
  intro i hi
  let pi : Fin 7 := ⟨i, by omega⟩
  let pj : Fin 7 := ⟨i + 1, by omega⟩
  have hij : pi ≤ pj := Fin.mk_le_mk.mpr (by omega)
  have hdi := pDegree_toNat G C hG hPB p h e r a z i (by omega)
  have hdj := pDegree_toNat G C hG hPB p h e r a z (i + 1) (by omega)
  have hPeI : pe (coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) r a z) i 0 = decide (G.Adj (p pi).1 C.s) := by
    rw [pe_coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) r a z i 0 (by omega) (by omega)]
    simp [pi, hE0]
  have hPeJ : pe (coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) r a z) (i + 1) 0 =
      decide (G.Adj (p pj).1 C.s) := by
    rw [pe_coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
      (fun j => (e j).1) r a z (i + 1) 0 (by omega) (by omega)]
    simp [pj, hE0]
  have hDegreeLe := hDegreeOrder pi pj hij
  simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
  refine ⟨by simpa [pi, pj, hdi, hdj] using hDegreeLe, ?_⟩
  by_cases hDegree : G.outdegree (p pi).1 = G.outdegree (p pj).1
  · rw [Bool.or_eq_true]
    apply Or.inr
    have hRootLe := hRootOrder pi pj hij hDegree
    by_cases hri : G.Adj (p pi).1 C.s <;>
      by_cases hrj : G.Adj (p pj).1 C.s
    · have hHEq : epsilonAt G (p pi).1 C.s = epsilonAt G (p pj).1 C.s := by
        simp [epsilonAt, hri, hrj]
      have hHLe := hHOrder pi pj hij hDegree hHEq
      have hPHI := ph_toNat G C.H (fun j => (p j).1) h
        (fun j => (e j).1) r a z i (by omega)
      have hPHJ := ph_toNat G C.H (fun j => (p j).1) h
        (fun j => (e j).1) r a z (i + 1) (by omega)
      simp [hPeI, hPeJ, pi, pj, hri, hrj,
        hPHI, hPHJ, hHLe]
    · simp [hPeI, hPeJ, hri, hrj]
    · have : ¬epsilonAt G (p pj).1 C.s ≤ epsilonAt G (p pi).1 C.s := by
        simp [epsilonAt, hri, hrj]
      exact (this hRootLe).elim
    · have hHEq : epsilonAt G (p pi).1 C.s = epsilonAt G (p pj).1 C.s := by
        simp [epsilonAt, hri, hrj]
      have hHLe := hHOrder pi pj hij hDegree hHEq
      have hPHI := ph_toNat G C.H (fun j => (p j).1) h
        (fun j => (e j).1) r a z i (by omega)
      have hPHJ := ph_toNat G C.H (fun j => (p j).1) h
        (fun j => (e j).1) r a z (i + 1) (by omega)
      simp [hPeI, hPeJ, pi, pj, hri, hrj,
        hPHI, hPHJ, hHLe]
  · rw [Bool.or_eq_true]
    apply Or.inl
    rw [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro hEq
    apply hDegree
    have hEq' := congrArg BitVec.toNat (beq_iff_eq.mp hEq)
    rw [hdi, hdj] at hEq'
    exact hEq'

theorem protectedLabel_target (C : G.LocalConfiguration)
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (hA0 : (a 0).1 = C.a1)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = (r i).1)
    (k : Fin 4) :
    (protectedLabelEquiv G C a r hA0 hCard k).1 =
      (a ⟨protectedA k, by fin_cases k <;> simp [protectedA]⟩).1 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 by omega)
      with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases hk with rfl | rfl | rfl | rfl
  · simp [protectedA]
  · rw [protectedLabelEquiv_one G C a r hA0 hCard]
    simpa [protectedA] using (hAR 0).symm
  · rw [protectedLabelEquiv_two G C a r hA0 hCard]
    simpa [protectedA] using (hAR 1).symm
  · rw [protectedLabelEquiv_three G C a r hA0 hCard]
    simpa [protectedA] using (hAR 2).symm

theorem alternateProtected_of_deletion_reached (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = (r i).1)
    (hE0 : (e 0).1 = C.s)
    (hCard : (BSevenKOne.protectedFinset G C).card = 4)
    (i : Nat) (hi : i < 7) (k : Fin 4)
    (hReached : (protectedLabelEquiv G C a r hA0 hCard k).1 ∈
      G.outNeighborFinsetOf (G.outNeighborFinset (p ⟨i, hi⟩).1 |>.erase C.s) \
        ((G.outNeighborFinset (p ⟨i, hi⟩).1 |>.erase C.s) ∪
          {(p ⟨i, hi⟩).1})) :
    alternateProtected
      (coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
        (fun j => (e j).1) (fun j => (r j).1) (fun j => (a j).1)
        (fun j => (e ⟨j + 1, by omega⟩).1)) i k = true := by
  let bits := coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (r j).1) (fun j => (a j).1)
    (fun j => (e ⟨j + 1, by omega⟩).1)
  let w := (protectedLabelEquiv G C a r hA0 hCard k).1
  rcases Finset.mem_sdiff.mp hReached with ⟨hReach, _hOutside⟩
  obtain ⟨middle, hmErase, hmw⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReach
  have hmOut : middle ∈ G.outNeighborFinset (p ⟨i, hi⟩).1 :=
    Finset.mem_of_mem_erase hmErase
  have hmNeS : middle ≠ C.s := (Finset.mem_erase.mp hmErase).1
  have hpm : G.Adj (p ⟨i, hi⟩).1 middle :=
    (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
  have hTarget := protectedLabel_target G C a r hA0 hCard hAR k
  have hH0Not : ¬G.Adj (h 0).1 w := by
    fin_cases k
    · have hForward : G.Adj (a 0).1 (h 0).1 := by
        rw [hA0]
        exact (Finset.mem_filter.mp hH0A1).2
      simpa [w] using hG.2 hForward
    · change ¬G.Adj (h 0).1
          (protectedLabelEquiv G C a r hA0 hCard (1 : Fin 4)).1
      rw [protectedLabelEquiv_one G C a r hA0 hCard]
      exact A1_not_adj_R G C (h 0).1 (r 0).1 hH0A1 (r 0).2
    · change ¬G.Adj (h 0).1
          (protectedLabelEquiv G C a r hA0 hCard (2 : Fin 4)).1
      rw [protectedLabelEquiv_two G C a r hA0 hCard]
      exact A1_not_adj_R G C (h 0).1 (r 1).1 hH0A1 (r 1).2
    · change ¬G.Adj (h 0).1
          (protectedLabelEquiv G C a r hA0 hCard (3 : Fin 4)).1
      rw [protectedLabelEquiv_three G C a r hA0 hCard]
      exact A1_not_adj_R G C (h 0).1 (r 2).1 hH0A1 (r 2).2
  have hPNot : ∀ q : Fin 7, ¬G.Adj (p q).1 w := by
    intro q
    fin_cases k
    · have hForward : G.Adj (a 0).1 (p q).1 := by
        rw [hA0]
        exact (Finset.mem_filter.mp (p q).2).2
      simpa [w] using hG.2 hForward
    · change ¬G.Adj (p q).1
          (protectedLabelEquiv G C a r hA0 hCard (1 : Fin 4)).1
      rw [protectedLabelEquiv_one G C a r hA0 hCard]
      exact P_not_adj_R G C (p q).1 (r 0).1 (p q).2 (r 0).2
    · change ¬G.Adj (p q).1
          (protectedLabelEquiv G C a r hA0 hCard (2 : Fin 4)).1
      rw [protectedLabelEquiv_two G C a r hA0 hCard]
      exact P_not_adj_R G C (p q).1 (r 1).1 (p q).2 (r 1).2
    · change ¬G.Adj (p q).1
          (protectedLabelEquiv G C a r hA0 hCard (3 : Fin 4)).1
      rw [protectedLabelEquiv_three G C a r hA0 hCard]
      exact P_not_adj_R G C (p q).1 (r 2).1 (p q).2 (r 2).2
  have hCaptured := outgoingCaptured_of_p_eq_B G C hG hPB
    (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2 hmOut
  simp only [Finset.mem_union, Finset.mem_singleton] at hCaptured
  rcases hCaptured with ((hmZ | hmS) | hmH) | hmP
  · rw [alternateProtected, Bool.or_eq_true]
    apply Or.inr
    rw [reduced_any_eq_true_iff]
    have hmE : middle ∈ externalTargets G C := Finset.mem_union_left _ hmZ
    obtain ⟨t, ht⟩ := e.surjective ⟨middle, hmE⟩
    have htVal : (e t).1 = middle := congrArg Subtype.val ht
    have ht0 : t.val ≠ 0 := by
      intro hzero
      have teq : t = 0 := Fin.ext hzero
      have : middle = C.s := by simpa [teq, hE0] using htVal.symm
      exact hmNeS this
    refine ⟨t.val - 1, by omega, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · rw [pe_coreBits G.Adj _ _ _ _ _ _ i (t.val - 1 + 1) hi (by omega)]
      have heq : (e ⟨t.val - 1 + 1, by omega⟩).1 = middle := by
        simpa [show t.val - 1 + 1 = t.val by omega] using htVal
      simpa [heq] using hpm
    · rw [zp_coreBits G.Adj _ _ _ _ _ _ (t.val - 1) k
        (by omega) k.isLt]
      have hSource : (e ⟨t.val - 1 + 1, by omega⟩).1 = middle := by
        simpa [show t.val - 1 + 1 = t.val by omega] using htVal
      have hTarget' :
          (if k.val = 0 then (a 0).1 else (a ⟨k.val + 4, by omega⟩).1) = w := by
        change (if k.val = 0 then (a 0).1 else
          (a ⟨k.val + 4, by omega⟩).1) =
            (protectedLabelEquiv G C a r hA0 hCard k).1
        rw [hTarget]
        fin_cases k <;> rfl
      apply decide_eq_true
      rw [hSource, hTarget']
      exact hmw
  · exact (hmNeS hmS).elim
  · obtain ⟨t, ht⟩ := h.surjective ⟨middle, hmH⟩
    have htVal : (h t).1 = middle := congrArg Subtype.val ht
    by_cases ht0 : t.val = 0
    · have teq : t = 0 := Fin.ext ht0
      have hm0 : G.Adj (h 0).1 w := by
        rw [teq] at htVal
        rw [htVal]
        exact hmw
      exact (hH0Not hm0).elim
    · rw [alternateProtected, Bool.or_eq_true]
      apply Or.inl
      rw [reduced_any_eq_true_iff]
      refine ⟨t.val - 1, by omega, ?_⟩
      simp only [Bool.and_eq_true]
      constructor
      · rw [ph_coreBits G.Adj _ _ _ _ _ _ i (t.val - 1 + 1) hi (by omega)]
        have heq : (h ⟨t.val - 1 + 1, by omega⟩).1 = middle := by
          simpa [show t.val - 1 + 1 = t.val by omega] using htVal
        simpa [heq] using hpm
      · rw [aa_coreBits G.Adj _ _ _ _ _ _ (t.val - 1 + 2) (protectedA k)
          (by omega) (by fin_cases k <;> simp [protectedA])]
        have hSource : (a ⟨t.val - 1 + 2, by omega⟩).1 = middle := by
          have ha := hAH ⟨t.val, t.isLt⟩
          simpa [show t.val - 1 + 2 = t.val + 1 by omega, htVal] using ha
        simpa [hSource, hTarget] using hmw
  · obtain ⟨q, hq⟩ := p.surjective ⟨middle, hmP⟩
    have hqVal : (p q).1 = middle := congrArg Subtype.val hq
    exact (hPNot q (by simpa [w, hqVal] using hmw)).elim

theorem protectedRedundancy_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 3)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (e : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = (r i).1)
    (hE0 : (e 0).1 = C.s) (i : Nat) (hi : i < 7) :
    protectedRedundancy
      (coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
        (fun j => (e j).1) (fun j => (r j).1) (fun j => (a j).1)
        (fun j => (e ⟨j + 1, by omega⟩).1)) i = true := by
  let bits := coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (r j).1) (fun j => (a j).1)
    (fun j => (e ⟨j + 1, by omega⟩).1)
  let ante : Bool := pDegree bits i == 8 && pe bits i 0
  by_cases hAnte : ante = true
  · have hAnte' : pDegree bits i = 8 ∧ pe bits i 0 = true := by
      simpa [ante, Bool.and_eq_true, beq_iff_eq] using hAnte
    have hDegree : G.outdegree (p ⟨i, hi⟩).1 = 8 := by
      have hd := pDegree_toNat G C hG hPB p h e (fun j => (r j).1)
        (fun j => (a j).1) (fun j => (e ⟨j + 1, by omega⟩).1) i hi
      rw [hAnte'.1] at hd
      simpa using hd.symm
    have hps : G.Adj (p ⟨i, hi⟩).1 C.s := by
      rw [pe_coreBits G.Adj _ _ _ _ _ _ i 0 hi (by omega)] at hAnte'
      simpa [hE0] using of_decide_eq_true hAnte'.2
    have hCard := protectedFinset_card_eq_four G C hG hRootDegree hk hx
    let E := G.outNeighborFinsetOf
      (G.outNeighborFinset (p ⟨i, hi⟩).1 |>.erase C.s) \
        ((G.outNeighborFinset (p ⟨i, hi⟩).1 |>.erase C.s) ∪
          {(p ⟨i, hi⟩).1})
    have hReach := Digraph.oneArcDeletion_reaches_all_but_one G
      (BSevenKOne.protectedFinset G C) hBound hG hNoSeymour hDegree hps
      (BSevenKOne.protectedFinset_subset_second G C hG
        (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2 hps)
    have hThree : 3 ≤ (BSevenKOne.protectedFinset G C ∩ E).card := by
      change (BSevenKOne.protectedFinset G C).card ≤
        (BSevenKOne.protectedFinset G C ∩ E).card + 1 at hReach
      omega
    let lab := protectedLabelEquiv G C a r hA0 hCard
    have hCompare : (BSevenKOne.protectedFinset G C ∩ E).card ≤
        ∑ k : Fin 4, if alternateProtected bits i k then 1 else 0 := by
      have hInter : BSevenKOne.protectedFinset G C ∩ E =
          (BSevenKOne.protectedFinset G C).filter (fun v => v ∈ E) := by
        ext v
        simp
      rw [hInter, filterCard_eq_sum_fin (BSevenKOne.protectedFinset G C) lab]
      apply Finset.sum_le_sum
      intro k hkMem
      by_cases hr : (lab k).1 ∈ E
      · have ha := alternateProtected_of_deletion_reached G C hG hPB p h e r a
          hA0 hAH hH0A1 hAR hE0 hCard i hi k hr
        change alternateProtected bits i k = true at ha
        rw [if_pos hr, if_pos ha]
      · rw [if_neg hr]
        omega
    have hCount : (count 4 (alternateProtected bits i)).toNat =
        ∑ k : Fin 4, if alternateProtected bits i k then 1 else 0 :=
      reduced_toNat_count_eq_fin_sum 4 _ (by omega)
    have hSumLower : 3 ≤
        ∑ k : Fin 4, if alternateProtected bits i k then 1 else 0 :=
      hThree.trans hCompare
    have hAnteBool : (pDegree bits i == 8 && pe bits i 0) = true := by
      simpa [ante] using hAnte
    change protectedRedundancy bits i = true
    rw [protectedRedundancy, hAnteBool]
    simp only [Bool.not_true, Bool.false_or, BitVec.ule_eq_decide,
      decide_eq_true_eq]
    rw [hCount]
    exact hSumLower
  · change protectedRedundancy bits i = true
    have hFalse : (pDegree bits i == 8 && pe bits i 0) = false := by
      apply Bool.eq_false_of_not_eq_true
      simpa [ante] using hAnte
    change (!(pDegree bits i == 8 && pe bits i 0) ||
      (3 : BitVec 8).ule (count 4 (alternateProtected bits i))) = true
    rw [hFalse]
    simp

theorem degreeEight_of_sorted_tail (C : G.LocalConfiguration)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (hOrder : ∀ i j : Fin 7, i ≤ j → G.outdegree (p j).1 ≤ G.outdegree (p i).1)
    (m idx : Nat) (hidx : idx < 7)
    (hExact : m ≤ (C.P.filter fun v => G.outdegree v = 8).card)
    (hThreshold : 7 - idx ≤ m) :
    G.outdegree (p ⟨idx, hidx⟩).1 = 8 := by
  by_contra hne
  have hgt : 8 < G.outdegree (p ⟨idx, hidx⟩).1 := by
    have := hMin (p ⟨idx, hidx⟩).1
    omega
  have hEarlier : ∀ j : Fin 7, j.val ≤ idx → G.outdegree (p j).1 ≠ 8 := by
    intro j hj heq
    have ho := hOrder j ⟨idx, hidx⟩ (Fin.mk_le_mk.mpr hj)
    omega
  have hCard : (C.P.filter fun v => G.outdegree v = 8).card ≤ 6 - idx := by
    rw [filterCard_eq_sum_fin C.P p]
    calc
      (∑ j : Fin 7, if G.outdegree (p j).1 = 8 then 1 else 0) ≤
          ∑ j : Fin 7, if idx < j.val then 1 else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases heq : G.outdegree (p j).1 = 8
        · have hlt : idx < j.val := by
            by_contra hn
            exact hEarlier j (by omega) heq
          simp [heq, hlt]
        · simp [heq]
      _ = 6 - idx := by
        interval_cases idx <;> decide
  omega

theorem exactDegree_card_lower (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPB : C.P = C.B) (hPCard : C.P.card = 7) (hHCard : C.H.card = 4)
    (m : Nat) (hExternal : edgeCount G C.P (externalTargets G C) + m = 28)
    (hHP : 14 ≤ edgeCount G C.H C.P) :
    m ≤ (C.P.filter fun v => G.outdegree v = 8).card := by
  have hPHCross := cross_edgeCount_add_reverse_le G C.H C.P hG
  rw [hPCard, hHCard] at hPHCross
  have hPH : edgeCount G C.P C.H ≤ 14 := by omega
  have hPP := internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternalSplit := edgeCount_externalTargets G C
  have hDegreeLower : 56 ≤ ∑ v ∈ C.P, G.outdegree v := by
    calc
      56 = ∑ _v ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ v ∈ C.P, G.outdegree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hMin v
  have hDegreeUpper : (∑ v ∈ C.P, G.outdegree v) + m ≤ 63 := by omega
  have hmLe : m ≤ 7 := by omega
  have hBad : (C.P.filter fun v => G.outdegree v ≠ 8).card ≤ 7 - m := by
    have hBadExcess : (C.P.filter fun v => G.outdegree v ≠ 8).card ≤
        ∑ v ∈ C.P, (G.outdegree v - 8) := by
      calc
        _ = ∑ _v ∈ C.P.filter (fun v => G.outdegree v ≠ 8), 1 := by simp
        _ ≤ ∑ v ∈ C.P.filter (fun v => G.outdegree v ≠ 8),
            (G.outdegree v - 8) := by
          apply Finset.sum_le_sum
          intro v hv
          have hvNe := (Finset.mem_filter.mp hv).2
          have hvMin := hMin v
          omega
        _ ≤ ∑ v ∈ C.P, (G.outdegree v - 8) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hSplit : ∑ v ∈ C.P, G.outdegree v =
        56 + ∑ v ∈ C.P, (G.outdegree v - 8) := by
      calc
        _ = ∑ v ∈ C.P, (8 + (G.outdegree v - 8)) := by
          apply Finset.sum_congr rfl
          intro v hv
          have := hMin v
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hPCard]
    omega
  have hPartition : (C.P.filter fun v => G.outdegree v = 8).card +
      (C.P.filter fun v => G.outdegree v ≠ 8).card = 7 := by
    simpa [hPCard] using Finset.card_filter_add_card_filter_not
      (s := C.P) (fun v => G.outdegree v = 8)
  omega

theorem tightEpsilonOneXThreeImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1) (hx : C.x = 3) (hz : C.z = 3) : False := by
  classical
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hHCard : C.H.card = 4 := by
    change C.h = 4
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hECard : (externalTargets G C).card = 4 := by
    rw [card_externalTargets G C, hz, hEpsilon]
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 1 := hk
  have hXCard : C.X.card = 3 := hx
  have hRCard : C.R.card = 3 := by
    have hXR := x_add_card_R_eq_six G C hG hRootDegree hk
    omega
  have hReach : ∃ u ∈ C.P, G.Adj u C.s := by
    rw [epsilonS_eq_ite] at hEpsilon
    by_cases hr : ∃ u ∈ C.P, G.Adj u C.s
    · exact hr
    · simp [hr] at hEpsilon
  have hsE : C.s ∈ externalTargets G C := by
    apply Finset.mem_union_right C.Z
    simp [rootSecondFinset, hReach]
  let eP : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let p := EpsilonOneRootCoreGraphBridge.rootSortedFinsetEquiv G.outdegree
    (fun v => epsilonAt G v C.s) (directCount G C.H) C.P eP
  let eA1 : Fin 1 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eX : Fin 3 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let h := FourZHighDefectGraphBridge.hLabelEquiv G C hHCard eA1 eX
  let r : Fin 3 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a := FourZHighDefectGraphBridge.aLabelEquiv G C hACard h r
  let e : Fin 4 ≃ {v : V // v ∈ externalTargets G C} :=
    FiveZExactLabels.finsetEquivFinAtZero (externalTargets G C) (by omega)
      hECard C.s hsE
  have hE0 : (e 0).1 = C.s :=
    FiveZExactLabels.finsetEquivFinAtZero_zero (externalTargets G C)
      (by omega) hECard C.s hsE
  have hA0 : (a 0).1 = C.a1 :=
    FourZHighDefectGraphBridge.aLabelEquiv_zero G C hACard h r
  have hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1 := by
    intro j
    exact FourZHighDefectGraphBridge.aLabelEquiv_h G C hACard h r j
  have hAR : ∀ j : Fin 3, (a ⟨j + 5, by omega⟩).1 = (r j).1 := by
    intro j
    exact FourZHighDefectGraphBridge.aLabelEquiv_r G C hACard h r j
  have hH0 : (h 0).1 ∈ C.A1 := by
    rw [FourZHighDefectGraphBridge.hLabelEquiv_zero G C hHCard eA1 eX]
    exact (eA1 0).2
  have hH1 : (h 1).1 ∈ C.X := by
    rw [FourZHighDefectGraphBridge.hLabelEquiv_one G C hHCard eA1 eX]
    exact (eX 0).2
  have hH2 : (h 2).1 ∈ C.X := by
    rw [FourZHighDefectGraphBridge.hLabelEquiv_two G C hHCard eA1 eX]
    exact (eX 1).2
  have hH3 : (h 3).1 ∈ C.X := by
    rw [FourZHighDefectGraphBridge.hLabelEquiv_three G C hHCard eA1 eX]
    exact (eX 2).2
  have hA0P : ∀ j : Fin 7, G.Adj (a 0).1 (p j).1 := by
    intro j
    rw [hA0]
    exact (Finset.mem_filter.mp (p j).2).2
  have hP0 : ∀ j : Fin 7, ¬G.Adj (p j).1 (a 0).1 :=
    fun j => hG.2 (hA0P j)
  have hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i).1 (r j).1 := by
    intro i j
    exact P_not_adj_R G C _ _ (p i).2 (r j).2
  have hAE : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i).1 (e j).1 := by
    intro i j
    rcases Finset.mem_union.mp (e j).2 with hjZ | hjRoot
    · exact A_not_adj_Z G C hG _ _ (a i).2 hjZ
    · have hjs : (e j).1 = C.s := by
        simpa [rootSecondFinset, hReach] using hjRoot
      rw [hjs]
      exact hG.2 ((Digraph.mem_outNeighborFinset (G := G)).mp (a i).2)
  have hOrder : ∀ i j : Fin 7, i ≤ j →
      G.outdegree (p j).1 ≤ G.outdegree (p i).1 := by
    intro i j hij
    exact EpsilonOneRootCoreGraphBridge.rootSorted_degree_anti G.outdegree
      (fun v => epsilonAt G v C.s) (directCount G C.H) C.P eP
      (fun v => by simp only [epsilonAt]; split <;> omega)
      (fun v => by
        have hvCard := Finset.card_le_card
          (show C.H.filter (G.Adj v) ⊆ C.H from Finset.filter_subset _ _)
        change (C.H.filter (G.Adj v)).card < 256
        omega) hij
  have hRootOrder : ∀ i j : Fin 7, i ≤ j →
      G.outdegree (p i).1 = G.outdegree (p j).1 →
      epsilonAt G (p j).1 C.s ≤ epsilonAt G (p i).1 C.s := by
    intro i j hij hDegree
    exact EpsilonOneRootCoreGraphBridge.rootSorted_root_anti_of_degree_eq
      G.outdegree (fun v => epsilonAt G v C.s) (directCount G C.H) C.P eP
      (fun v => by
        have hvCard := Finset.card_le_card
          (show C.H.filter (G.Adj v) ⊆ C.H from Finset.filter_subset _ _)
        change (C.H.filter (G.Adj v)).card < 256
        omega) hij hDegree
  have hHOrder : ∀ i j : Fin 7, i ≤ j →
      G.outdegree (p i).1 = G.outdegree (p j).1 →
      epsilonAt G (p i).1 C.s = epsilonAt G (p j).1 C.s →
      directCount G C.H (p j).1 ≤ directCount G C.H (p i).1 := by
    intro i j hij hDegree hRoot
    exact EpsilonOneRootCoreGraphBridge.rootSorted_h_anti_of_degree_root_eq
      G.outdegree (fun v => epsilonAt G v C.s) (directCount G C.H) C.P eP
      hij hDegree hRoot
  let bits := coreBits G.Adj (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (r j).1) (fun j => (a j).1)
    (fun j => (e ⟨j + 1, by omega⟩).1)
  let m := 28 - edgeCount G C.P (externalTargets G C)
  have hExternalLe : edgeCount G C.P (externalTargets G C) ≤ 28 := by
    have hc := edgeCount_le_card_mul_card G C.P (externalTargets G C)
    simpa [hPCard, hECard] using hc
  have hExternal : edgeCount G C.P (externalTargets G C) + m = 28 := by
    dsimp [m]
    omega
  have hmLe : m ≤ 7 := by
    have hl := equationTwentyLower G C hG hMin hRootDegree hBCard hk
    simp [hx, Nat.choose] at hl
    omega
  have hHPGraph : 14 ≤ edgeCount G C.H C.P := by
    have hc := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB
      hRootDegree hk
    simpa [hx, Nat.choose] using hc
  have hPHGraph : edgeCount G C.P C.H ≤ 14 := by
    have hc := cross_edgeCount_add_reverse_le G C.H C.P hG
    rw [hPCard, hHCard] at hc
    omega
  have hExactCard := exactDegree_card_lower G C hG hMin hPB hPCard hHCard
    m hExternal hHPGraph
  have hOr := oriented_true G (fun j => (p j).1) (fun j => (h j).1)
    (fun j => (e j).1) (fun j => (r j).1) (fun j => (a j).1)
    (fun j => (e ⟨j + 1, by omega⟩).1) hG
  have hFixed := fixedStructure_true G C hG hPivot hMin hPB hk p h
    (fun j => (e j).1) r a (fun j => (e ⟨j + 1, by omega⟩).1)
    hA0 hAH hH0 hH1 hH2 hH3 hAR
  have hCovered := covered_true G C p (fun j => (h j).1) e
    (fun j => (r j).1) (fun j => (a j).1)
    (fun j => (e ⟨j + 1, by omega⟩).1)
  have hRows : all 7 (fun i => (8 : BitVec 8).ule (pDegree bits i) &&
      rootEquation bits i && protectedRedundancy bits i) = true := by
    rw [reduced_all_eq_true_iff]
    intro i hi
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [pDegree_toNat G C hG hPB p h e (fun j => (r j).1)
        (fun j => (a j).1) (fun j => (e ⟨j + 1, by omega⟩).1) i hi]
      exact hMin _
    · exact rootEquation_true G C hG hPB hNoSeymour hRootDegree p h e
        (fun j => (r j).1) (fun j => (a j).1)
        (fun j => (e ⟨j + 1, by omega⟩).1) hE0 i hi
    · exact protectedRedundancy_true G hBound C hG hPB hNoSeymour
        hRootDegree hk hx p h e r a hA0 hAH hH0 hAR hE0 i hi
  have hExternalLower : (21 : BitVec 8).ule
      (sumCount 7 (pEOut bits)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
      show (21 : BitVec 8).toNat = 21 by decide]
    rw [totalPE_toNat G C p (fun j => (h j).1) e
      (fun j => (r j).1) (fun j => (a j).1)
      (fun j => (e ⟨j + 1, by omega⟩).1)]
    omega
  have hHPBit : (14 : BitVec 8).ule
      (sumCount 4 (fun q => count 7 (hp bits q))) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [totalHP_toNat G C p h (fun j => (e j).1) (fun j => (r j).1)
      (fun j => (a j).1) (fun j => (e ⟨j + 1, by omega⟩).1)]
    exact hHPGraph
  have hPHBit : (sumCount 7 (pHOut bits)).ule 14 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [totalPH_toNat G C p h (fun j => (e j).1) (fun j => (r j).1)
      (fun j => (a j).1) (fun j => (e ⟨j + 1, by omega⟩).1)]
    exact hPHGraph
  have hNon := hNonSeymour_true G C hG hPB hNoSeymour p h e
    (fun j => (r j).1) a (fun j => (e ⟨j + 1, by omega⟩).1)
    hA0P hP0 hAH hAR hPR hAE
  have hOrdered := aggregateOrderedP_true G C hG hPB p h e
    (fun j => (r j).1) (fun j => (a j).1)
    (fun j => (e ⟨j + 1, by omega⟩).1) hE0 hOrder hRootOrder hHOrder
  have hTail : aggregateTail bits = true := by
    rw [aggregateTail, reduced_all_eq_true_iff]
    intro i hi
    rw [Bool.or_eq_true]
    by_cases hThreshold : 7 - i ≤ m
    · apply Or.inl
      apply beq_iff_eq.mpr
      apply BitVec.eq_of_toNat_eq
      rw [pDegree_toNat G C hG hPB p h e (fun j => (r j).1)
        (fun j => (a j).1) (fun j => (e ⟨j + 1, by omega⟩).1) i hi]
      exact degreeEight_of_sorted_tail G C hMin p hOrder m i hi
        hExactCard hThreshold
    · apply Or.inr
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.reducePow]
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [totalPE_toNat G C p (fun j => (h j).1) e
        (fun j => (r j).1) (fun j => (a j).1)
        (fun j => (e ⟨j + 1, by omega⟩).1)]
      omega
  have hCore : aggregateCore bits = true := by
    simp only [aggregateCore, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hOr, hFixed⟩, hCovered⟩, hRows⟩,
      hExternalLower⟩, hHPBit⟩, hPHBit⟩, hNon⟩, hOrdered⟩, hTail⟩
  have hFalse : aggregateCore bits = false := aggregateCore_unsat bits
  rw [hFalse] at hCore
  contradiction

end SeymourEight.EpsilonOneXThreeReducedGraphBridge
