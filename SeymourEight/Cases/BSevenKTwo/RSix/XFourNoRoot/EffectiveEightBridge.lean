import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Labels
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.EffectiveEight
import Batteries.Data.BitVec.Lemmas

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.EffectiveEightBridge

open CertificateBridge Shared
open EffectiveEightCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def bitAt (p : Fin 6 → V) (e : Fin 3 → V) (w : Fin 7 → V)
    (n : Nat) : Bool :=
  if n < 18 then
    decide (G.Adj (p ⟨(n / 3) % 6, Nat.mod_lt _ (by omega)⟩)
      (e ⟨n % 3, Nat.mod_lt _ (by omega)⟩))
  else if n < 36 then
    let q := n - 18
    decide (G.Adj (e ⟨(q / 6) % 3, Nat.mod_lt _ (by omega)⟩)
      (p ⟨q % 6, Nat.mod_lt _ (by omega)⟩))
  else if n < 45 then
    let q := n - 36
    decide (G.Adj (e ⟨(q / 3) % 3, Nat.mod_lt _ (by omega)⟩)
      (e ⟨q % 3, Nat.mod_lt _ (by omega)⟩))
  else
    let q := n - 45
    decide (G.Adj (e ⟨(q / 7) % 3, Nat.mod_lt _ (by omega)⟩)
      (w ⟨q % 7, Nat.mod_lt _ (by omega)⟩))

def graphBits (p : Fin 6 → V) (e : Fin 3 → V) (w : Fin 7 → V) :
    EffectiveEightCore.Encoding :=
  BitVec.ofFnLE fun n : Fin 66 ↦ bitAt G p e w n

private theorem div_index (i j width : Nat) (hj : j < width) :
    (width * i + j) / width = i := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j width : Nat) (hj : j < width) :
    (width * i + j) % width = j := by
  simpa [Nat.mul_comm] using Nat.mul_add_mod_of_lt (a := i) hj

omit [Fintype V] [DecidableEq V] in
@[simp] theorem graphBits_get (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (n : Nat) (hn : n < 66) :
    (graphBits G p e w).getLsbD n = bitAt G p e w n := by
  classical
  rw [graphBits, BitVec.getLsbD_ofFnLE]
  simp only [hn, ↓reduceDIte]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pToE_graphBits (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (i j : Nat) (hi : i < 6) (hj : j < 3) :
    pToE (graphBits G p e w) i j =
      decide (G.Adj (p ⟨i, hi⟩) (e ⟨j, hj⟩)) := by
  classical
  rw [pToE, graphBits_get G p e w (3 * i + j) (by omega)]
  simp only [bitAt, if_pos (by omega : 3 * i + j < 18)]
  have hd : (3 * i + j) / 3 = i := div_index i j 3 hj
  have hm : (3 * i + j) % 3 = j := mod_index i j 3 hj
  have hp : p ⟨(3 * i + j) / 3 % 6, by omega⟩ = p ⟨i, hi⟩ := by
    apply congrArg p; apply Fin.ext; simp [hd, Nat.mod_eq_of_lt hi]
  have he : e ⟨(3 * i + j) % 3, by omega⟩ = e ⟨j, hj⟩ := by
    apply congrArg e; apply Fin.ext; exact hm
  rw [hp, he]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem eToP_graphBits (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (i j : Nat) (hi : i < 3) (hj : j < 6) :
    eToP (graphBits G p e w) i j =
      decide (G.Adj (e ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  classical
  rw [eToP, graphBits_get G p e w (18 + 6 * i + j) (by omega)]
  simp only [bitAt, if_neg (by omega : ¬18 + 6 * i + j < 18),
    if_pos (by omega : 18 + 6 * i + j < 36)]
  have hsub : 18 + 6 * i + j - 18 = 6 * i + j := by omega
  simp only [hsub]
  have hd : (6 * i + j) / 6 = i := div_index i j 6 hj
  have hm : (6 * i + j) % 6 = j := mod_index i j 6 hj
  have he : e ⟨(6 * i + j) / 6 % 3, by omega⟩ = e ⟨i, hi⟩ := by
    apply congrArg e; apply Fin.ext; simp [hd, Nat.mod_eq_of_lt hi]
  have hp : p ⟨(6 * i + j) % 6, by omega⟩ = p ⟨j, hj⟩ := by
    apply congrArg p; apply Fin.ext; exact hm
  rw [he, hp]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem eArc_graphBits (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (i j : Nat) (hi : i < 3) (hj : j < 3) :
    eArc (graphBits G p e w) i j =
      decide (i ≠ j ∧ G.Adj (e ⟨i, hi⟩) (e ⟨j, hj⟩)) := by
  classical
  by_cases hij : i = j
  · subst j
    simp [eArc]
  · rw [eArc, graphBits_get G p e w (36 + 3 * i + j) (by omega)]
    simp only [bitAt, if_neg (by omega : ¬36 + 3 * i + j < 18),
      if_neg (by omega : ¬36 + 3 * i + j < 36),
      if_pos (by omega : 36 + 3 * i + j < 45)]
    have hsub : 36 + 3 * i + j - 36 = 3 * i + j := by omega
    simp only [hsub]
    have hd : (3 * i + j) / 3 = i := div_index i j 3 hj
    have hm : (3 * i + j) % 3 = j := mod_index i j 3 hj
    have hei : e ⟨(3 * i + j) / 3 % 3, by omega⟩ = e ⟨i, hi⟩ := by
      apply congrArg e; apply Fin.ext; simp [hd, Nat.mod_eq_of_lt hi]
    have hej : e ⟨(3 * i + j) % 3, by omega⟩ = e ⟨j, hj⟩ := by
      apply congrArg e; apply Fin.ext; exact hm
    rw [hei, hej]
    simp [hij]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem eToW_graphBits (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (i j : Nat) (hi : i < 3) (hj : j < 7) :
    eToW (graphBits G p e w) i j =
      decide (G.Adj (e ⟨i, hi⟩) (w ⟨j, hj⟩)) := by
  classical
  rw [eToW, graphBits_get G p e w (45 + 7 * i + j) (by omega)]
  simp only [bitAt, if_neg (by omega : ¬45 + 7 * i + j < 18),
    if_neg (by omega : ¬45 + 7 * i + j < 36),
    if_neg (by omega : ¬45 + 7 * i + j < 45)]
  have hsub : 45 + 7 * i + j - 45 = 7 * i + j := by omega
  simp only [hsub]
  have hd : (7 * i + j) / 7 = i := div_index i j 7 hj
  have hm : (7 * i + j) % 7 = j := mod_index i j 7 hj
  have he : e ⟨(7 * i + j) / 7 % 3, by omega⟩ = e ⟨i, hi⟩ := by
    apply congrArg e; apply Fin.ext; simp [hd, Nat.mod_eq_of_lt hi]
  have hw : w ⟨(7 * i + j) % 7, by omega⟩ = w ⟨j, hj⟩ := by
    apply congrArg w; apply Fin.ext; exact hm
  rw [he, hw]

def targetVertex (p : Fin 6 → V) (e : Fin 3 → V)
    (target : Nat) : V :=
  if ht : target < 3 then e ⟨target, ht⟩
  else p ⟨(target - 3) % 6, Nat.mod_lt _ (by omega)⟩

omit [Fintype V] [DecidableEq V] in
theorem localArc_graphBits (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (i target : Nat) (hi : i < 3) (ht : target < 9) :
    localArc (graphBits G p e w) i target =
      if target < 3 then
        decide (i ≠ target ∧ G.Adj (e ⟨i, hi⟩) (targetVertex p e target))
      else decide (G.Adj (e ⟨i, hi⟩) (targetVertex p e target)) := by
  classical
  unfold localArc targetVertex
  split
  · simp_all
  · have hidx : target - 3 < 6 := by omega
    rw [eToP_graphBits G p e w i (target - 3) hi hidx]
    simp [Nat.mod_eq_of_lt hidx]

omit [Fintype V] [DecidableEq V] in
theorem targetToE_graphBits (p : Fin 6 → V) (e : Fin 3 → V)
    (w : Fin 7 → V) (target i : Nat) (ht : target < 9) (hi : i < 3) :
    targetToE (graphBits G p e w) target i =
      if target < 3 then
        decide (target ≠ i ∧ G.Adj (targetVertex p e target) (e ⟨i, hi⟩))
      else decide (G.Adj (targetVertex p e target) (e ⟨i, hi⟩)) := by
  classical
  unfold targetToE targetVertex
  split
  · simp_all
  · have hidx : target - 3 < 6 := by omega
    rw [pToE_graphBits G p e w (target - 3) i hidx hi]
    simp [Nat.mod_eq_of_lt hidx]

private theorem sum_fin18_eq_blocks (f : Fin 18 → Nat) :
    (∑ q, f q) = ∑ i : Fin 6, ∑ j : Fin 3,
      f ⟨i * 3 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 6 × Fin 3 ≃ Fin 18).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp [finProdFinEquiv]
  omega

private theorem sum_fin9_split (f : Nat → Nat) :
    (∑ i : Fin 9, f i) =
      (∑ i : Fin 3, f i) + ∑ j : Fin 6, f (3 + j) := by
  simp [Fin.sum_univ_succ, Nat.add_assoc]

set_option linter.flexible false in
/-- A seven-vertex outside union for three auxiliaries with at most one
missing `P → E` incidence has the deletion configuration certified above,
and hence contradicts the degree-seven theorem after deleting one arc. -/
theorem exactSevenAuxiliaryUnion_false
    (hBound : Digraph.LimitedSeymourConjectureOn V 7)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (P E W : Finset V) (hPCard : P.card = 6)
    (hECard : E.card = 3) (hWCard : W.card = 7)
    (hEP : Disjoint E P) (hEW : Disjoint E W) (hPW : Disjoint P W)
    (hPE : edgeCount G P E = 18)
    (hCaptured : ∀ e ∈ E, G.outNeighborFinset e ⊆ E ∪ P ∪ W) : False := by
  classical
  let lp := finsetEquivFin P hPCard
  let le := finsetEquivFin E hECard
  let lw := finsetEquivFin W hWCard
  let bits := graphBits G (fun i => (lp i).1) (fun i => (le i).1)
    (fun i => (lw i).1)
  have hOrientedE : Shared.FiniteCore.all 3 (fun e =>
      Shared.FiniteCore.all 3 fun f =>
        decide (e = f) || !(eArc bits e f && eArc bits f e)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro i hi
    rw [Bridge.all_eq_true_iff]
    intro j hj
    simp only [bits, eArc_graphBits G _ _ _ i j hi hj,
      eArc_graphBits G _ _ _ j i hj hi]
    by_cases hij : i = j
    · simp [hij]
    · by_cases ha : G.Adj (le ⟨i, hi⟩).1 (le ⟨j, hj⟩).1
      · simp [hij, ha, hG.2 ha]
      · simp [hij, ha]
  have hOrientedCross : Shared.FiniteCore.all 3 (fun e =>
      Shared.FiniteCore.all 6 fun p =>
        !(eToP bits e p && pToE bits p e)) = true := by
    rw [Bridge.all_eq_true_iff]
    intro i hi
    rw [Bridge.all_eq_true_iff]
    intro j hj
    simp only [bits, eToP_graphBits G _ _ _ i j hi hj,
      pToE_graphBits G _ _ _ j i hj hi]
    by_cases ha : G.Adj (le ⟨i, hi⟩).1 (lp ⟨j, hj⟩).1
    · simp [ha, hG.2 ha]
    · simp [ha]
  have hTotalPEToNat :
      (Shared.FiniteCore.count 18
        (fun n => pToE bits (n / 3) (n % 3))).toNat = edgeCount G P E := by
    rw [Bridge.toNat_count_eq_fin_sum 18 _ (by omega),
      sum_fin18_eq_blocks]
    simp only [bits]
    rw [edgeCount_eq_sum_fin G P E lp]
    apply Finset.sum_congr rfl
    intro i _
    rw [directCount_eq_sum_fin G E le]
    apply Finset.sum_congr rfl
    intro j _
    have hd : (i.val * 3 + j.val) / 3 = i.val := by omega
    have hm : (i.val * 3 + j.val) % 3 = j.val := by omega
    simp [hd, hm]
  have hTotalPE :
      (Shared.FiniteCore.count 18
        (fun n => pToE bits (n / 3) (n % 3)) == 18) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hTotalPEToNat, hPE]
    decide
  have hDegrees : Shared.FiniteCore.all 3 (fun e =>
      (8 : BitVec 8).ule
        (Shared.FiniteCore.count 9 (localArc bits e) +
          Shared.FiniteCore.count 7 (eToW bits e))) = true := by
    rw [Bridge.all_eq_true_iff]
    intro i hi
    let u := (le ⟨i, hi⟩).1
    have hLocal : (Shared.FiniteCore.count 9 (localArc bits i)).toNat =
        directCount G E u + directCount G P u := by
      rw [Bridge.toNat_count_eq_fin_sum 9 _ (by omega)]
      rw [sum_fin9_split
        (fun k => if localArc bits i k = true then 1 else 0)]
      rw [directCount_eq_sum_fin G E le, directCount_eq_sum_fin G P lp]
      apply congrArg₂ (·+·)
      · apply Finset.sum_congr rfl
        intro j _
        simp only [localArc, if_pos (by omega : j.val < 3), bits,
          eArc_graphBits G _ _ _ i j hi j.isLt]
        by_cases hij : i = j
        · have hVertices : (le ⟨i, hi⟩).1 = (le j).1 := by
            apply congrArg Subtype.val
            apply congrArg le
            apply Fin.ext
            exact hij
          simp [hij, hVertices, u]
          exact hG.1 _
        · simp [hij, u]
      · apply Finset.sum_congr rfl
        intro j _
        simp only [localArc, if_neg (by omega : ¬3 + j.val < 3), bits]
        have hsub : 3 + j.val - 3 = j.val := by omega
        simp only [hsub]
        rw [eToP_graphBits G _ _ _ i j hi j.isLt]
    have hOutside : (Shared.FiniteCore.count 7 (eToW bits i)).toNat =
        directCount G W u := by
      rw [Bridge.toNat_count_eq_fin_sum 7 _ (by omega),
        directCount_eq_sum_fin G W lw]
      apply Finset.sum_congr rfl
      intro j _
      rw [eToW_graphBits G _ _ _ i j hi j.isLt]
    have hDegreeEq : G.outdegree u =
        directCount G E u + directCount G P u + directCount G W u := by
      have hc := hCaptured u (le ⟨i, hi⟩).2
      have h := outdegree_eq_directCount_of_captured G (E ∪ P ∪ W) u hc
      have hEPW : Disjoint (E ∪ P) W := by
        rw [Finset.disjoint_left]
        intro v hvEP hvW
        rcases Finset.mem_union.mp hvEP with hvE | hvP
        · exact (Finset.disjoint_left.mp hEW) hvE hvW
        · exact (Finset.disjoint_left.mp hPW) hvP hvW
      rw [directCount_union_of_disjoint G (E ∪ P) W u hEPW,
        directCount_union_of_disjoint G E P u hEP] at h
      exact h
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
      BitVec.toNat_add]
    have hEL : directCount G E u ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
    have hPL : directCount G P u ≤ 6 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hWL : directCount G W u ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hWCard
    rw [Nat.mod_eq_of_lt (by rw [hLocal, hOutside]; omega),
      hLocal, hOutside, ← hDegreeEq]
    exact hMin u
  have hConditions : conditions bits = true := by
    simp only [conditions, Bool.and_eq_true]
    exact ⟨⟨⟨hOrientedE, hOrientedCross⟩, hTotalPE⟩, hDegrees⟩
  have hWitness := conditions_imply_witness bits hConditions
  rw [deletionWitness, Bridge.any_eq_true_iff] at hWitness
  obtain ⟨ui, hui, hWitness⟩ := hWitness
  rw [Bridge.any_eq_true_iff] at hWitness
  obtain ⟨vi, hvi, hWitness⟩ := hWitness
  rw [Bridge.any_eq_true_iff] at hWitness
  obtain ⟨ti, hti, hWitness⟩ := hWitness
  simp only [Bool.and_eq_true] at hWitness
  rcases hWitness with ⟨⟨⟨⟨⟨⟨⟨hLocalOne, hAllUW⟩, huv⟩,
    hAllVW⟩, hvt⟩, hut⟩, hnut⟩, hAllTW⟩
  let u := (le ⟨ui, hui⟩).1
  let v := targetVertex (fun i => (lp i).1) (fun i => (le i).1) vi
  let t := (le ⟨ti, hti⟩).1
  have hutIdx : ui ≠ ti := of_decide_eq_true hut
  have huvAdj : G.Adj u v := by
    rw [localArc_graphBits G _ _ _ ui vi hui (by omega)] at huv
    by_cases hvE : vi < 3
    · simp [hvE] at huv
      exact huv.2
    · simpa [hvE, u, v] using huv
  have hvtAdj : G.Adj v t := by
    rw [targetToE_graphBits G _ _ _ vi ti (by omega) hti] at hvt
    by_cases hvE : vi < 3
    · simp [hvE] at hvt
      exact hvt.2
    · simpa [hvE, v, t] using hvt
  have hutNe : u ≠ t := by
    intro heq
    apply hutIdx
    have heq' : (le ⟨ui, hui⟩).1 = (le ⟨ti, hti⟩).1 := by
      exact heq
    exact Fin.ext_iff.mp (le.injective (Subtype.ext heq'))
  have hAllUWAdj : ∀ x ∈ W, G.Adj u x := by
    intro x hxW
    obtain ⟨j, hj⟩ := lw.surjective ⟨x, hxW⟩
    have hjBool := (Bridge.all_eq_true_iff 7 _).mp hAllUW j j.isLt
    rw [eToW_graphBits G _ _ _ ui j hui j.isLt] at hjBool
    have hjAdj : G.Adj (le ⟨ui, hui⟩).1 (lw j).1 := by
      simpa only [decide_eq_true_eq] using hjBool
    simpa [u, congrArg Subtype.val hj] using hjAdj
  have hAllTWAdj : ∀ x ∈ W, G.Adj t x := by
    intro x hxW
    obtain ⟨j, hj⟩ := lw.surjective ⟨x, hxW⟩
    have hjBool := (Bridge.all_eq_true_iff 7 _).mp hAllTW j j.isLt
    rw [eToW_graphBits G _ _ _ ti j hti j.isLt] at hjBool
    have hjAdj : G.Adj (le ⟨ti, hti⟩).1 (lw j).1 := by
      simpa only [decide_eq_true_eq] using hjBool
    simpa [t, congrArg Subtype.val hj] using hjAdj
  have hAllVWAdj : ∀ x ∈ W, G.Adj v x := by
    intro x hxW
    obtain ⟨j, hj⟩ := lw.surjective ⟨x, hxW⟩
    have hjBool := (Bridge.all_eq_true_iff 7 _).mp hAllVW j j.isLt
    rw [eToW_graphBits G _ _ _ vi j hvi j.isLt] at hjBool
    have hjAdj : G.Adj (le ⟨vi, hvi⟩).1 (lw j).1 := by
      simpa only [decide_eq_true_eq] using hjBool
    simpa [v, targetVertex, hvi, congrArg Subtype.val hj] using hjAdj
  have hnutAdj : ¬G.Adj u t := by
    have hFalse : localArc bits ui ti = false := by
      simpa using hnut
    rw [localArc_graphBits G _ _ _ ui ti hui (by omega)] at hFalse
    simp only [if_pos (by omega : ti < 3), decide_eq_false_iff_not] at hFalse
    exact fun hutAdj => hFalse ⟨hutIdx, by
      simpa [u, t, targetVertex, hti] using hutAdj⟩
  have hvLocal : v ∈ E ∪ P := by
    by_cases hvE : vi < 3
    · exact Finset.mem_union_left _ (by simp [v, targetVertex, hvE])
    · have hvP : vi - 3 < 6 := by omega
      exact Finset.mem_union_right _ (by
        simp [v, targetVertex, hvE, Nat.mod_eq_of_lt hvP])
  have hvNotW : v ∉ W := by
    intro hvW
    rcases Finset.mem_union.mp hvLocal with hvE | hvP
    · exact (Finset.disjoint_left.mp hEW) hvE hvW
    · exact (Finset.disjoint_left.mp hPW) hvP hvW
  have hLocalCountNat :
      (Shared.FiniteCore.count 9 (localArc bits ui)).toNat =
        directCount G E u + directCount G P u := by
    rw [Bridge.toNat_count_eq_fin_sum 9 _ (by omega)]
    rw [sum_fin9_split
      (fun k => if localArc bits ui k = true then 1 else 0)]
    rw [directCount_eq_sum_fin G E le, directCount_eq_sum_fin G P lp]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro j _
      simp only [localArc, if_pos (by omega : j.val < 3), bits,
        eArc_graphBits G _ _ _ ui j hui j.isLt]
      by_cases hij : ui = j
      · have hVertices : (le ⟨ui, hui⟩).1 = (le j).1 := by
          apply congrArg Subtype.val
          apply congrArg le
          apply Fin.ext
          exact hij
        simp [hij, hVertices, u]
        exact hG.1 _
      · simp [hij, u]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [localArc, if_neg (by omega : ¬3 + j.val < 3), bits]
      have hsub : 3 + j.val - 3 = j.val := by omega
      simp only [hsub]
      rw [eToP_graphBits G _ _ _ ui j hui j.isLt]
  have hLocalCount : directCount G E u + directCount G P u = 1 := by
    rw [beq_iff_eq] at hLocalOne
    have hNat := congrArg BitVec.toNat hLocalOne
    have hOne : (1 : BitVec 8).toNat = 1 := by decide
    rw [hOne, hLocalCountNat] at hNat
    exact hNat
  have hEPW : Disjoint (E ∪ P) W := by
    rw [Finset.disjoint_left]
    intro x hxEP hxW
    rcases Finset.mem_union.mp hxEP with hxE | hxP
    · exact (Finset.disjoint_left.mp hEW) hxE hxW
    · exact (Finset.disjoint_left.mp hPW) hxP hxW
  have hLocalUnionCount : directCount G (E ∪ P) u = 1 := by
    rw [directCount_union_of_disjoint G E P u hEP]
    exact hLocalCount
  have hWCount : directCount G W u = 7 := by
    unfold directCount internalFirstNeighbors
    have hEq : W.filter (G.Adj u) = W := by
      apply Finset.Subset.antisymm (Finset.filter_subset _ _)
      intro x hxW
      exact Finset.mem_filter.mpr ⟨hxW, hAllUWAdj x hxW⟩
    rw [hEq, hWCard]
  have hDegreeEq : G.outdegree u = 8 := by
    have huE : u ∈ E := (le ⟨ui, hui⟩).2
    have h := outdegree_eq_directCount_of_captured G (E ∪ P ∪ W) u
      (hCaptured u huE)
    rw [directCount_union_of_disjoint G (E ∪ P) W u hEPW,
      hLocalUnionCount, hWCount] at h
    omega
  let Local := internalFirstNeighbors G (E ∪ P) u
  have hvInLocal : v ∈ Local := Finset.mem_filter.mpr ⟨hvLocal, huvAdj⟩
  have hLocalEq : Local = {v} := by
    have hCard : Local.card = 1 := hLocalUnionCount
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hCard
    have hva : v = a := by simpa [ha] using hvInLocal
    simpa [hva] using ha
  have hErase : (G.outNeighborFinset u).erase v = W := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_erase.mp hx with ⟨hxv, hxOut⟩
      have hxCap := hCaptured u (le ⟨ui, hui⟩).2 hxOut
      rcases Finset.mem_union.mp hxCap with hxLocal | hxW
      · have hxL : x ∈ Local := Finset.mem_filter.mpr
          ⟨hxLocal, (Digraph.mem_outNeighborFinset (G := G)).mp hxOut⟩
        have : x = v := by simpa [hLocalEq] using hxL
        exact (hxv this).elim
      · exact hxW
    · intro hxW
      exact Finset.mem_erase.mpr ⟨fun hxv => hvNotW (hxv ▸ hxW),
        (Digraph.mem_outNeighborFinset (G := G)).mpr (hAllUWAdj x hxW)⟩
  let D := G.outNeighborFinsetOf W \ (W ∪ {u})
  have hDCard : 7 ≤ D.card := by
    have hExpansion := Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour
      hDegreeEq huvAdj
    simpa [D, hErase] using hExpansion
  have hDSecond : D ⊆ G.secondOutNeighborFinset u := by
    intro x hxD
    rcases Finset.mem_sdiff.mp hxD with ⟨hxReach, hxOutside⟩
    obtain ⟨w, hwW, hwx⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hxReach
    have huxNot : ¬G.Adj u x := by
      intro hux
      have hxOut : x ∈ G.outNeighborFinset u :=
        (Digraph.mem_outNeighborFinset (G := G)).mpr hux
      by_cases hxv : x = v
      · subst x
        exact hG.2 (hAllVWAdj w hwW) hwx
      · have hxErase : x ∈ (G.outNeighborFinset u).erase v :=
          Finset.mem_erase.mpr ⟨hxv, hxOut⟩
        have hxW : x ∈ W := by simpa [hErase] using hxErase
        exact hxOutside (Finset.mem_union_left _ hxW)
    have hxu : x ≠ u := by
      intro hxu
      subst x
      exact hxOutside (Finset.mem_union_right _ (Finset.mem_singleton_self u))
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨w, hAllUWAdj w hwW, hwx⟩, huxNot, hxu⟩
  have htSecond : t ∈ G.secondOutNeighborFinset u := by
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨v, huvAdj, hvtAdj⟩, hnutAdj, hutNe.symm⟩
  have htNotD : t ∉ D := by
    intro htD
    have htReach := (Finset.mem_sdiff.mp htD).1
    obtain ⟨w, hwW, hwt⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
    exact hG.2 (hAllTWAdj w hwW) hwt
  have hUnionSubset : D ∪ {t} ⊆ G.secondOutNeighborFinset u :=
    Finset.union_subset hDSecond (by simpa using htSecond)
  have hCard := Finset.card_le_card hUnionSubset
  have hUnionCard : (D ∪ {t}).card = D.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro x hxD hxt
      simpa using htNotD (Finset.mem_singleton.mp hxt ▸ hxD)
  rw [hUnionCard] at hCard
  apply hNoSeymour
  refine ⟨u, ?_⟩
  unfold Digraph.IsSeymourVertex Digraph.secondOutdegree
  rw [hDegreeEq]
  omega

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.EffectiveEightBridge
