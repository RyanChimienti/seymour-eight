import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.GraphBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.MicroBridge
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.SharpKing
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalFour
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalMicroHRangeBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.ReachedAssembly

open Shared Shared.FiniteCore
open Labels Encoding Core GraphBridge MicroScratch

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private noncomputable def finsetEquivAtZero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    Fin n ≃ {w : V // w ∈ S} :=
  let base := finsetEquivFin S hCard
  (Equiv.swap ⟨0, hn⟩ (base.symm ⟨v, hv⟩)).trans base

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem finsetEquivAtZero_zero {n : Nat} (S : Finset V)
    (hn : 0 < n) (hCard : S.card = n) (v : V) (hv : v ∈ S) :
    (finsetEquivAtZero S hn hCard v hv ⟨0, hn⟩).1 = v := by
  classical
  simp [finsetEquivAtZero]

private theorem q_not_mem_Z (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) : q ∉ C.Z := by
  intro hqZ
  exact (Finset.disjoint_left.mp
    (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hqZ
    (Finset.mem_union_right ({C.s} ∪ C.A)
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ))

private noncomputable def reachedFourSetEquiv (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hZCard : C.Z.card = 3)
    (eZ : Fin 3 ≃ {v : V // v ∈ C.Z}) :
    Fin 4 ≃ {v : V // v ∈ ({q} ∪ C.Z : Finset V)} := by
  let e := reachedExternalFour G C q (fun i => (eZ i).1)
  let f : Fin 4 → {v : V // v ∈ ({q} ∪ C.Z : Finset V)} := fun i =>
    ⟨e ⟨i.val, by omega⟩, by
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        subst i
        simp [e]
      · let z : Fin 3 := ⟨i.val - 1, by omega⟩
        have hi' : i = ⟨z.val + 1, by omega⟩ := Fin.ext (by dsimp [z]; omega)
        rw [hi']
        simp [e]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    have hval : e ⟨i.val, by omega⟩ = e ⟨j.val, by omega⟩ := by
      simpa [f] using congrArg Subtype.val hij
    have hFin := reachedExternalFour_injective G C q hqQ eZ hval
    apply Fin.ext
    simpa using congrArg Fin.val hFin
  · simp only [Fintype.card_fin, Fintype.card_coe]
    rw [Finset.card_union_of_disjoint]
    · simp [hZCard]
    · rw [Finset.disjoint_left]
      intro v hvq hvz
      exact q_not_mem_Z G C q hqQ (Finset.mem_singleton.mp hvq ▸ hvz)

@[simp] private theorem reachedFourSetEquiv_val (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hZCard : C.Z.card = 3)
    (eZ : Fin 3 ≃ {v : V // v ∈ C.Z}) (i : Fin 4) :
    (reachedFourSetEquiv G C q hqQ hZCard eZ i).1 =
      reachedExternalFour G C q (fun z => (eZ z).1) ⟨i.val, by omega⟩ := rfl

private noncomputable def reachedFiveSetEquiv (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hZCard : C.Z.card = 4)
    (eZ : Fin 4 ≃ {v : V // v ∈ C.Z}) :
    Fin 5 ≃ {v : V // v ∈ ({q} ∪ C.Z : Finset V)} := by
  let e := reachedExternalFive q (fun i => (eZ i).1)
  let f : Fin 5 → {v : V // v ∈ ({q} ∪ C.Z : Finset V)} := fun i =>
    ⟨e i, by
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        subst i
        simp [e]
      · let z : Fin 4 := ⟨i.val - 1, by omega⟩
        have hi' : i = ⟨z.val + 1, by omega⟩ := Fin.ext (by dsimp [z]; omega)
        rw [hi']
        simp [e]⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    apply reachedExternalFive_injective G C q hqQ eZ
    simpa [f, e] using congrArg Subtype.val hij
  · simp only [Fintype.card_fin, Fintype.card_coe]
    rw [Finset.card_union_of_disjoint]
    · simp [hZCard]
    · rw [Finset.disjoint_left]
      intro v hvq hvz
      exact q_not_mem_Z G C q hqQ (Finset.mem_singleton.mp hvq ▸ hvz)

@[simp] private theorem reachedFiveSetEquiv_val (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hZCard : C.Z.card = 4)
    (eZ : Fin 4 ≃ {v : V // v ∈ C.Z}) (i : Fin 5) :
    (reachedFiveSetEquiv G C q hqQ hZCard eZ i).1 =
      reachedExternalFive q (fun z => (eZ z).1) i := rfl

private theorem externalMissingFive_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hHCard : C.H.card = 4) (E : Finset V)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1) :
    (externalMissing 5 (Encoding.coreBits G.Adj L)).toNat =
      30 - edgeCount G C.P E := by
  rw [externalMissing, BitVec.toNat_sub,
    totalPToE_toNat G C q L hG hHCard E eEq (by omega) hELab]
  have hCap := edgeCount_le_card_mul_card G C.P E
  have hp : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have he : E.card = 5 := by
    simpa using (Fintype.card_congr eEq).symm
  rw [hp, he] at hCap
  norm_num [BitVec.toNat_ofNat]
  change (256 - edgeCount G C.P E + 30) % 256 = _
  have heq : 256 - edgeCount G C.P E + 30 =
      256 + (30 - edgeCount G C.P E) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  have hlt : 30 - edgeCount G C.P E < 256 := by omega
  simp [Nat.mod_eq_of_lt hlt]

private theorem totalPToEFour_sub_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hHCard : C.H.card = 4) (E : Finset V)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1) :
    (24 - totalPToE 4 (Encoding.coreBits G.Adj L)).toNat =
      24 - edgeCount G C.P E := by
  rw [BitVec.toNat_sub,
    totalPToE_toNat G C q L hG hHCard E eEq (by omega) hELab]
  have hCap := edgeCount_le_card_mul_card G C.P E
  have hp : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have he : E.card = 4 := by
    simpa using (Fintype.card_congr eEq).symm
  rw [hp, he] at hCap
  norm_num [BitVec.toNat_ofNat]
  change (256 - edgeCount G C.P E + 24) % 256 = _
  have heq : 256 - edgeCount G C.P E + 24 =
      256 + (24 - edgeCount G C.P E) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  have hlt : 24 - edgeCount G C.P E < 256 := by omega
  simp [Nat.mod_eq_of_lt hlt]

set_option linter.flexible false in
/-- The complete Boolean package for the reached `|Z|=3` row.  The unused
fifth external slot is the root; this is needed by the restricted-second
bridge even though `microFour` only counts the first four slots. -/
theorem reachedFour_package_of_labels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hNoRoot : epsilonS G C = 0)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (hy : BSevenKTwo.y G C = 1) (hZCard : C.Z.card = 3)
    (E : Finset V) (hE : E = {q} ∪ C.Z)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (he0 : L.e 0 = q)
    (eZ : Fin 3 ≃ {v : V // v ∈ C.Z})
    (hZLab : ∀ i : Fin 3, L.e ⟨i.val + 1, by omega⟩ = (eZ i).1)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e)
    (hZero : directCount G C.A1 (L.a 1).1 = 0)
    (hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x)
    (c : Nat) (hc : edgeCount G C.A1 {q} = c) :
    microFourDistinguished c (Encoding.coreBits G.Adj L) = true := by
  let bits := Encoding.coreBits G.Adj L
  have hOrP := orientedP_true G C q L hG
  have hOrPH := orientedPH_true G C q L hG
  have hOrHH := orientedHH_true G C q L hG
  have hAMin0 := aOneMinimum_true G C q hqQ hQ L hG hPivot hHCard hk hr
  have hAMin : all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
      (!(count 4 (hArc bits a) == 2) ||
        (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) = true := by
    simpa [bits, hToQCore] using hAMin0
  have hHMin0 := hMinimum_true G C q hqQ hQ L hG hMin hHCard hRCard
  have hHMin : all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) = true := by
    simpa [bits, hDirectCore, hToQCore] using hHMin0
  have hXR := everyXReached_true G C q L hk
  have hQR := qStructureReached_true G C q hqQ hQ L he0 hy c hc
  have hZR := labelledZReached_true (zCount := 3) (offset := 1)
    G C q L eZ (by omega) (by simpa [Nat.add_comm] using hZLab)
  have hPMin := pMinimumDegreeReached_true G C q hqQ hQ L hG hHCard
    hMin hNoRoot E hE eEq (by omega) hELab
  have hHNS := all_hRestrictedNonSeymourFour_true G C q hqQ hQ L hG
    hNoSeymour hHCard hRCard he0 heZ heInj c
  have hPNS := all_pMicroNonSeymourFour_true G C q hqQ hQ L hG
    hNoSeymour hHCard hNoRoot E hE eEq hELab he0 heZ heInj c
  have hDist := distinguishedAOne_true G C q L hG hZero hX
  have hAOneNat := aOneToQ_toNat G C q L (aOneEquiv G C q L hk)
    (fun i => aOneEquiv_val G C q L hk i)
  have hcLe : c ≤ 2 := by
    rw [← hc]
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  have hCEq : aOneToQ bits = BitVec.ofNat 8 c := by
    apply BitVec.eq_of_toNat_eq
    rw [show (aOneToQ bits).toNat = edgeCount G C.A1 {q} by
      simpa [bits] using hAOneNat, hc]
    simp [BitVec.toNat_ofNat]
    omega
  have hHPLowerGraph := H_to_P_lower G C q hqQ hQ hG hMin hk hx hRCard
  have hHPUpperGraph := H_to_P_add_missing_four_le G C q hQ hG hMin hr
    hNoRoot hHCard hZCard
  have hLower : (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using totalHToP_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    have hlt : 16 - c < 256 := by omega
    rw [Nat.mod_eq_of_lt hlt, ← hc]
    exact hHPLowerGraph
  have hUpper : (totalHToP bits + (24 - totalPToE 4 bits)).ule 15 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using totalHToP_toNat G C q L hHCard,
      show (24 - totalPToE 4 bits).toNat = 24 - edgeCount G C.P E by
        simpa [bits] using totalPToEFour_sub_toNat G C q L hG hHCard E eEq hELab]
    norm_num [BitVec.toNat_ofNat]
    have hSmall : edgeCount G C.H C.P + (24 - edgeCount G C.P E) < 256 := by
      omega
    rw [Nat.mod_eq_of_lt hSmall]
    simpa [hE] using hHPUpperGraph
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := hr
  have hPHGraph : edgeCount G C.P C.H ≤ 8 + c := by
    rw [hPCard, hHCard] at hCross
    omega
  have hPH : (totalPToH bits).ule (BitVec.ofNat 8 (8 + c)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalPToH bits).toNat = edgeCount G C.P C.H by
      simpa [bits] using totalPToH_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    have hlt : 8 + c < 256 := by omega
    simpa [Nat.mod_eq_of_lt hlt] using hPHGraph
  have hCore : microFour c bits = true := by
    simp only [microFour, Bool.and_eq_true]
    aesop
  rw [microFourDistinguished, Bool.and_eq_true]
  exact ⟨hCore, by simpa [bits] using hDist⟩

/-- End-to-end reached `|Z|=3` contradiction.  This theorem constructs the
distinguished `A₁` ordering internally and then invokes the two completed
`microFour` certificates. -/
theorem reachedFour_impossible (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hNoRoot : epsilonS G C = 0)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (hy : BSevenKTwo.y G C = 1) (hZCard : C.Z.card = 3) : False := by
  obtain ⟨u, huAOne, huA, huZero, huX⟩ :=
    exists_distinguished_aOne G C hG hPivot hk hx
  let eA1 : Fin 2 ≃ {v : V // v ∈ C.A1} :=
    finsetEquivAtZero C.A1 (by omega) (by exact hk) u huAOne
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X (by exact hx)
  let eZ : Fin 3 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let e : Fin 5 → V := reachedExternalFour G C q (fun i => (eZ i).1)
  let L : ReachedLabels G C q :=
    labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e
  let eEq : Fin 4 ≃ {v : V // v ∈ ({q} ∪ C.Z : Finset V)} :=
    reachedFourSetEquiv G C q hqQ hZCard eZ
  have he0 : L.e 0 = q := by simp [L, labelsFromEquivs, e]
  have hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1 := by
    intro i
    change reachedExternalFour G C q (fun z => (eZ z).1) ⟨i.val, by omega⟩ =
      (reachedFourSetEquiv G C q hqQ hZCard eZ i).1
    rw [reachedFourSetEquiv_val]
  have hZLab : ∀ i : Fin 3, L.e ⟨i.val + 1, by omega⟩ = (eZ i).1 := by
    intro i
    simp [L, labelsFromEquivs, e]
  have heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s} := by
    intro i
    by_cases hi : i.val < 3
    · let j : Fin 3 := ⟨i.val, hi⟩
      have hij : (⟨i.val + 1, by omega⟩ : Fin 5) =
          ⟨j.val + 1, by omega⟩ := Fin.ext (by rfl)
      rw [hij, hZLab j]
      exact Finset.mem_union_left {C.s} (eZ j).2
    · have hi3 : i.val = 3 := by omega
      have ieq : i = (3 : Fin 4) := Fin.ext hi3
      subst i
      change L.e 4 ∈ C.Z ∪ {C.s}
      have hlast : L.e 4 = C.s := by simp [L, labelsFromEquivs, e]
      rw [hlast]
      simp
  have heInj : Function.Injective L.e := by
    change Function.Injective e
    exact reachedExternalFour_injective G C q hqQ eZ
  have hLabelOne : (L.a 1).1 = u := by
    have h := labelsFromEquivs_aOne G C q hPCard hACard hRCard hHCard
      eA1 eX e (0 : Fin 2)
    calc
      (L.a 1).1 = (eA1 0).1 := by simpa [L] using h
      _ = u := by simp [eA1, finsetEquivAtZero]
  have hZero : directCount G C.A1 (L.a 1).1 = 0 := by
    simpa [hLabelOne] using huZero
  have hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x := by
    intro x hxMem
    simpa [hLabelOne] using huX x hxMem
  let c := edgeCount G C.A1 {q}
  have hc : edgeCount G C.A1 {q} = c := rfl
  have hPack := reachedFour_package_of_labels G C q hqQ hQ L hG hMin
    hNoSeymour hNoRoot hPivot hk hr hx hHCard hRCard hy hZCard
    ({q} ∪ C.Z) rfl eEq
    hELab he0 eZ hZLab heZ heInj hZero hX c hc
  have hcLe : c ≤ 2 := by
    dsimp [c]
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with hc0 | hc1 | hc2
  · have hLower := H_to_P_lower G C q hqQ hQ hG hMin hk hx hRCard
    have hUpper := H_to_P_add_missing_four_le G C q hQ hG hMin hr
      hNoRoot hHCard hZCard
    dsimp [c] at hc0
    omega
  · rw [hc1] at hPack
    rw [microFourDistinguished_one_unsat] at hPack
    contradiction
  · rw [hc2] at hPack
    rw [microFourDistinguished_two_unsat] at hPack
    contradiction

set_option linter.flexible false in
/-- Package all graph facts used by both the high- and low-PH width-five
certificates.  The special `A₁` row is assumed to occupy label zero. -/
theorem reachedFive_package_of_labels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hNoRoot : epsilonS G C = 0)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (hy : BSevenKTwo.y G C = 1) (hZCard : C.Z.card = 4)
    (E : Finset V) (hE : E = {q} ∪ C.Z)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (he0 : L.e 0 = q)
    (eZ : Fin 4 ≃ {v : V // v ∈ C.Z})
    (hZLab : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ = (eZ i).1)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (hZero : directCount G C.A1 (L.a 1).1 = 0)
    (hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x)
    (c : Nat) (hc : edgeCount G C.A1 {q} = c) :
    let bits := Encoding.coreBits G.Adj L
    reachedEffectiveHybrid c bits = true ∧ distinguishedAOne bits = true := by
  dsimp
  let bits := Encoding.coreBits G.Adj L
  have heInj : Function.Injective L.e := by
    intro i j hij
    apply eEq.injective
    apply Subtype.ext
    simpa [hELab] using hij
  have hOrP := orientedP_true G C q L hG
  have hOrPH := orientedPH_true G C q L hG
  have hOrHH := orientedHH_true G C q L hG
  have hAMin0 := aOneMinimum_true G C q hqQ hQ L hG hPivot hHCard hk hr
  have hAMin : all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
      (!(count 4 (hArc bits a) == 2) ||
        (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) = true := by
    simpa [bits, hToQCore] using hAMin0
  have hHMin0 := hMinimum_true G C q hqQ hQ L hG hMin hHCard hRCard
  have hHMin : all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) = true := by
    simpa [bits, hDirectCore, hToQCore] using hHMin0
  have hXR := everyXReached_true G C q L hk
  have hQR := qStructureReached_true G C q hqQ hQ L he0 hy c hc
  have hZR := labelledZReached_true (zCount := 4) (offset := 1)
    G C q L eZ (by omega) (by simpa [Nat.add_comm] using hZLab)
  have hPMin := pMinimumDegreeReached_true G C q hqQ hQ L hG hHCard
    hMin hNoRoot E hE eEq (by omega) hELab
  have hHNS := all_hRestrictedNonSeymourCore_true G C q hqQ hQ L hG
    hNoSeymour hHCard hRCard he0 heZ heInj c
  have hPNS := all_pMicroNonSeymourCore_true G C q hqQ hQ L hG
    hNoSeymour hHCard hNoRoot E hE eEq hELab he0 heZ c
  have hDist := distinguishedAOne_true G C q L hG hZero hX
  have hcLe : c ≤ 2 := by
    rw [← hc]
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  have hAOneNat := aOneToQ_toNat G C q L (aOneEquiv G C q L hk)
    (fun i => aOneEquiv_val G C q L hk i)
  have hCEq : aOneToQ bits = BitVec.ofNat 8 c := by
    apply BitVec.eq_of_toNat_eq
    rw [show (aOneToQ bits).toNat = edgeCount G C.A1 {q} by
      simpa [bits] using hAOneNat, hc]
    simp [BitVec.toNat_ofNat]
    omega
  have hHPLowerGraph := H_to_P_lower G C q hqQ hQ hG hMin hk hx hRCard
  have hHPUpperGraph := H_to_P_add_missing_le G C q hQ hG hMin hr
    hNoRoot hHCard hZCard
  have hLower : (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using totalHToP_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    have hlt : 16 - c < 256 := by omega
    rw [Nat.mod_eq_of_lt hlt, ← hc]
    exact hHPLowerGraph
  have hMNat := externalMissingFive_toNat G C q L hG hHCard E eEq hELab
  have hUpper : (totalHToP bits + externalMissing 5 bits).ule 21 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using totalHToP_toNat G C q L hHCard,
      show (externalMissing 5 bits).toNat = 30 - edgeCount G C.P E by
        simpa [bits] using hMNat]
    norm_num [BitVec.toNat_ofNat]
    have hSmall : edgeCount G C.H C.P + (30 - edgeCount G C.P E) < 256 := by
      omega
    rw [Nat.mod_eq_of_lt hSmall]
    simpa [hE] using hHPUpperGraph
  have hmBound : 30 - edgeCount G C.P E ≤ 7 := by
    rw [hE]
    omega
  have hEff := pEffectiveConditionFive_true G C q hqQ hQ L hG hMin
    hNoSeymour hNoRoot hHCard hy E hE eEq hELab hmBound
  have hSharp := sharpKing_of_orientedP bits (by simpa [bits] using hOrP)
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := hr
  have hPHGraph : edgeCount G C.P C.H ≤ 8 + c := by
    rw [hPCard, hHCard] at hCross
    omega
  have hPH : (totalPToH bits).ule (BitVec.ofNat 8 (8 + c)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalPToH bits).toNat = edgeCount G C.P C.H by
      simpa [bits] using totalPToH_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    have hlt : 8 + c < 256 := by omega
    simpa [Nat.mod_eq_of_lt hlt] using hPHGraph
  have hCore : microCore c bits = true := by
    simp only [microCore, Bool.and_eq_true]
    aesop
  have hHybrid : reachedEffectiveHybrid c bits = true := by
    simp only [reachedEffectiveHybrid, Bool.and_eq_true]
    aesop
  exact ⟨hHybrid, by simpa [bits] using hDist⟩

/-- Degree accounting on `P` forces each missing external arc to be paid for
above the baseline of three arcs from `P` to `H`. -/
theorem externalMissing_add_three_le_ph (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoRoot : epsilonS G C = 0) (hr : C.r = 6)
    (hZCard : C.Z.card = 4) :
    30 - edgeCount G C.P ({q} ∪ C.Z) + 3 ≤ edgeCount G C.P C.H := by
  have hPCard : C.P.card = 6 := hr
  have hDegreeLower : 48 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      48 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hInternal := internal_edgeCount_le_choose_two G C.P hG
  rw [hPCard] at hInternal
  norm_num [Nat.choose] at hInternal
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExternal : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hDis : Disjoint {q} C.Z := by
    rw [Finset.disjoint_left]
    intro v hvq hvz
    exact q_not_mem_Z G C q hqQ (Finset.mem_singleton.mp hvq ▸ hvz)
  have hPE : edgeCount G C.P ({q} ∪ C.Z) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint G C.P {q} C.Z hDis, ← hQ, ← hExternal]
  have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
  have hUnionCard : ({q} ∪ C.Z).card = 5 := by
    rw [Finset.card_union_of_disjoint hDis]
    simp [hZCard]
  have hPECap := edgeCount_le_card_mul_card G C.P ({q} ∪ C.Z)
  rw [hPCard, hUnionCard] at hPECap
  omega

/-- In the `c=2`, `P→H≤6` leaf, degree accounting forces at least
27 of the 30 possible arcs from `P` to `{q}∪Z`. -/
theorem externalMissing_le_three_of_ph_le_six (C : G.LocalConfiguration)
    (q : V) (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoRoot : epsilonS G C = 0) (hr : C.r = 6)
    (hZCard : C.Z.card = 4)
    (hPH : edgeCount G C.P C.H ≤ 6) :
    30 - edgeCount G C.P ({q} ∪ C.Z) ≤ 3 := by
  have hMissing := externalMissing_add_three_le_ph G C q hqQ hQ hG hMin
    hNoRoot hr hZCard
  omega

private theorem phUle_of_toNat (bits : Encoding) (ph bound : Nat)
    (hPHNat : (totalPToH bits).toNat = ph) (hbound : bound < 256)
    (h : ph ≤ bound) :
    (totalPToH bits).ule (BitVec.ofNat 8 bound) = true := by
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hPHNat]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound, h]

private theorem phLower_of_toNat (bits : Encoding) (ph bound : Nat)
    (hPHNat : (totalPToH bits).toNat = ph) (hbound : bound < 256)
    (h : bound ≤ ph) :
    (BitVec.ofNat 8 bound).ule (totalPToH bits) = true := by
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hPHNat]
  simp [BitVec.toNat_ofNat]
  simpa [Nat.mod_eq_of_lt hbound] using h

private theorem lowDist_of_encoded (c bound : Nat) (bits : Encoding)
    (hHybrid : reachedEffectiveHybrid c bits = true)
    (hDist : distinguishedAOne bits = true)
    (ph : Nat) (hPHNat : (totalPToH bits).toNat = ph)
    (hbound : bound < 256) (hPH : ph ≤ bound) :
    reachedEffectiveLowPHDistinguished c bound bits = true := by
  rw [reachedEffectiveLowPHDistinguished, Bool.and_eq_true]
  constructor
  · rw [reachedEffectiveLowPH, Bool.and_eq_true]
    exact ⟨hHybrid, phUle_of_toNat bits ph bound hPHNat hbound hPH⟩
  · exact hDist

private theorem externalMissing_eq_of_toNat (bits : Encoding) (m : Nat)
    (hMNat : (externalMissing 5 bits).toNat = m) (hm : m < 256) :
    externalMissing 5 bits = BitVec.ofNat 8 m := by
  apply BitVec.eq_of_toNat_eq
  rw [hMNat]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]

theorem encoded_c_zero_false
    (high : ∀ bits, microCZeroNonHard bits = false)
    (low : ∀ bits, microHEffectiveLowPHMissing 0 3 0 bits = false)
    (bits : Encoding) (ph m : Nat)
    (hHybrid : reachedEffectiveHybrid 0 bits = true)
    (hDist : distinguishedAOne bits = true)
    (hPHNat : (totalPToH bits).toNat = ph)
    (hPHUpper : ph ≤ 8) (hmBase : m + 3 ≤ ph)
    (hMNat : (externalMissing 5 bits).toNat = m) : False := by
  have hCore : microCore 0 bits = true := by
    simp only [reachedEffectiveHybrid, Bool.and_eq_true] at hHybrid
    aesop
  by_cases hph : 4 ≤ ph
  · have hHigh : microCZeroNonHard bits = true := by
      simp only [microCZeroNonHard, Bool.and_eq_true]
      exact ⟨⟨hCore, phLower_of_toNat bits ph 4 hPHNat (by omega) hph⟩,
        phUle_of_toNat bits ph 8 hPHNat (by omega) hPHUpper⟩
    rw [high bits] at hHigh
    exact Bool.false_ne_true hHigh
  · have hLow := lowDist_of_encoded 0 3 bits hHybrid hDist ph hPHNat (by omega)
      (by omega)
    have hMicro := reachedEffectiveLowPHDistinguished_implies_microH 0 3 bits hLow
    have hm0 : m = 0 := by omega
    have hMEq := externalMissing_eq_of_toNat bits m hMNat (by omega)
    have hMissing := microHEffectiveLowPH_to_missing 0 3 m bits hMicro hMEq
    rw [hm0, low bits] at hMissing
    exact Bool.false_ne_true hMissing

theorem encoded_c_one_false
    (high : ∀ bits, microCOneHighPH bits = false)
    (low : ∀ m bits,
      microHEffectiveLowPHSelectedMissing 1 5 2 m bits = false)
    (bits : Encoding) (ph m : Nat)
    (hHybrid : reachedEffectiveHybrid 1 bits = true)
    (hDist : distinguishedAOne bits = true)
    (hPHNat : (totalPToH bits).toNat = ph)
    (hPHUpper : ph ≤ 9) (hmBase : m + 3 ≤ ph)
    (hMNat : (externalMissing 5 bits).toNat = m) : False := by
  have hCore : microCore 1 bits = true := by
    simp only [reachedEffectiveHybrid, Bool.and_eq_true] at hHybrid
    aesop
  by_cases hph : 6 ≤ ph
  · have hHigh : microCOneHighPH bits = true := by
      simp only [microCOneHighPH, Bool.and_eq_true]
      exact ⟨⟨hCore, phLower_of_toNat bits ph 6 hPHNat (by omega) hph⟩,
        phUle_of_toNat bits ph 9 hPHNat (by omega) hPHUpper⟩
    rw [high bits] at hHigh
    exact Bool.false_ne_true hHigh
  · have hLow := lowDist_of_encoded 1 5 bits hHybrid hDist ph hPHNat (by omega)
      (by omega)
    have hMicro := reachedEffectiveLowPHDistinguished_implies_microH 1 5 bits hLow
    have hmLe : m ≤ 2 := by omega
    have hMEq := externalMissing_eq_of_toNat bits m hMNat (by omega)
    have hMissing := microHEffectiveLowPH_to_missing 1 5 m bits hMicro hMEq
    have hSelected := microHEffectiveLowPHMissing_to_selected
      1 5 2 m bits hmLe (by omega) hMissing
    rw [low (BitVec.ofNat 2 m) bits] at hSelected
    exact Bool.false_ne_true hSelected

theorem encoded_c_two_false
    (high : ∀ bits, microCTwoHighPH bits = false)
    (low : ∀ m bits,
      microHEffectiveLowPHSelectedMissing 2 6 3 m bits = false)
    (bits : Encoding) (ph m : Nat)
    (hHybrid : reachedEffectiveHybrid 2 bits = true)
    (hDist : distinguishedAOne bits = true)
    (hPHNat : (totalPToH bits).toNat = ph)
    (hPHUpper : ph ≤ 10) (hmBase : m + 3 ≤ ph)
    (hMNat : (externalMissing 5 bits).toNat = m) : False := by
  have hCore : microCore 2 bits = true := by
    simp only [reachedEffectiveHybrid, Bool.and_eq_true] at hHybrid
    aesop
  by_cases hph : 7 ≤ ph
  · have hHigh : microCTwoHighPH bits = true := by
      simp only [microCTwoHighPH, Bool.and_eq_true]
      exact ⟨⟨hCore, phLower_of_toNat bits ph 7 hPHNat (by omega) hph⟩,
        phUle_of_toNat bits ph 10 hPHNat (by omega) hPHUpper⟩
    rw [high bits] at hHigh
    exact Bool.false_ne_true hHigh
  · have hLow := lowDist_of_encoded 2 6 bits hHybrid hDist ph hPHNat (by omega)
      (by omega)
    have hMicro := reachedEffectiveLowPHDistinguished_implies_microH 2 6 bits hLow
    have hmLe : m ≤ 3 := by omega
    have hMEq := externalMissing_eq_of_toNat bits m hMNat (by omega)
    have hMissing := microHEffectiveLowPH_to_missing 2 6 m bits hMicro hMEq
    have hSelected := microHEffectiveLowPHMissing_to_selected
      2 6 3 m bits hmLe (by omega) hMissing
    rw [low (BitVec.ofNat 2 m) bits] at hSelected
    exact Bool.false_ne_true hSelected

set_option maxHeartbeats 512000000 in
/-- End-to-end width-five bridge, parameterized by the certificate theorems. -/
theorem reachedFive_impossible_of_certificates
    (high0 : ∀ bits, microCZeroNonHard bits = false)
    (high1 : ∀ bits, microCOneHighPH bits = false)
    (high2 : ∀ bits, microCTwoHighPH bits = false)
    (low0 : ∀ bits, microHEffectiveLowPHMissing 0 3 0 bits = false)
    (low1 : ∀ m bits,
      microHEffectiveLowPHSelectedMissing 1 5 2 m bits = false)
    (low2 : ∀ m bits,
      microHEffectiveLowPHSelectedMissing 2 6 3 m bits = false)
    (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hNoRoot : epsilonS G C = 0)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (hy : BSevenKTwo.y G C = 1) (hZCard : C.Z.card = 4) : False := by
  obtain ⟨u, huAOne, huA, huZero, huX⟩ :=
    exists_distinguished_aOne G C hG hPivot hk hx
  let eA1 : Fin 2 ≃ {v : V // v ∈ C.A1} :=
    finsetEquivAtZero C.A1 (by omega) (by exact hk) u huAOne
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X (by exact hx)
  let eZ : Fin 4 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let e : Fin 5 → V := reachedExternalFive q (fun i => (eZ i).1)
  let L : ReachedLabels G C q :=
    labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e
  let eEq : Fin 5 ≃ {v : V // v ∈ ({q} ∪ C.Z : Finset V)} :=
    reachedFiveSetEquiv G C q hqQ hZCard eZ
  have he0 : L.e 0 = q := by simp [L, labelsFromEquivs, e]
  have hELab : ∀ i : Fin 5, L.e i = (eEq i).1 := by
    intro i
    change reachedExternalFive q (fun z => (eZ z).1) i =
      (reachedFiveSetEquiv G C q hqQ hZCard eZ i).1
    rw [reachedFiveSetEquiv_val]
  have hZLab : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ = (eZ i).1 := by
    intro i
    simp [L, labelsFromEquivs, e]
  have heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s} := by
    intro i
    rw [hZLab i]
    exact Finset.mem_union_left {C.s} (eZ i).2
  have hLabelOne : (L.a 1).1 = u := by
    have h := labelsFromEquivs_aOne G C q hPCard hACard hRCard hHCard
      eA1 eX e (0 : Fin 2)
    calc
      (L.a 1).1 = (eA1 0).1 := by simpa [L] using h
      _ = u := by simp [eA1, finsetEquivAtZero]
  have hZero : directCount G C.A1 (L.a 1).1 = 0 := by
    simpa [hLabelOne] using huZero
  have hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x := by
    intro x hxMem
    simpa [hLabelOne] using huX x hxMem
  let bits := Encoding.coreBits G.Adj L
  let c := edgeCount G C.A1 {q}
  have hPack := reachedFive_package_of_labels G C q hqQ hQ L hG hMin
    hNoSeymour hNoRoot hPivot hk hr hx hHCard hRCard hy hZCard
    ({q} ∪ C.Z) rfl eEq hELab he0 eZ hZLab heZ hZero hX c rfl
  have hHybrid : reachedEffectiveHybrid c bits = true := by
    simpa [bits] using hPack.1
  have hDist : distinguishedAOne bits = true := by simpa [bits] using hPack.2
  have hcLe : c ≤ 2 := by
    dsimp [c]
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  let ph := edgeCount G C.P C.H
  have hPHNat : (totalPToH bits).toNat = ph := by
    simpa [bits, ph] using totalPToH_toNat G C q L hHCard
  have hPHUpper : ph ≤ 8 + c := by
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    have hLower := H_to_P_lower G C q hqQ hQ hG hMin hk hx hRCard
    rw [hPCard, hHCard] at hCross
    dsimp [c, ph]
    omega
  let m := 30 - edgeCount G C.P ({q} ∪ C.Z)
  have hmBase : m + 3 ≤ ph := by
    dsimp [m, ph]
    exact externalMissing_add_three_le_ph G C q hqQ hQ hG hMin hNoRoot hr hZCard
  have hMNatRaw := externalMissingFive_toNat G C q L hG hHCard
    ({q} ∪ C.Z) eEq hELab
  have hMNat : (externalMissing 5 bits).toNat = m := by
    simpa [bits, m] using hMNatRaw
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with hc0 | hc1 | hc2
  · exact encoded_c_zero_false high0 low0 bits ph m
      (by simpa [hc0] using hHybrid) hDist hPHNat
      (by simpa [hc0] using hPHUpper) hmBase hMNat
  · exact encoded_c_one_false high1 low1 bits ph m
      (by simpa [hc1] using hHybrid) hDist hPHNat
      (by simpa [hc1] using hPHUpper) hmBase hMNat
  · exact encoded_c_two_false high2 low2 bits ph m
      (by simpa [hc2] using hHybrid) hDist hPHNat
      (by simpa [hc2] using hPHUpper) hmBase hMNat

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.ReachedAssembly
