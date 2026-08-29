import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.MicroBridge
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.ReachedAssembly
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.SharpKing
import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.LocalFour

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoRoot.ReachedAssembly

open Shared Shared.FiniteCore
open RSix.XTwoNoRoot
open Labels Encoding Core
open XTwoNoRoot.GraphBridge
open XTwoRoot.GraphBridge XTwoRoot.MicroBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def consExternal {n : Nat} (q : V) (z : Fin n → V) : Fin (n + 1) → V := fun i =>
  if hi : i.val = 0 then q else z ⟨i.val - 1, by omega⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consExternal_zero {n : Nat} (q : V) (z : Fin n → V) :
    consExternal q z 0 = q := by
  classical
  simp [consExternal]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consExternal_succ {n : Nat} (q : V) (z : Fin n → V)
    (i : Fin n) : consExternal q z ⟨i.val + 1, by omega⟩ = z i := by
  classical
  simp [consExternal]

omit [Fintype V] [DecidableEq V] in
theorem consExternal_injective {n : Nat} (q : V) (S : Finset V)
    (hq : q ∉ S) (z : Fin n ≃ {v : V // v ∈ S}) :
    Function.Injective (consExternal q (fun i => (z i).1)) := by
  classical
  intro i j hij
  apply Fin.ext
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    by_cases hj0 : j.val = 0
    · omega
    · let k : Fin n := ⟨j.val - 1, by omega⟩
      have hij' : q = (z k).1 := by
        simpa [consExternal, hj0, k] using hij
      have : q ∈ S := by rw [hij']; exact (z k).2
      exact (hq this).elim
  · by_cases hj0 : j.val = 0
    · let k : Fin n := ⟨i.val - 1, by omega⟩
      have hj : j = 0 := Fin.ext hj0
      subst j
      have hij' : (z k).1 = q := by
        simpa [consExternal, hi0, k] using hij
      have : q ∈ S := by rw [← hij']; exact (z k).2
      exact (hq this).elim
    · let ki : Fin n := ⟨i.val - 1, by omega⟩
      let kj : Fin n := ⟨j.val - 1, by omega⟩
      have hij' : (z ki).1 = (z kj).1 := by
        simpa [consExternal, hi0, hj0, ki, kj] using hij
      have hk : ki = kj := z.injective (Subtype.ext hij')
      have hval := congrArg Fin.val hk
      dsimp [ki, kj] at hval
      omega

def consExternalWithDummy (q : V) (z : Fin 3 → V) (dummy : V) : Fin 5 → V :=
  fun i => if hi : i.val < 4
    then consExternal q z ⟨i.val, hi⟩
    else dummy

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consExternalWithDummy_zero (q : V) (z : Fin 3 → V) (dummy : V) :
    consExternalWithDummy q z dummy 0 = q := by
  classical
  simp [consExternalWithDummy]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consExternalWithDummy_succ (q : V) (z : Fin 3 → V) (dummy : V)
    (i : Fin 3) : consExternalWithDummy q z dummy ⟨i.val + 1, by omega⟩ = z i := by
  classical
  simp [consExternalWithDummy]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem consExternalWithDummy_last (q : V) (z : Fin 3 → V) (dummy : V) :
    consExternalWithDummy q z dummy 4 = dummy := by
  classical
  simp [consExternalWithDummy]

private theorem external_mem_Z_or_s (C : G.LocalConfiguration) (v : V)
    (hv : v ∈ externalTargets G C) : v ∈ C.Z ∪ {C.s} := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · exact Finset.mem_union_left {C.s} hvZ
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvEq : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      simp
    · simp [rootSecondFinset, hReach] at hvRoot

private theorem totalPToEFour_sub_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hHCard : C.H.card = 4) (E : Finset V)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1) :
    (24 - totalPToE 4 (Encoding.coreBits G.Adj L)).toNat =
      24 - edgeCount G C.P E := by
  rw [BitVec.toNat_sub,
    XTwoNoRoot.GraphBridge.totalPToE_toNat G C q L hG hHCard E eEq
      (by omega) hELab]
  have hCap := edgeCount_le_card_mul_card G C.P E
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have he : E.card = 4 := by simpa using (Fintype.card_congr eEq).symm
  rw [hp, he] at hCap
  norm_num [BitVec.toNat_ofNat]
  change (256 - edgeCount G C.P E + 24) % 256 = _
  have heq : 256 - edgeCount G C.P E + 24 =
      256 + (24 - edgeCount G C.P E) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  have hlt : 24 - edgeCount G C.P E < 256 := by omega
  simp [Nat.mod_eq_of_lt hlt]

private theorem externalMissingFive_toNat (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented)
    (hHCard : C.H.card = 4) (E : Finset V)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1) :
    (externalMissing 5 (Encoding.coreBits G.Adj L)).toNat =
      30 - edgeCount G C.P E := by
  rw [externalMissing, BitVec.toNat_sub,
    XTwoNoRoot.GraphBridge.totalPToE_toNat G C q L hG hHCard E eEq
      (by omega) hELab]
  have hCap := edgeCount_le_card_mul_card G C.P E
  have hp : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
  have he : E.card = 5 := by simpa using (Fintype.card_congr eEq).symm
  rw [hp, he] at hCap
  norm_num [BitVec.toNat_ofNat]
  change (256 - edgeCount G C.P E + 30) % 256 = _
  have heq : 256 - edgeCount G C.P E + 30 =
      256 + (30 - edgeCount G C.P E) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  have hlt : 30 - edgeCount G C.P E < 256 := by omega
  simp [Nat.mod_eq_of_lt hlt]

set_option linter.flexible false in
theorem reachedFour_package_of_labels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (hy : BSevenKTwo.y G C = 1)
    (hExternalCard : (externalTargets G C).card = 3)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (he0 : L.e 0 = q)
    (eExternal : Fin 3 ≃ {v : V // v ∈ externalTargets G C})
    (hExternalLab : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ = (eExternal i).1)
    (hDummy : L.e 4 = (L.a 5).1)
    (hZero : directCount G C.A1 (L.a 1).1 = 0)
    (hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x)
    (c : Nat) (hc : edgeCount G C.A1 {q} = c) :
    microFourDistinguished c (Encoding.coreBits G.Adj L) = true := by
  let bits := Encoding.coreBits G.Adj L
  have hOrP := XTwoNoRoot.GraphBridge.orientedP_true G C q L hG
  have hOrPH := XTwoNoRoot.GraphBridge.orientedPH_true G C q L hG
  have hOrHH := XTwoNoRoot.GraphBridge.orientedHH_true G C q L hG
  have hAMin0 := XTwoNoRoot.GraphBridge.aOneMinimum_true
    G C q hqQ hQ L hG hPivot hHCard hk hr
  have hAMin : all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
      (!(count 4 (hArc bits a) == 2) ||
        (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) = true := by
    simpa [bits, hToQCore] using hAMin0
  have hHMin0 := XTwoNoRoot.GraphBridge.hMinimum_true
    G C q hqQ hQ L hG hMin hHCard hRCard
  have hHMin : all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) = true := by
    simpa [bits, hDirectCore, hToQCore] using hHMin0
  have hXR := XTwoNoRoot.GraphBridge.everyXReached_true G C q L hk
  have hQR := XTwoNoRoot.GraphBridge.qStructureReached_true
    G C q hqQ hQ L he0 hy c hc
  have heExt : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ ∈ externalTargets G C := by
    intro i
    rw [hExternalLab i]
    exact (eExternal i).2
  have hZR := labelledExternalReached_true (zCount := 3) (offset := 1)
    G C q L eExternal (by omega) (by simpa [Nat.add_comm] using hExternalLab)
  have hPMin := XTwoRoot.GraphBridge.pMinimumDegreeReached_true
    G C q hqQ hQ L hG hHCard hMin E hE eEq (by omega) hELab
  have hHNS := XTwoRoot.MicroBridge.all_hRestrictedNonSeymourFour_true
    G C q hqQ hQ L hG hNoSeymour hHCard hRCard he0 heExt E hE eEq
      hELab hDummy c
  have hPNS := XTwoRoot.MicroBridge.all_pMicroNonSeymourFour_true
    G C q hqQ hQ L hG hNoSeymour hHCard E hE eEq hELab he0 heExt
      hDummy c
  have hDist := XTwoNoRoot.GraphBridge.distinguishedAOne_true G C q L hG hZero hX
  have hAOneNat := XTwoNoRoot.GraphBridge.aOneToQ_toNat
    G C q L (XTwoNoRoot.GraphBridge.aOneEquiv G C q L hk)
      (fun i => XTwoNoRoot.GraphBridge.aOneEquiv_val G C q L hk i)
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
  have hHPLowerGraph := XTwoNoRoot.GraphBridge.H_to_P_lower
    G C q hqQ hQ hG hMin hk hx hRCard
  have hHPUpperGraph := XTwoRoot.GraphBridge.H_to_P_add_missing_four_le
    G C q hqQ hQ hG hMin hr hHCard hExternalCard
  have hLower : (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using XTwoNoRoot.GraphBridge.totalHToP_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 16 - c < 256), ← hc]
    exact hHPLowerGraph
  have hUpper : (totalHToP bits + (24 - totalPToE 4 bits)).ule 15 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using XTwoNoRoot.GraphBridge.totalHToP_toNat G C q L hHCard,
      show (24 - totalPToE 4 bits).toNat = 24 - edgeCount G C.P E by
        simpa [bits] using totalPToEFour_sub_toNat G C q L hG hHCard E eEq hELab]
    norm_num [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    simpa [hE] using hHPUpperGraph
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := hr
  have hPHGraph : edgeCount G C.P C.H ≤ 8 + c := by
    rw [hPCard, hHCard] at hCross
    omega
  have hPH : (totalPToH bits).ule (BitVec.ofNat 8 (8 + c)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalPToH bits).toNat = edgeCount G C.P C.H by
      simpa [bits] using XTwoNoRoot.GraphBridge.totalPToH_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    simpa [Nat.mod_eq_of_lt (by omega : 8 + c < 256)] using hPHGraph
  have hCore : microFour c bits = true := by
    simp only [microFour, Bool.and_eq_true]
    aesop
  rw [microFourDistinguished, Bool.and_eq_true]
  exact ⟨hCore, by simpa [bits] using hDist⟩

/-- End-to-end contradiction when the reached-root row has only four genuine
external columns.  A vertex of `R` fills the certificate's unused fifth slot;
all `P → R` bits in that slot are forced false. -/
theorem reachedFour_impossible (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q})
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (hy : BSevenKTwo.y G C = 1)
    (hExternalCard : (externalTargets G C).card = 3) : False := by
  obtain ⟨u, huAOne, huA, huZero, huX⟩ :=
    XTwoNoRoot.GraphBridge.exists_distinguished_aOne G C hG hPivot hk hx
  let eA1 : Fin 2 ≃ {v : V // v ∈ C.A1} :=
    Labels.finsetEquivAtZero C.A1 (by omega) (by exact hk) u huAOne
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X (by exact hx)
  let eExternal : Fin 3 ≃ {v : V // v ∈ externalTargets G C} :=
    finsetEquivFin (externalTargets G C) hExternalCard
  have hDis := XTwoRoot.GraphBridge.q_disjoint_externalTargets G C q hqQ
  have hqNot : q ∉ externalTargets G C := by
    intro hqExt
    exact (Finset.disjoint_left.mp hDis) (by simp) hqExt
  let E : Finset V := {q} ∪ externalTargets G C
  have hECard : E.card = 4 := by
    simpa [E, hExternalCard] using Finset.card_insert_of_notMem hqNot
  let f : Fin 4 → V := consExternal q (fun i => (eExternal i).1)
  have hfMem : ∀ i, f i ∈ E := by
    intro i
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simp [f, E]
    · let j : Fin 3 := ⟨i.val - 1, by omega⟩
      have hij : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      rw [hij]
      simp [f, E, eExternal]
  have hfInj : Function.Injective f := by
    exact consExternal_injective q (externalTargets G C) hqNot eExternal
  let eEq : Fin 4 ≃ {v : V // v ∈ E} :=
    Labels.finEquivSubtypeOfInjective E f hfMem hfInj hECard
  let dummy : V := (finsetEquivFin C.R hRCard (0 : Fin 3)).1
  let e : Fin 5 → V :=
    consExternalWithDummy q (fun i => (eExternal i).1) dummy
  let L : ReachedLabels G C q :=
    Labels.labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e
  have he0 : L.e 0 = q := by simp [L, Labels.labelsFromEquivs, e]
  have hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1 := by
    intro i
    change e ⟨i.val, by omega⟩ = (eEq i).1
    simp only [e, consExternalWithDummy, dif_pos i.isLt]
    change consExternal q (fun j => (eExternal j).1) i = _
    rw [Labels.finEquivSubtypeOfInjective_apply]
  have hExternalLab : ∀ i : Fin 3,
      L.e ⟨i.val + 1, by omega⟩ = (eExternal i).1 := by
    intro i
    simp [L, Labels.labelsFromEquivs, e]
  have hDummy : L.e 4 = (L.a 5).1 := by
    calc
      L.e 4 = dummy := by simp [L, Labels.labelsFromEquivs, e]
      _ = (finsetEquivFin C.R hRCard (0 : Fin 3)).1 := rfl
      _ = (L.a 5).1 := by
        symm
        simpa [L] using Labels.labelsFromEquivs_r G C q hPCard hACard
          hRCard hHCard eA1 eX e (0 : Fin 3)
  have hLabelOne : (L.a 1).1 = u := by
    have h := Labels.labelsFromEquivs_aOne G C q hPCard hACard hRCard hHCard
      eA1 eX e (0 : Fin 2)
    calc
      (L.a 1).1 = (eA1 0).1 := by simpa [L] using h
      _ = u := by simp [eA1, Labels.finsetEquivAtZero]
  have hZero : directCount G C.A1 (L.a 1).1 = 0 := by
    simpa [hLabelOne] using huZero
  have hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x := by
    intro x hxMem
    simpa [hLabelOne] using huX x hxMem
  let c := edgeCount G C.A1 {q}
  have hPack := reachedFour_package_of_labels G C q hqQ hQ L hG hMin
    hNoSeymour hPivot hk hr hx hHCard hRCard hy hExternalCard E rfl eEq
    hELab he0 eExternal hExternalLab hDummy hZero hX c rfl
  have hcLe : c ≤ 2 := by
    dsimp [c]
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with hc0 | hc1 | hc2
  · have hLower := XTwoNoRoot.GraphBridge.H_to_P_lower
      G C q hqQ hQ hG hMin hk hx hRCard
    have hUpper := XTwoRoot.GraphBridge.H_to_P_add_missing_four_le
      G C q hqQ hQ hG hMin hr hHCard hExternalCard
    dsimp [c] at hc0
    omega
  · rw [hc1] at hPack
    rw [microFourDistinguished_one_unsat] at hPack
    contradiction
  · rw [hc2] at hPack
    rw [microFourDistinguished_two_unsat] at hPack
    contradiction

set_option linter.flexible false in
/-- The width-five Boolean package is unchanged from the no-root model after
replacing `Z` by the rooted external-target set. -/
theorem reachedFive_package_of_labels (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (hy : BSevenKTwo.y G C = 1)
    (hExternalCard : (externalTargets G C).card = 4)
    (E : Finset V) (hE : E = {q} ∪ externalTargets G C)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (he0 : L.e 0 = q)
    (eExternal : Fin 4 ≃ {v : V // v ∈ externalTargets G C})
    (hExternalLab : ∀ i : Fin 4,
      L.e ⟨i.val + 1, by omega⟩ = (eExternal i).1)
    (hZero : directCount G C.A1 (L.a 1).1 = 0)
    (hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x)
    (c : Nat) (hc : edgeCount G C.A1 {q} = c) :
    let bits := Encoding.coreBits G.Adj L
    reachedEffectiveHybrid c bits = true ∧ distinguishedAOne bits = true := by
  dsimp
  let bits := Encoding.coreBits G.Adj L
  have heExt : ∀ i : Fin 4,
      L.e ⟨i.val + 1, by omega⟩ ∈ externalTargets G C := by
    intro i
    rw [hExternalLab i]
    exact (eExternal i).2
  have heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s} :=
    fun i => external_mem_Z_or_s G C _ (heExt i)
  have heInj : Function.Injective L.e := by
    intro i j hij
    apply eEq.injective
    apply Subtype.ext
    simpa [hELab] using hij
  have hOrP := XTwoNoRoot.GraphBridge.orientedP_true G C q L hG
  have hOrPH := XTwoNoRoot.GraphBridge.orientedPH_true G C q L hG
  have hOrHH := XTwoNoRoot.GraphBridge.orientedHH_true G C q L hG
  have hAMin0 := XTwoNoRoot.GraphBridge.aOneMinimum_true
    G C q hqQ hQ L hG hPivot hHCard hk hr
  have hAMin : all 2 (fun a => (2 : BitVec 8).ule (count 4 (hArc bits a)) &&
      (!(count 4 (hArc bits a) == 2) ||
        (6 : BitVec 8).ule (hPOut bits a + bitCount (hToQCore c bits a)))) = true := by
    simpa [bits, hToQCore] using hAMin0
  have hHMin0 := XTwoNoRoot.GraphBridge.hMinimum_true
    G C q hqQ hQ L hG hMin hHCard hRCard
  have hHMin : all 4 (fun h => (8 : BitVec 8).ule (hDirectCore c bits h)) = true := by
    simpa [bits, hDirectCore, hToQCore] using hHMin0
  have hXR := XTwoNoRoot.GraphBridge.everyXReached_true G C q L hk
  have hQR := XTwoNoRoot.GraphBridge.qStructureReached_true
    G C q hqQ hQ L he0 hy c hc
  have hZR := labelledExternalReached_true (zCount := 4) (offset := 1)
    G C q L eExternal (by omega) (by simpa [Nat.add_comm] using hExternalLab)
  have hPMin := XTwoRoot.GraphBridge.pMinimumDegreeReached_true
    G C q hqQ hQ L hG hHCard hMin E hE eEq (by omega) hELab
  have hHNS := XTwoNoRoot.MicroScratch.all_hRestrictedNonSeymourCore_true
    G C q hqQ hQ L hG hNoSeymour hHCard hRCard he0 heZ heInj c
  have hPNS := XTwoRoot.MicroBridge.all_pMicroNonSeymourCore_true
    G C q hqQ hQ L hG hNoSeymour hHCard E hE eEq hELab he0 heZ c
  have hDist := XTwoNoRoot.GraphBridge.distinguishedAOne_true G C q L hG hZero hX
  have hcLe : c ≤ 2 := by
    rw [← hc]
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    change C.A1.card = 2 at hk
    simpa [hk] using h
  have hAOneNat := XTwoNoRoot.GraphBridge.aOneToQ_toNat
    G C q L (XTwoNoRoot.GraphBridge.aOneEquiv G C q L hk)
      (fun i => XTwoNoRoot.GraphBridge.aOneEquiv_val G C q L hk i)
  have hCEq : aOneToQ bits = BitVec.ofNat 8 c := by
    apply BitVec.eq_of_toNat_eq
    rw [show (aOneToQ bits).toNat = edgeCount G C.A1 {q} by
      simpa [bits] using hAOneNat, hc]
    simp [BitVec.toNat_ofNat]
    omega
  have hHPLowerGraph := XTwoNoRoot.GraphBridge.H_to_P_lower
    G C q hqQ hQ hG hMin hk hx hRCard
  have hHPUpperGraph := XTwoRoot.GraphBridge.H_to_P_add_missing_le
    G C q hqQ hQ hG hMin hr hHCard hExternalCard
  have hLower : (BitVec.ofNat 8 (16 - c)).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using XTwoNoRoot.GraphBridge.totalHToP_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 16 - c < 256), ← hc]
    exact hHPLowerGraph
  have hMNat := externalMissingFive_toNat G C q L hG hHCard E eEq hELab
  have hUpper : (totalHToP bits + externalMissing 5 bits).ule 21 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using XTwoNoRoot.GraphBridge.totalHToP_toNat G C q L hHCard,
      show (externalMissing 5 bits).toNat = 30 - edgeCount G C.P E by
        simpa [bits] using hMNat]
    norm_num [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    simpa [hE] using hHPUpperGraph
  have hmBound : 30 - edgeCount G C.P E ≤ 7 := by
    rw [hE]
    omega
  have hEff := XTwoRoot.GraphBridge.pEffectiveConditionFive_true
    G C q hqQ hQ L hG hMin hNoSeymour hHCard hy E hE eEq hELab hmBound
  have hSharp := sharpKing_of_orientedP bits (by simpa [bits] using hOrP)
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  have hPCard : C.P.card = 6 := hr
  have hPHGraph : edgeCount G C.P C.H ≤ 8 + c := by
    rw [hPCard, hHCard] at hCross
    omega
  have hPH : (totalPToH bits).ule (BitVec.ofNat 8 (8 + c)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalPToH bits).toNat = edgeCount G C.P C.H by
      simpa [bits] using XTwoNoRoot.GraphBridge.totalPToH_toNat G C q L hHCard]
    simp [BitVec.toNat_ofNat]
    simpa [Nat.mod_eq_of_lt (by omega : 8 + c < 256)] using hPHGraph
  have hCore : microCore c bits = true := by
    simp only [microCore, Bool.and_eq_true]
    aesop
  have hHybrid : reachedEffectiveHybrid c bits = true := by
    simp only [reachedEffectiveHybrid, Bool.and_eq_true]
    aesop
  exact ⟨hHybrid, by simpa [bits] using hDist⟩

set_option maxHeartbeats 512000000 in
/-- Reuse the completed no-root width-five certificates with rooted graph
bridges.  Only the graph interpretation changes. -/
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
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hRCard : C.R.card = 3) (hHCard : C.H.card = 4)
    (hy : BSevenKTwo.y G C = 1)
    (hExternalCard : (externalTargets G C).card = 4) : False := by
  obtain ⟨u, huAOne, huA, huZero, huX⟩ :=
    XTwoNoRoot.GraphBridge.exists_distinguished_aOne G C hG hPivot hk hx
  let eA1 : Fin 2 ≃ {v : V // v ∈ C.A1} :=
    Labels.finsetEquivAtZero C.A1 (by omega) (by exact hk) u huAOne
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X (by exact hx)
  let eExternal : Fin 4 ≃ {v : V // v ∈ externalTargets G C} :=
    finsetEquivFin (externalTargets G C) hExternalCard
  have hDis := XTwoRoot.GraphBridge.q_disjoint_externalTargets G C q hqQ
  have hqNot : q ∉ externalTargets G C := by
    intro hqExt
    exact (Finset.disjoint_left.mp hDis) (by simp) hqExt
  let E : Finset V := {q} ∪ externalTargets G C
  have hECard : E.card = 5 := by
    simpa [E, hExternalCard] using Finset.card_insert_of_notMem hqNot
  let e : Fin 5 → V := consExternal q (fun i => (eExternal i).1)
  have heMem : ∀ i, e i ∈ E := by
    intro i
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simp [e, E]
    · let j : Fin 4 := ⟨i.val - 1, by omega⟩
      have hij : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      rw [hij]
      simp [e, E, eExternal]
  have heInj : Function.Injective e := by
    exact consExternal_injective q (externalTargets G C) hqNot eExternal
  let eEq : Fin 5 ≃ {v : V // v ∈ E} :=
    Labels.finEquivSubtypeOfInjective E e heMem heInj hECard
  let L : ReachedLabels G C q :=
    Labels.labelsFromEquivs G C q hPCard hACard hRCard hHCard eA1 eX e
  have he0 : L.e 0 = q := by simp [L, Labels.labelsFromEquivs, e]
  have hELab : ∀ i : Fin 5, L.e i = (eEq i).1 := by
    intro i
    change e i = (eEq i).1
    rw [Labels.finEquivSubtypeOfInjective_apply]
  have hExternalLab : ∀ i : Fin 4,
      L.e ⟨i.val + 1, by omega⟩ = (eExternal i).1 := by
    intro i
    simp [L, Labels.labelsFromEquivs, e]
  have hLabelOne : (L.a 1).1 = u := by
    have h := Labels.labelsFromEquivs_aOne G C q hPCard hACard hRCard hHCard
      eA1 eX e (0 : Fin 2)
    calc
      (L.a 1).1 = (eA1 0).1 := by simpa [L] using h
      _ = u := by simp [eA1, Labels.finsetEquivAtZero]
  have hZero : directCount G C.A1 (L.a 1).1 = 0 := by
    simpa [hLabelOne] using huZero
  have hX : ∀ x ∈ C.X, G.Adj (L.a 1).1 x := by
    intro x hxMem
    simpa [hLabelOne] using huX x hxMem
  let bits := Encoding.coreBits G.Adj L
  let c := edgeCount G C.A1 {q}
  have hPack := reachedFive_package_of_labels G C q hqQ hQ L hG hMin
    hNoSeymour hPivot hk hr hx hHCard hRCard hy hExternalCard E rfl eEq
    hELab he0 eExternal hExternalLab hZero hX c rfl
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
    simpa [bits, ph] using XTwoNoRoot.GraphBridge.totalPToH_toNat G C q L hHCard
  have hPHUpper : ph ≤ 8 + c := by
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    have hLower := XTwoNoRoot.GraphBridge.H_to_P_lower
      G C q hqQ hQ hG hMin hk hx hRCard
    rw [hPCard, hHCard] at hCross
    dsimp [c, ph]
    omega
  let m := 30 - edgeCount G C.P ({q} ∪ externalTargets G C)
  have hmBase : m + 3 ≤ ph := by
    dsimp [m, ph]
    exact XTwoRoot.GraphBridge.externalMissing_add_three_le_ph
      G C q hqQ hQ hG hMin hr hExternalCard
  have hMNatRaw := externalMissingFive_toNat G C q L hG hHCard E eEq hELab
  have hMNat : (externalMissing 5 bits).toNat = m := by
    simpa [bits, m, E] using hMNatRaw
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with hc0 | hc1 | hc2
  · exact XTwoNoRoot.ReachedAssembly.encoded_c_zero_false high0 low0 bits ph m
      (by simpa [hc0] using hHybrid) hDist hPHNat
      (by simpa [hc0] using hPHUpper) hmBase hMNat
  · exact XTwoNoRoot.ReachedAssembly.encoded_c_one_false high1 low1
      bits ph m (by simpa [hc1] using hHybrid) hDist hPHNat
      (by simpa [hc1] using hPHUpper) hmBase hMNat
  · exact XTwoNoRoot.ReachedAssembly.encoded_c_two_false high2 low2
      bits ph m (by simpa [hc2] using hHybrid) hDist hPHNat
      (by simpa [hc2] using hPHUpper) hmBase hMNat

end SeymourEight.BSevenKTwo.RSix.XTwoRoot.ReachedAssembly
