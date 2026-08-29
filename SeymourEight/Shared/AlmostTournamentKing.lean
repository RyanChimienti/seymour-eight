import SeymourEight.Shared.ArcCounting
import Mathlib.Data.Finset.Powerset

set_option linter.style.header false

/-!
# Kings in almost-tournaments

This file contains a certificate-free version of the usual maximum-outdegree
proof that a tournament has a two-step king.  The quantitative form allows
missing unordered pairs: a suitable vertex reaches all but at most the number
of missing pairs in at most two steps.
-/

namespace SeymourEight.Shared

open CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [DecidableEq V] [DecidableRel G.Adj]

/-- If a finite family attains the sum of a pointwise lower bound, every term
attains that lower bound. -/
theorem pointwise_eq_of_sum_eq_card_mul {W : Type*}
    (S : Finset W) (f : W → Nat) (d : Nat)
    (hLower : ∀ v ∈ S, d ≤ f v)
    (hSum : ∑ v ∈ S, f v = S.card * d) :
    ∀ v ∈ S, f v = d := by
  classical
  intro v hv
  apply Nat.le_antisymm
  · by_contra hNot
    have hStrict : d < f v := by omega
    have hSumStrict : (∑ _w ∈ S, d) < ∑ w ∈ S, f w := by
      apply Finset.sum_lt_sum
      · exact hLower
      · exact ⟨v, hv, hStrict⟩
    simp [hSum] at hSumStrict
  · exact hLower v hv

/-- Unordered pairs in `S` carrying no arc in either direction. -/
def internalMissingPairs (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter fun e ↦
    ∀ u ∈ e, ∀ v ∈ e, u ≠ v → ¬G.Adj u v

/-- Vertices in `S`, other than `p`, reached from `p` in one or two internal steps. -/
def internalReachWithinTwo (S : Finset V) (p : V) : Finset V :=
  S.filter fun v ↦ v ≠ p ∧
    (G.Adj p v ∨ ∃ w ∈ S, G.Adj p w ∧ G.Adj w v)

/-- Internal reach in at most two steps splits into direct and strict second
neighbors. -/
theorem internalReachWithinTwo_eq_first_union_second (S : Finset V) (p : V)
    (hG : G.IsOriented) :
    internalReachWithinTwo G S p =
      internalFirstNeighbors G S p ∪ internalSecondNeighbors (G := G) S p := by
  ext v
  simp only [internalReachWithinTwo, internalFirstNeighbors,
    internalSecondNeighbors, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hvS, hvp, hpv | hTwo⟩
    · exact Or.inl ⟨hvS, hpv⟩
    · by_cases hpv : G.Adj p v
      · exact Or.inl ⟨hvS, hpv⟩
      · exact Or.inr ⟨hvS, hpv, hvp, hTwo⟩
  · rintro (⟨hvS, hpv⟩ | ⟨hvS, hpv, hvp, hTwo⟩)
    · exact ⟨hvS, fun hv ↦ hG.1 p (hv ▸ hpv), Or.inl hpv⟩
    · exact ⟨hvS, hvp, Or.inr hTwo⟩

/-- Cardinal form of the direct/strict-second decomposition. -/
theorem card_internalReachWithinTwo (S : Finset V) (p : V)
    (hG : G.IsOriented) :
    (internalReachWithinTwo G S p).card = directCount G S p +
      (internalSecondNeighbors (G := G) S p).card := by
  rw [internalReachWithinTwo_eq_first_union_second G S p hG,
    Finset.card_union_of_disjoint]
  · rfl
  · rw [Finset.disjoint_left]
    intro v hvFirst hvSecond
    exact (Finset.mem_filter.mp hvSecond).2.1
      (Finset.mem_filter.mp hvFirst).2

theorem card_internalReachWithinTwo_le_card_erase (S : Finset V) (p : V) :
    (internalReachWithinTwo G S p).card ≤ (S.erase p).card := by
  apply Finset.card_le_card
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvS, hvp, _⟩
  exact Finset.mem_erase.mpr ⟨hvp, hvS⟩

/-- In an oriented graph, the number of missing unordered pairs is the defect
from the complete oriented edge count. -/
theorem card_internalMissingPairs_add_edgeCount (S : Finset V)
    (hG : G.IsOriented) :
    (internalMissingPairs G S).card + edgeCount G S S = S.card.choose 2 := by
  classical
  let A : Finset (V × V) := (S ×ˢ S).filter fun uv ↦ G.Adj uv.1 uv.2
  let pairOf : V × V → Finset V := fun uv ↦ {uv.1, uv.2}
  let occupied := (S.powersetCard 2).filter fun e ↦
    ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v
  have hACard : A.card = edgeCount G S S := by
    unfold A edgeCount directCount internalFirstNeighbors
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.card_filter]
  have hPairInj : Set.InjOn pairOf A := by
    intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨haSS, haAdj⟩
    rcases Finset.mem_filter.mp hb with ⟨hbSS, hbAdj⟩
    rcases Finset.mem_product.mp haSS with ⟨ha1S, ha2S⟩
    rcases Finset.mem_product.mp hbSS with ⟨hb1S, hb2S⟩
    have haNe : a.1 ≠ a.2 := fun h ↦ hG.1 a.1 (h ▸ haAdj)
    have hbNe : b.1 ≠ b.2 := fun h ↦ hG.1 b.1 (h ▸ hbAdj)
    have ha1mem : a.1 ∈ pairOf a := by simp [pairOf]
    have ha2mem : a.2 ∈ pairOf a := by simp [pairOf]
    have hb1mem : b.1 ∈ pairOf b := by simp [pairOf]
    have hb2mem : b.2 ∈ pairOf b := by simp [pairOf]
    have ha1b : a.1 = b.1 ∨ a.1 = b.2 := by
      have := hab ▸ ha1mem
      simpa [pairOf] using this
    have ha2b : a.2 = b.1 ∨ a.2 = b.2 := by
      have := hab ▸ ha2mem
      simpa [pairOf] using this
    rcases ha1b with h11 | h12
    · have h22 : a.2 = b.2 := by
        rcases ha2b with h21 | h22
        · exact (haNe (h11.trans h21.symm)).elim
        · exact h22
      exact Prod.ext h11 h22
    · have h21 : a.2 = b.1 := by
        rcases ha2b with h21 | h22
        · exact h21
        · exact (haNe (h12.trans h22.symm)).elim
      have : G.Adj b.2 b.1 := by simpa [h12, h21] using haAdj
      exact (hG.2 hbAdj this).elim
  have hImageEq : A.image pairOf = occupied := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_image.mp he with ⟨a, haA, rfl⟩
      rcases Finset.mem_filter.mp haA with ⟨haSS, haAdj⟩
      rcases Finset.mem_product.mp haSS with ⟨ha1S, ha2S⟩
      have haNe : a.1 ≠ a.2 := fun h ↦ hG.1 a.1 (h ▸ haAdj)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨?_, by simp [pairOf, haNe]⟩, ?_⟩
      · intro v hv
        simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
      · exact ⟨a.1, by simp [pairOf], a.2, by simp [pairOf], haNe, haAdj⟩
    · intro he
      rcases Finset.mem_filter.mp he with
        ⟨hePairs, u, hu, v, hv, huv, huvAdj⟩
      have heSub := (Finset.mem_powersetCard.mp hePairs).1
      apply Finset.mem_image.mpr
      refine ⟨(u, v), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨heSub hu, heSub hv⟩, huvAdj⟩
      · apply Finset.eq_of_subset_of_card_le
        · intro w hw
          simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
          rcases hw with rfl | rfl
          · exact hu
          · exact hv
        · rw [(Finset.mem_powersetCard.mp hePairs).2]
          simp [pairOf, huv]
  have hOccupiedCard : occupied.card = edgeCount G S S := by
    rw [← hImageEq, Finset.card_image_of_injOn hPairInj, hACard]
  have hPartition : internalMissingPairs G S ∪ occupied = S.powersetCard 2 := by
    ext e
    simp only [internalMissingPairs, occupied, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      by_cases hOcc : ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v
      · exact Or.inr ⟨he, hOcc⟩
      · left
        refine ⟨he, ?_⟩
        intro u hu v hv huv huvAdj
        exact hOcc ⟨u, hu, v, hv, huv, huvAdj⟩
  have hDisjoint : Disjoint (internalMissingPairs G S) occupied := by
    rw [Finset.disjoint_left]
    intro e heMissing heOccupied
    rcases Finset.mem_filter.mp heMissing with ⟨_, hMissing⟩
    rcases Finset.mem_filter.mp heOccupied with ⟨_, u, hu, v, hv, huv, huvAdj⟩
    exact hMissing u hu v hv huv huvAdj
  rw [← hOccupiedCard, ← Finset.card_union_of_disjoint hDisjoint,
    hPartition, Finset.card_powersetCard]

/-- A maximum-internal-outdegree vertex reaches all but at most the missing
unordered pairs in one or two steps. -/
theorem exists_internalReachWithinTwo_add_missing_ge (S : Finset V)
    (hS : S.Nonempty) (hG : G.IsOriented) :
    ∃ p ∈ S, S.card - 1 ≤
      (internalReachWithinTwo G S p).card + (internalMissingPairs G S).card := by
  classical
  obtain ⟨p, hpS, hpMax⟩ := Finset.exists_max_image S (directCount G S) hS
  let T := internalFirstNeighbors G S p
  let R := internalReachWithinTwo G S p
  let U := (S.erase p) \ R
  have hTCard : T.card = directCount G S p := rfl
  have hUSub : U ⊆ S.erase p := Finset.sdiff_subset
  have hUNotReach : ∀ v ∈ U, v ∉ R := by
    intro v hv
    exact (Finset.mem_sdiff.mp hv).2
  have hUNotOut : ∀ v ∈ U, ¬G.Adj p v := by
    intro v hvU hpv
    have hvErase := hUSub hvU
    apply hUNotReach v hvU
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_of_mem_erase hvErase, (Finset.mem_erase.mp hvErase).1,
      Or.inl hpv⟩
  have hNoBackFromT : ∀ v ∈ U, ∀ w ∈ T, ¬G.Adj w v := by
    intro v hvU w hwT hwv
    have hvErase := hUSub hvU
    apply hUNotReach v hvU
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_of_mem_erase hvErase, (Finset.mem_erase.mp hvErase).1,
      Or.inr ?_⟩
    exact ⟨w, (Finset.mem_filter.mp hwT).1, (Finset.mem_filter.mp hwT).2, hwv⟩
  have hPartner : ∀ v ∈ U, ∃ w ∈ S,
      w ≠ v ∧ ¬G.Adj v w ∧ ¬G.Adj w v ∧ w ∉ U := by
    intro v hvU
    have hvS := Finset.mem_of_mem_erase (hUSub hvU)
    by_cases hvp : G.Adj v p
    · have hExists : ∃ w ∈ T, ¬G.Adj v w := by
        by_contra hNot
        push Not at hNot
        have hSubset : insert p T ⊆ internalFirstNeighbors G S v := by
          intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | hwT
          · exact Finset.mem_filter.mpr ⟨hpS, hvp⟩
          · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hwT).1,
              hNot w hwT⟩
        have hpNotT : p ∉ T := by
          intro hpT
          exact hG.1 p (Finset.mem_filter.mp hpT).2
        have hCardLower := Finset.card_le_card hSubset
        have hVCard : (internalFirstNeighbors G S v).card = directCount G S v := rfl
        rw [Finset.card_insert_of_notMem hpNotT, hTCard, hVCard] at hCardLower
        have hMax := hpMax v hvS
        omega
      obtain ⟨w, hwT, hvw⟩ := hExists
      have hwS := (Finset.mem_filter.mp hwT).1
      have hwv := hNoBackFromT v hvU w hwT
      have hwNe : w ≠ v := by
        intro h
        subst w
        exact hG.2 (Finset.mem_filter.mp hwT).2 hvp
      have hwNotU : w ∉ U := by
        intro hwU
        exact hUNotOut w hwU (Finset.mem_filter.mp hwT).2
      exact ⟨w, hwS, hwNe, hvw, hwv, hwNotU⟩
    · have hpNe : p ≠ v := (Finset.mem_erase.mp (hUSub hvU)).1.symm
      have hpNotU : p ∉ U := fun hpU ↦
        (Finset.mem_erase.mp (hUSub hpU)).1 rfl
      exact ⟨p, hpS, hpNe, hvp, hUNotOut v hvU, hpNotU⟩
  let partner : V → V := fun v ↦ if hv : v ∈ U then Classical.choose (hPartner v hv) else p
  let charge : V → Finset V := fun v ↦ {v, partner v}
  have hPartnerSpec : ∀ v ∈ U,
      partner v ∈ S ∧ partner v ≠ v ∧ ¬G.Adj v (partner v) ∧
        ¬G.Adj (partner v) v ∧ partner v ∉ U := by
    intro v hv
    simp only [partner, dif_pos hv]
    exact Classical.choose_spec (hPartner v hv)
  have hChargeMissing : ∀ v ∈ U, charge v ∈ internalMissingPairs G S := by
    intro v hvU
    have hvS := Finset.mem_of_mem_erase (hUSub hvU)
    rcases hPartnerSpec v hvU with ⟨hwS, hwv, hvw, hwvAdj, _⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        simp only [charge, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · simp [charge, hwv.symm]
    · intro a ha b hb hab
      simp only [charge, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hvw
      · exact hwvAdj
      · exact (hab rfl).elim
  have hChargeInj : Set.InjOn charge U := by
    intro v hvU v' hvU' hEq
    have hvMem : v ∈ charge v := by simp [charge]
    have hvMem' : v ∈ charge v' := hEq ▸ hvMem
    simp only [charge, Finset.mem_insert, Finset.mem_singleton] at hvMem'
    rcases hvMem' with hvv' | hvPartner
    · exact hvv'
    · exact False.elim ((hPartnerSpec v' hvU').2.2.2.2 (hvPartner ▸ hvU))
  have hUCard : U.card ≤ (internalMissingPairs G S).card := by
    have hImageSubset : U.image charge ⊆ internalMissingPairs G S := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨v, hvU, rfl⟩
      exact hChargeMissing v hvU
    have hCard := Finset.card_le_card hImageSubset
    rw [Finset.card_image_of_injOn hChargeInj] at hCard
    exact hCard
  have hRErase : R ⊆ S.erase p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvS, hvp, _⟩
    exact Finset.mem_erase.mpr ⟨hvp, hvS⟩
  have hSplit : R.card + U.card = (S.erase p).card := by
    have hRCard := Finset.card_le_card hRErase
    dsimp [U]
    rw [Finset.card_sdiff_of_subset hRErase]
    omega
  refine ⟨p, hpS, ?_⟩
  rw [Finset.card_erase_of_mem hpS] at hSplit
  calc
    S.card - 1 = R.card + U.card := hSplit.symm
    _ ≤ R.card + (internalMissingPairs G S).card :=
      Nat.add_le_add_left hUCard R.card
    _ = (internalReachWithinTwo G S p).card +
        (internalMissingPairs G S).card := by rfl

/-- Edge-defect form of the almost-tournament king bound. -/
theorem exists_internalReachWithinTwo_add_edgeDefect_ge (S : Finset V)
    (hS : S.Nonempty) (hG : G.IsOriented) :
    ∃ p ∈ S, S.card - 1 ≤
      (internalReachWithinTwo G S p).card +
        (S.card.choose 2 - edgeCount G S S) := by
  obtain ⟨p, hpS, hp⟩ := exists_internalReachWithinTwo_add_missing_ge G S hS hG
  refine ⟨p, hpS, ?_⟩
  have hMissing := card_internalMissingPairs_add_edgeCount G S hG
  omega

/-- A complete oriented graph has no missing internal pair. -/
theorem internalMissingPairs_eq_empty_of_complete (S : Finset V)
    (hComplete : ∀ {u : V}, u ∈ S → ∀ {v : V}, v ∈ S → u ≠ v →
      G.Adj u v ∨ G.Adj v u) :
    internalMissingPairs G S = ∅ := by
  classical
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  rcases Finset.mem_filter.mp he with ⟨hePair, heMissing⟩
  rcases Finset.mem_powersetCard.mp hePair with ⟨heS, heCard⟩
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp heCard
  have huS : u ∈ S := heS (by simp)
  have hvS : v ∈ S := heS (by simp)
  rcases hComplete huS hvS huv with huvArc | hvuArc
  · exact heMissing u (by simp) v (by simp) huv huvArc
  · exact heMissing v (by simp) u (by simp) huv.symm hvuArc

/-- Certificate-free two-step-king theorem for finite tournaments. -/
theorem exists_internalReachWithinTwo_eq_card_sub_one_of_complete
    (S : Finset V) (hS : S.Nonempty) (hG : G.IsOriented)
    (hComplete : ∀ {u : V}, u ∈ S → ∀ {v : V}, v ∈ S → u ≠ v →
      G.Adj u v ∨ G.Adj v u) :
    ∃ p ∈ S, (internalReachWithinTwo G S p).card = S.card - 1 := by
  obtain ⟨p, hpS, hp⟩ :=
    exists_internalReachWithinTwo_add_missing_ge G S hS hG
  have hMissing := internalMissingPairs_eq_empty_of_complete G S hComplete
  have hUpper := card_internalReachWithinTwo_le_card_erase G S p
  rw [hMissing] at hp
  simp only [Finset.card_empty, Nat.add_zero] at hp
  rw [Finset.card_erase_of_mem hpS] at hUpper
  exact ⟨p, hpS, Nat.le_antisymm hUpper hp⟩

end SeymourEight.Shared
