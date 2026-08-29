import SeymourEight.Certificates.BSevenKThree.RSix.XFour.XHDeletionDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.XHDeletionBridge

open Shared.FiniteCore HDeletion

theorem xQDeletionConditions_true_of_hQDeletionConditions_true
    (arc pToZ : Nat → Nat → Bool)
    (hAll : hQDeletionConditions arc pToZ = true) :
    xQDeletionConditions arc pToZ = true := by
  rw [hQDeletionConditions, all_eq_true_iff] at hAll
  rw [xQDeletionConditions, all_eq_true_iff]
  intro x hx
  exact hAll (3 + x) (by omega)

theorem xHDeletionLeaf_true_of_hDeletionLeaf_true
    (m delta alphaValue betaValue : Nat) (arc pToZ : Nat → Nat → Bool)
  (hLeaf : hDeletionLeaf m delta alphaValue betaValue arc pToZ = true) :
    xHDeletionLeaf m delta alphaValue betaValue arc pToZ = true := by
  simp only [hDeletionLeaf, Bool.and_eq_true] at hLeaf
  simp only [xHDeletionLeaf, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hLeaf.1.1.1.1.1,
    xQDeletionConditions_true_of_hQDeletionConditions_true arc pToZ
      hLeaf.1.1.1.1.2⟩,
    hLeaf.1.1.1.2⟩, hLeaf.1.1.2⟩, hLeaf.1.2⟩, hLeaf.2⟩

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.XHDeletionBridge
