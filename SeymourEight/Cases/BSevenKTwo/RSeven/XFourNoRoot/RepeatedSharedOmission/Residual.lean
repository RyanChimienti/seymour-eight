import SeymourEight.Cases.BSevenKTwo.Basic
import SeymourEight.Shared.ArcCounting

set_option linter.style.header false

/-!
# The repeated-shared-omission residual

This is the graph-level `x=4`, no-root, `theta=4`, `eta=0` residual with
external missing-row profile `2+1+1+1+1`.  The labels record the canonical
orbit in which two three-neighbor rows omit the same `Z` vertex and that
omitted vertex is used by the two-neighbor row.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def profileDirectCount (i : Fin 7) : Nat :=
  if i.1 = 0 then 2 else if i.1 ≤ 4 then 3 else 4

/-- Labels for the external profile `2+1+1+1+1`.  The `A` order is
`a1,A1[2],X[4],R`; the first five `P` rows have respective `Z`-outdegrees
`2,3,3,3,3`, and the last two have `Z`-outdegree four. -/
structure Profile21111Labels (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 4 ≃ {v : V // v ∈ C.Z}
  a_zero : (a 0).1 = C.a1
  a_aOne : ∀ i : Fin 2, (a ⟨i.1 + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 4, (a ⟨i.1 + 3, by omega⟩).1 ∈ C.X
  a_r : (a 7).1 ∈ C.R
  p_z_count : ∀ i, directCount G C.Z (p i).1 = profileDirectCount i

/-- Canonical labels for a mixed omission: one three-neighbor row contains
the two-neighbor row, while another omits a vertex used by it. -/
structure MixedOmissionLabels (C : G.LocalConfiguration)
    extends Profile21111Labels G C where
  p0_pattern : ∀ j : Fin 4, G.Adj (p 0).1 (z j).1 ↔ j = 2 ∨ j = 3
  p1_pattern : ∀ j : Fin 4, G.Adj (p 1).1 (z j).1 ↔ j ≠ 0
  p2_pattern : ∀ j : Fin 4, G.Adj (p 2).1 (z j).1 ↔ j ≠ 2

/-- Canonical labels for the selected repeated-shared-omission row orbit. -/
structure RepeatedSharedOmissionLabels (C : G.LocalConfiguration)
    extends MixedOmissionLabels G C where
  p3_pattern : ∀ j : Fin 4, G.Adj (p 3).1 (z j).1 ↔ j ≠ 2

/-- A mixed omission before choosing canonical names for the vertices of
`Z`. -/
structure UnnormalizedMixedOmissionLabels (C : G.LocalConfiguration)
    extends Profile21111Labels G C where
  p0_subset_p1 : ∀ j : Fin 4, G.Adj (p 0).1 (z j).1 → G.Adj (p 1).1 (z j).1
  p0_uses_p2_omission : ∃ j : Fin 4,
    G.Adj (p 0).1 (z j).1 ∧ ¬G.Adj (p 2).1 (z j).1

/-- The repeated-shared-omission orbit before choosing canonical names for
the vertices of `Z`. -/
structure UnnormalizedRepeatedSharedOmissionLabels (C : G.LocalConfiguration)
    extends UnnormalizedMixedOmissionLabels G C where
  p2_p3_same : ∀ j : Fin 4, G.Adj (p 2).1 (z j).1 ↔ G.Adj (p 3).1 (z j).1

/-- The selected graph residual: external defect six, no root tail, complete
`H`, and the canonical repeated-shared-omission incidence orbit. -/
def ThetaFourEtaZeroRepeatedSharedOmissionResidual
    (C : G.LocalConfiguration) : Prop :=
  C.X.card = 4 ∧ C.Z.card = 4 ∧
  edgeCount G C.P {C.s} = 0 ∧ edgeCount G C.H C.P = 29 ∧
  C.H.card = 6 ∧ edgeCount G C.H C.H = 15 ∧
  Nonempty (RepeatedSharedOmissionLabels G C)

/-- The canonically labeled mixed-omission residual. -/
def ThetaFourEtaZeroMixedOmissionResidual
    (C : G.LocalConfiguration) : Prop :=
  C.X.card = 4 ∧ C.Z.card = 4 ∧
  edgeCount G C.P {C.s} = 0 ∧ edgeCount G C.H C.P = 29 ∧
  C.H.card = 6 ∧ edgeCount G C.H C.H = 15 ∧
  Nonempty (MixedOmissionLabels G C)

/-- The label-independent repeated-shared-omission residual.  Compared with
`ThetaFourEtaZeroRepeatedSharedOmissionResidual`, it does not prescribe which
vertices of `Z` receive indices zero through three. -/
def ThetaFourEtaZeroProfile21111RepeatedSharedOmissionResidual
    (C : G.LocalConfiguration) : Prop :=
  C.X.card = 4 ∧ C.Z.card = 4 ∧
  edgeCount G C.P {C.s} = 0 ∧ edgeCount G C.H C.P = 29 ∧
  C.H.card = 6 ∧ edgeCount G C.H C.H = 15 ∧
  Nonempty (UnnormalizedRepeatedSharedOmissionLabels G C)

/-- The intrinsic mixed-omission residual, with no prescribed numbering of
the vertices of `Z`. -/
def ThetaFourEtaZeroProfile21111MixedOmissionResidual
    (C : G.LocalConfiguration) : Prop :=
  C.X.card = 4 ∧ C.Z.card = 4 ∧
  edgeCount G C.P {C.s} = 0 ∧ edgeCount G C.H C.P = 29 ∧
  C.H.card = 6 ∧ edgeCount G C.H C.H = 15 ∧
  Nonempty (UnnormalizedMixedOmissionLabels G C)

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot
