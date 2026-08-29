import SeymourEight.Definitions

set_option linter.style.header false

/-!
# Internal first and second neighborhoods

These definitions restrict first and strict second neighborhoods to a chosen
set of vertices.
-/

namespace SeymourEight.CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [DecidableRel G.Adj]

/-- The direct outneighbors of `p` which remain inside `S`. -/
def internalFirstNeighbors (S : Finset V) (p : V) : Finset V :=
  S.filter (G.Adj p)

/--
The strict second outneighbors of `p` inside `S` witnessed by an intermediate
vertex which also belongs to `S`.
-/
def internalSecondNeighbors [DecidableEq V] (S : Finset V) (p : V) : Finset V :=
  S.filter fun v ↦ ¬G.Adj p v ∧ v ≠ p ∧
    ∃ w ∈ S, G.Adj p w ∧ G.Adj w v

end SeymourEight.CertificateBridge
