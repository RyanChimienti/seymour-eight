import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.Labels
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CoreDefs

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Encoding

open Labels Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def graphArc {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) : Bool :=
  if hiA : i < 8 then
    if hjA : j < 8 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 14 then
      decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if hjQ : j = 14 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.q 0).1)
    else false
  else if hiP : i < 14 then
    if hjA : j < 8 then decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 14 then
      decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if hjQ : j = 14 then decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.q 0).1)
    else false
  else false

def graphPToZ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) : Bool :=
  if hp : p < 6 then
    if hz : z < zCount then decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1)
    else false
  else false

@[simp] theorem aArc_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (graphArc G L) i j =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  simp [aArc, graphArc, hi, hj]

@[simp] theorem aToP_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i p : Nat) (hi : i < 8) (hp : p < 6) :
    aToP (graphArc G L) i p =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.p ⟨p, hp⟩).1) := by
  have hip : 8 + p < 14 := by omega
  simp [aToP, graphArc, hi, hip]

@[simp] theorem pToA_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p i : Nat) (hp : p < 6) (hi : i < 8) :
    pToA (graphArc G L) p i =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨i, hi⟩).1) := by
  have hip : 8 + p < 14 := by omega
  simp [pToA, graphArc, hi, hip]

@[simp] theorem pArc_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p r : Nat) (hp : p < 6) (hr : r < 6) :
    pArc (graphArc G L) p r =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.p ⟨r, hr⟩).1) := by
  have hip : 8 + p < 14 := by omega
  have hir : 8 + r < 14 := by omega
  simp [pArc, graphArc, hip, hir]

@[simp] theorem aToQ_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i : Nat) (hi : i < 8) :
    aToQ (graphArc G L) i =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.q 0).1) := by
  simp [aToQ, graphArc, hi]

@[simp] theorem pToQ_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p : Nat) (hp : p < 6) :
    pToQ (graphArc G L) p =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1) := by
  have hip : 8 + p < 14 := by omega
  simp [pToQ, graphArc, hip]

@[simp] theorem pToZ_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) (hp : p < 6) (hz : z < zCount) :
    graphPToZ G L p z =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  simp [graphPToZ, hp, hz]

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Encoding
