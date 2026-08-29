import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.Labels
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.CoreDefs

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Encoding

open Labels Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def graphArc {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) : Bool :=
  if hiA : i < 8 then
    if hjA : j < 8 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 13 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if hjQ : j < 15 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.q ⟨j - 13, by omega⟩).1)
    else false
  else if hiP : i < 13 then
    if hjA : j < 8 then decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 13 then decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if hjQ : j < 15 then decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.q ⟨j - 13, by omega⟩).1)
    else false
  else false

def graphPToZ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) : Bool :=
  if hp : p < 5 then
    if hz : z < zCount then decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1)
    else false
  else false

@[simp] theorem aArc_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (graphArc G L) i j = decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  simp [aArc, graphArc, hi, hj]

@[simp] theorem aToP_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i p : Nat) (hi : i < 8) (hp : p < 5) :
    aToP (graphArc G L) i p = decide (G.Adj (L.a ⟨i, hi⟩).1 (L.p ⟨p, hp⟩).1) := by
  simp [aToP, graphArc, hi, show 8 + p < 13 by omega]

@[simp] theorem pToA_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p i : Nat) (hp : p < 5) (hi : i < 8) :
    pToA (graphArc G L) p i = decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨i, hi⟩).1) := by
  simp [pToA, graphArc, hi, show 8 + p < 13 by omega]

@[simp] theorem pArc_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p r : Nat) (hp : p < 5) (hr : r < 5) :
    pArc (graphArc G L) p r = decide (G.Adj (L.p ⟨p, hp⟩).1 (L.p ⟨r, hr⟩).1) := by
  simp [pArc, graphArc, show 8 + p < 13 by omega, show 8 + r < 13 by omega]

@[simp] theorem aToQ_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i q : Nat) (hi : i < 8) (hq : q < 2) :
    aToQ (graphArc G L) i q = decide (G.Adj (L.a ⟨i, hi⟩).1 (L.q ⟨q, hq⟩).1) := by
  have hNotA : ¬13 + q < 8 := by omega
  have hNotP : ¬13 + q < 13 := by omega
  simp [aToQ, graphArc, hi, hNotA, hNotP, show 13 + q < 15 by omega]

@[simp] theorem pToQ_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p q : Nat) (hp : p < 5) (hq : q < 2) :
    pToQ (graphArc G L) p q = decide (G.Adj (L.p ⟨p, hp⟩).1 (L.q ⟨q, hq⟩).1) := by
  have hNotA : ¬13 + q < 8 := by omega
  have hNotP : ¬13 + q < 13 := by omega
  simp [pToQ, graphArc, hNotA, hNotP, show 8 + p < 13 by omega,
    show 13 + q < 15 by omega]

@[simp] theorem pToZ_graph {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) (hp : p < 5) (hz : z < zCount) :
    graphPToZ G L p z = decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  simp [graphPToZ, hp, hz]

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Encoding
