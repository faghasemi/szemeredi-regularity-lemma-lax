import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

/-!
---
title: Edge density between two vertex sets
type: definition
---
For a finite simple graph, the edge count between two vertex sets counts the
ordered cross-pairs \((a,b)\in A\times B\) which are adjacent in the graph.
When the two sets are disjoint, this counts each edge between them exactly
once, in the direction from \(A\) to \(B\).

The edge density of \(A\) and \(B\) is this edge count divided by
\(|A||B|\), as a real number.  If one side is empty, the density is defined to
be zero; regular pairs themselves require nonempty sides.
-/

namespace Lax18.EdgeDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The number of adjacent ordered pairs from `A` to `B`. -/
noncomputable def edgeCountBetween (G : SimpleGraph V)
    (A B : Finset V) : ℕ := by
  classical
  exact ((A.product B).filter fun p : V × V => G.Adj p.1 p.2).card

/-- The real-valued edge density between two vertex sets. -/
noncomputable def density (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  if A.card = 0 ∨ B.card = 0 then
    0
  else
    (edgeCountBetween G A B : ℝ) / ((A.card : ℝ) * (B.card : ℝ))

end Lax18.EdgeDensity
