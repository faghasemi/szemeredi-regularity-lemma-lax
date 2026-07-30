import Lax18.FiniteGraphPartitions
import Lax18.RegularPairs

/-!
---
title: Regular partitions
type: definition
---
For a vertex partition with \(k\) parts, an unordered pair of distinct parts is
irregular if it is not an \(\varepsilon\)-regular pair.  A partition is
\(\varepsilon\)-regular when the number of irregular unordered pairs is at most
\(\varepsilon k^2\).

An equitable \(\varepsilon\)-regular partition is an \(\varepsilon\)-regular
partition whose part sizes differ by at most one.
-/

namespace Lax18.RegularPartitions

open Lax18.FiniteGraphPartitions
open Lax18.RegularPairs

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The unordered irregular pairs of parts, represented by index pairs
`i < j`. -/
noncomputable def irregularPairIndices
    (G : SimpleGraph V) (ε : ℝ)
    (P : VertexPartition V) : Finset (Fin P.partCount × Fin P.partCount) := by
  classical
  exact
    (Finset.univ.product Finset.univ).filter
      (fun p : Fin P.partCount × Fin P.partCount =>
        p.1 < p.2 ∧
          ¬ IsRegularPair G ε (P.part p.1) (P.part p.2))

/-- The number of unordered irregular pairs of parts. -/
noncomputable def irregularPairCount
    (G : SimpleGraph V) (ε : ℝ)
    (P : VertexPartition V) : ℕ :=
  (irregularPairIndices G ε P).card

/-- A partition is `ε`-regular if it has at most `ε k^2` irregular unordered
pairs of distinct parts. -/
def IsRegularPartition (G : SimpleGraph V) (ε : ℝ)
    (P : VertexPartition V) : Prop :=
  (irregularPairCount G ε P : ℝ) ≤ ε * (P.partCount : ℝ) ^ 2

/-- A clean equitable `ε`-regular partition. -/
def IsEquitableRegularPartition
    (G : SimpleGraph V) (ε : ℝ) (P : VertexPartition V) : Prop :=
  P.Equitable ∧ IsRegularPartition G ε P

end Lax18.RegularPartitions
