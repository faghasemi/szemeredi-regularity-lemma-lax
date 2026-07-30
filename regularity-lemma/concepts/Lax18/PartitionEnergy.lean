import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lax18.RegularPartitions

/-!
---
title: Refinement and the index of a graph partition
type: definition
---
A partition Q refines a partition P when every class of Q is contained in a
class of P.

The index, also called the mean-square density or energy, of a partition is
the weighted average of the squared densities between all ordered pairs of
its classes. The weight of the pair (Vᵢ,Vⱼ) is |Vᵢ||Vⱼ|/|V|².
Including diagonal pairs makes this an exact conditional mean-square and is
convenient for the refinement argument.
-/

namespace Lax18.PartitionEnergy

open Lax18.EdgeDensity
open Lax18.FiniteGraphPartitions
open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `Q.Refines P` means that every class of `Q` lies in a class of `P`. -/
def Refines (Q P : VertexPartition V) : Prop :=
  ∀ j : Fin Q.partCount,
    ∃ i : Fin P.partCount, Q.part j ⊆ P.part i

/-- The normalized weight of the ordered pair of classes `(i,j)`. -/
noncomputable def pairWeight (P : VertexPartition V)
    (i j : Fin P.partCount) : ℝ :=
  ((P.partSize i : ℝ) * (P.partSize j : ℝ)) /
    (Fintype.card V : ℝ) ^ 2

/-- The weighted mean-square density (or index) of a graph partition. -/
noncomputable def partitionEnergy (G : SimpleGraph V)
    (P : VertexPartition V) : ℝ :=
  ∑ i : Fin P.partCount,
    ∑ j : Fin P.partCount,
      pairWeight P i j * (density G (P.part i) (P.part j)) ^ 2

end Lax18.PartitionEnergy
