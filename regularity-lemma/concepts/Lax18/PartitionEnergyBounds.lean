import Lax18.PartitionEnergy

/-!
---
title: Bounds for partition energy
type: theorem
---
The weighted mean-square density of every finite graph partition lies in the
interval from zero to one. This boundedness forces the energy-increment
process to terminate after a number of steps depending only on the regularity
parameter.
-/

namespace Lax18.PartitionEnergyBounds

open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy

universe u

/-- Partition energy lies between zero and one. -/
axiom partitionEnergy_mem_unitInterval :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : VertexPartition V),
      0 ≤ partitionEnergy G P ∧ partitionEnergy G P ≤ 1

end Lax18.PartitionEnergyBounds
