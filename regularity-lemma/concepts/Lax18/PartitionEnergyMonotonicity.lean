import Lax18.PartitionEnergy

/-!
---
title: Monotonicity of partition energy under refinement
type: theorem
---
If one graph partition refines another, then its weighted mean-square density
is at least that of the coarser partition. This is the finite conditional
variance inequality underlying the energy-increment proof.
-/

namespace Lax18.PartitionEnergyMonotonicity

open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy

universe u

/-- Refining a partition cannot decrease its energy. -/
axiom partitionEnergy_mono_of_refines :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P Q : VertexPartition V),
      Refines Q P → partitionEnergy G P ≤ partitionEnergy G Q

end Lax18.PartitionEnergyMonotonicity
