import Lax18.PartitionEnergy

/-!
---
title: The energy-increment refinement lemma
type: theorem
---
This is the standard energy-increment step.  If an equitable partition P is
not ε-regular, witnesses for all
irregular pairs simultaneously split its classes.  The resulting refinement
has at most k·2^k classes and raises the energy by at least ε⁵/4.
The constant is deliberately conservative; what matters
for the regularity lemma is a positive increment depending only on
ε.
-/

namespace Lax18.EnergyIncrement

open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy
open Lax18.RegularPartitions

universe u

/-- An irregular equitable partition admits a bounded refinement with a
definite energy increment. -/
axiom energy_increment_refinement :
  ∀ (ε : ℝ),
    0 < ε →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (P : VertexPartition V),
          P.Equitable →
            ¬ IsRegularPartition G ε P →
              ∃ Q : VertexPartition V,
                Refines Q P ∧
                  P.partCount ≤ Q.partCount ∧
                    Q.partCount ≤ P.partCount * 2 ^ P.partCount ∧
                      partitionEnergy G P + ε ^ 5 / 4 ≤
                        partitionEnergy G Q

end Lax18.EnergyIncrement
