import Lax18.PartitionEnergy

/-!
---
title: Equitable cleanup of a bounded partition
type: theorem
---
For every error tolerance η > 0 and bound r on the number of classes,
there are uniform bounds K,N with the following property. Every partition
of a graph on at least N vertices into at most r classes can be
replaced by an equitable partition into between its original number of
classes and K classes, while losing at most η of its energy.

Conceptually, each old class is cut into nearly equal small pieces and the
few remainders are redistributed.  This is the cleanup step that allows the
energy-increment proof to maintain the clean textbook formulation without an
exceptional class.
-/

namespace Lax18.EquitableCleanup

open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy

universe u

/-- A bounded partition can be made equitable with arbitrarily small loss of
energy, uniformly over all sufficiently large finite graphs. -/
axiom equitable_cleanup :
  ∀ (η : ℝ) (r : ℕ),
    0 < η →
      0 < r →
        ∃ K N : ℕ,
          r ≤ K ∧
            r ≤ N ∧
              ∀ {V : Type u} [Fintype V] [DecidableEq V]
                (G : SimpleGraph V) (P : VertexPartition V),
                  P.partCount ≤ r →
                    N ≤ Fintype.card V →
                      ∃ Q : VertexPartition V,
                        Q.Equitable ∧
                          P.partCount ≤ Q.partCount ∧
                            Q.partCount ≤ K ∧
                              partitionEnergy G P ≤
                                partitionEnergy G Q + η

end Lax18.EquitableCleanup
