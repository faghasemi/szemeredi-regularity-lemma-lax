import Lax18.EnergyIncrement
import Lax18.EquitableCleanup
import Lax18.PartitionEnergyBounds
import Lax18.PartitionEnergyMonotonicity

/-!
---
title: Szemerédi's regularity lemma
type: theorem
---
Szemerédi's regularity lemma says that for every \(\varepsilon>0\) and every
positive lower bound \(m_0\), there is an upper bound \(M\ge m_0\) such that
every finite simple graph on at least \(m_0\) vertices has an equitable
\(\varepsilon\)-regular partition into \(k\) parts with \(m_0\le k\le M\).

The partition is clean: its parts are nonempty, pairwise disjoint, cover all
vertices, and have sizes differing by at most one.  There is no exceptional
leftover class.

# Source
The classical lower-bound statement and its energy-increment presentation
follow Reinhard Diestel, *Graph Theory*, 5th edition, Section 7.4.  Diestel
uses an exceptional class to make the remaining classes exactly equal; the
statement here uses the equivalent clean equipartition convention, with all
part sizes differing by at most one.
-/

namespace Lax18.SzemerediRegularityLemma

open Lax18.FiniteGraphPartitions
open Lax18.RegularPartitions

universe u

/-- Szemerédi's regularity lemma for finite simple graphs, in the standard
lower-bound form. -/
axiom szemeredi_regularity_lemma :
  ∀ (ε : ℝ) (m₀ : ℕ),
    0 < ε →
      0 < m₀ →
        ∃ M : ℕ,
          m₀ ≤ M ∧
            ∀ {V : Type u} [Fintype V] [DecidableEq V]
              (G : SimpleGraph V),
                m₀ ≤ Fintype.card V →
                  ∃ P : VertexPartition V,
                    m₀ ≤ P.partCount ∧
                      P.partCount ≤ M ∧
                        IsEquitableRegularPartition G ε P

end Lax18.SzemerediRegularityLemma
