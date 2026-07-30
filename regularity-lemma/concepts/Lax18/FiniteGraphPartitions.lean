import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
---
title: Finite graph vertex partitions
type: definition
---
A finite vertex partition is an indexed family of nonempty vertex sets which
are pairwise disjoint and cover the whole vertex set.  The indexing keeps the
number of parts explicit, which is convenient for the regularity lemma.

An equitable partition is one in which any two parts have sizes differing by
at most one.  This is the clean textbook convention: there is no exceptional
leftover class.
-/

namespace Lax18.FiniteGraphPartitions

universe u

/-- An indexed partition of a finite vertex set. -/
structure VertexPartition (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The number of parts. -/
  partCount : ℕ
  /-- The part indexed by `i`. -/
  part : Fin partCount → Finset V
  /-- Every part is nonempty. -/
  nonempty_part : ∀ i : Fin partCount, (part i).Nonempty
  /-- Distinct parts are disjoint. -/
  pairwise_disjoint :
    ∀ i j : Fin partCount, i ≠ j → Disjoint (part i) (part j)
  /-- The parts cover all vertices. -/
  covers : ∀ v : V, ∃ i : Fin partCount, v ∈ part i

namespace VertexPartition

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The size of a part of a vertex partition. -/
def partSize (P : VertexPartition V) (i : Fin P.partCount) : ℕ :=
  (P.part i).card

/-- A partition is equitable if any two part sizes differ by at most one. -/
def Equitable (P : VertexPartition V) : Prop :=
  ∀ i j : Fin P.partCount,
    P.partSize i ≤ P.partSize j + 1 ∧
      P.partSize j ≤ P.partSize i + 1

/-- A partition has exactly `k` parts. -/
def HasPartCount (P : VertexPartition V) (k : ℕ) : Prop :=
  P.partCount = k

end VertexPartition

end Lax18.FiniteGraphPartitions
