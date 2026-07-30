import Lax18.EdgeDensity

/-!
---
title: Regular pairs
type: definition
---
An \(\varepsilon\)-regular pair in a finite simple graph is a pair of nonempty
vertex sets \(A,B\) such that every \(X\subseteq A\) and \(Y\subseteq B\) with
\(|X|\ge \varepsilon |A|\) and \(|Y|\ge \varepsilon |B|\) has density within
\(\varepsilon\) of the density of \(A,B\).

This is the standard textbook definition, stated with real-valued densities.
The definition itself does not require \(A\) and \(B\) to be disjoint; in the
regularity lemma they are used as distinct blocks of a vertex partition, hence
are disjoint there.
-/

namespace Lax18.RegularPairs

open Lax18.EdgeDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `X` is a large enough subset of `A` for the threshold `ε`. -/
def LargeSubset (ε : ℝ) (A X : Finset V) : Prop :=
  X ⊆ A ∧ ε * (A.card : ℝ) ≤ (X.card : ℝ)

/-- The pair `(A,B)` is `ε`-regular in `G`. -/
def IsRegularPair (G : SimpleGraph V) (ε : ℝ) (A B : Finset V) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧
    ∀ X Y : Finset V,
      LargeSubset ε A X →
        LargeSubset ε B Y →
          |density G X Y - density G A B| ≤ ε

end Lax18.RegularPairs
