import Lax18.PartitionEnergyBounds
import Mathlib.Tactic

namespace Lax18Proofs

open Lax18.EdgeDensity
open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy
open scoped BigOperators

universe u

private lemma density_nonneg {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) :
    0 ≤ density G A B := by
  rw [density]
  split_ifs
  · norm_num
  · exact div_nonneg (by positivity) (by positivity)

private lemma density_le_one {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) :
    density G A B ≤ 1 := by
  classical
  rw [density]
  split_ifs
  · norm_num
  · apply div_le_one_of_le₀
    · norm_cast
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product A B)
    · positivity

private lemma sum_partSize_le_card {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    ∑ i : Fin P.partCount, P.partSize i ≤ Fintype.card V := by
  have hdisjoint :
      ((Finset.univ : Finset (Fin P.partCount)) : Set (Fin P.partCount)).PairwiseDisjoint
        P.part := by
    intro i _ j _ hij
    exact P.pairwise_disjoint i j hij
  calc
    ∑ i : Fin P.partCount, P.partSize i =
        ((Finset.univ : Finset (Fin P.partCount)).biUnion P.part).card := by
          symm
          simpa [VertexPartition.partSize] using Finset.card_biUnion hdisjoint
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (by simp)
    _ = Fintype.card V := Finset.card_univ

private lemma pairWeight_nonneg {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) (i j : Fin P.partCount) :
    0 ≤ pairWeight P i j := by
  exact div_nonneg (mul_nonneg (by positivity) (by positivity)) (sq_nonneg _)

private lemma sum_pairWeight_eq {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    (∑ i : Fin P.partCount, ∑ j : Fin P.partCount, pairWeight P i j) =
      (∑ i : Fin P.partCount, (P.partSize i : ℝ)) ^ 2 /
        (Fintype.card V : ℝ) ^ 2 := by
  simp only [pairWeight]
  calc
    (∑ i : Fin P.partCount,
        ∑ j : Fin P.partCount,
          (P.partSize i : ℝ) * (P.partSize j : ℝ) /
            (Fintype.card V : ℝ) ^ 2) =
        (∑ i : Fin P.partCount,
          ∑ j : Fin P.partCount,
            (P.partSize i : ℝ) * (P.partSize j : ℝ)) /
          (Fintype.card V : ℝ) ^ 2 := by
            simp_rw [← Finset.sum_div]
    _ = (∑ i : Fin P.partCount, (P.partSize i : ℝ)) ^ 2 /
          (Fintype.card V : ℝ) ^ 2 := by
      congr 1
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

private lemma sum_pairWeight_le_one {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    ∑ i : Fin P.partCount, ∑ j : Fin P.partCount, pairWeight P i j ≤ 1 := by
  rw [sum_pairWeight_eq]
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · have hsum_nat := sum_partSize_le_card P
    have hsum :
        (∑ i : Fin P.partCount, (P.partSize i : ℝ)) ≤
          (Fintype.card V : ℝ) := by
      exact_mod_cast hsum_nat
    have hsum_nonneg :
        0 ≤ ∑ i : Fin P.partCount, (P.partSize i : ℝ) := by positivity
    have hcard_pos : 0 < (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hV)
    rw [div_le_one (sq_pos_of_pos hcard_pos)]
    nlinarith

/--
---
conclusion: Lax18.PartitionEnergyBounds.partitionEnergy_mem_unitInterval
---
The density between two finite vertex sets lies in the unit interval. Hence
each energy summand is nonnegative and at most its pair weight. Disjointness
of the partition classes bounds the total pair weight by one.
-/
theorem partitionEnergy_mem_unitInterval :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (P : VertexPartition V),
        0 ≤ partitionEnergy G P ∧ partitionEnergy G P ≤ 1 := by
  intro V _ _ G P
  constructor
  · unfold partitionEnergy
    exact Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦
        mul_nonneg (pairWeight_nonneg P i j) (sq_nonneg _)
  · calc
      partitionEnergy G P ≤
          ∑ i : Fin P.partCount, ∑ j : Fin P.partCount, pairWeight P i j := by
            unfold partitionEnergy
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_of_le_one_right (pairWeight_nonneg P i j)
            have h₀ := density_nonneg G (P.part i) (P.part j)
            have h₁ := density_le_one G (P.part i) (P.part j)
            nlinarith
      _ ≤ 1 := sum_pairWeight_le_one P

end Lax18Proofs
