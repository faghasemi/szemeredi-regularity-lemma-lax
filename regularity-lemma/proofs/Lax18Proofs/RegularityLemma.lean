import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Lax18.SzemerediRegularityLemma

namespace Lax18Proofs

open Finset Fintype
open Lax18.EdgeDensity
open Lax18.FiniteGraphPartitions
open Lax18.RegularPairs
open Lax18.RegularPartitions

universe u

/-- Turn mathlib's unlabelled finite partition into the indexed partition
used by the concepts in this submission. -/
noncomputable def vertexPartitionOfFinpartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) : VertexPartition V := by
  classical
  refine
    { partCount := P.parts.card
      part := fun i => (P.parts.equivFin.symm i).1
      nonempty_part := fun i =>
        P.nonempty_of_mem_parts (P.parts.equivFin.symm i).2
      pairwise_disjoint := fun i j hij =>
        P.disjoint (P.parts.equivFin.symm i).2
          (P.parts.equivFin.symm j).2 ?_
      covers := fun v => ?_ }
  · intro h
    apply hij
    exact P.parts.equivFin.symm.injective (Subtype.ext h)
  · obtain ⟨A, hA, hvA⟩ := P.exists_mem (Finset.mem_univ v)
    let a : P.parts := ⟨A, hA⟩
    refine ⟨P.parts.equivFin a, ?_⟩
    simpa [a] using hvA

@[simp]
lemma vertexPartitionOfFinpartition_partCount
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) :
    (vertexPartitionOfFinpartition P).partCount = P.parts.card :=
  rfl

@[simp]
lemma vertexPartitionOfFinpartition_part
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (i : Fin P.parts.card) :
    (vertexPartitionOfFinpartition P).part i =
      (P.parts.equivFin.symm i).1 :=
  rfl

lemma density_eq_mathlib_edgeDensity
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    density G A B = (G.edgeDensity A B : ℝ) := by
  classical
  by_cases hA : A.card = 0
  · have : A = ∅ := Finset.card_eq_zero.mp hA
    subst A
    simp [density]
  by_cases hB : B.card = 0
  · have : B = ∅ := Finset.card_eq_zero.mp hB
    subst B
    simp [density]
  simp only [density, hA, hB, false_or, if_false,
    SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_mul]
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext p
  simp [SimpleGraph.interedges, Rel.interedges]

lemma isRegularPair_of_mathlib_isUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : G.IsUniform ε A B) :
    IsRegularPair G ε A B := by
  refine ⟨hA, hB, ?_⟩
  intro X Y hX hY
  rw [density_eq_mathlib_edgeDensity, density_eq_mathlib_edgeDensity]
  exact
    (h hX.1 hY.1 (by simpa [mul_comm] using hX.2)
      (by simpa [mul_comm] using hY.2)).le

noncomputable def partPairEmbedding
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) :
    (Fin P.parts.card × Fin P.parts.card) ↪ (Finset V × Finset V) where
  toFun p :=
    ((P.parts.equivFin.symm p.1).1, (P.parts.equivFin.symm p.2).1)
  inj' p q h := by
    apply Prod.ext
    · apply P.parts.equivFin.symm.injective
      apply Subtype.ext
      exact congrArg Prod.fst h
    · apply P.parts.equivFin.symm.injective
      apply Subtype.ext
      exact congrArg Prod.snd h

lemma irregularPairCount_le_mathlib_nonUniforms
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (P : Finpartition (Finset.univ : Finset V)) :
    irregularPairCount G ε (vertexPartitionOfFinpartition P) ≤
      (P.nonUniforms G ε).card := by
  classical
  rw [irregularPairCount]
  let S : Finset (Fin P.parts.card × Fin P.parts.card) :=
    irregularPairIndices G ε (vertexPartitionOfFinpartition P)
  change S.card ≤ (P.nonUniforms G ε).card
  calc
    S.card = (S.map (partPairEmbedding P)).card :=
      (Finset.card_map (partPairEmbedding P)).symm
    _ ≤ (P.nonUniforms G ε).card := Finset.card_le_card (by
      rintro uv huv
      rw [Finset.mem_map] at huv
      obtain ⟨p, hp, rfl⟩ := huv
      change p ∈ (Finset.univ.product Finset.univ).filter
        (fun q : Fin P.parts.card × Fin P.parts.card =>
          q.1 < q.2 ∧
            ¬ IsRegularPair G ε
              ((vertexPartitionOfFinpartition P).part q.1)
              ((vertexPartitionOfFinpartition P).part q.2)) at hp
      have hp' := (Finset.mem_filter.mp hp).2
      rw [Finpartition.mk_mem_nonUniforms]
      refine ⟨(P.parts.equivFin.symm p.1).2,
        (P.parts.equivFin.symm p.2).2, ?_, ?_⟩
      · intro hparts
        have hpEq : p.1 = p.2 := by
          apply P.parts.equivFin.symm.injective
          exact Subtype.ext hparts
        exact hp'.1.ne hpEq
      · intro hUniform
        apply hp'.2
        exact
          isRegularPair_of_mathlib_isUniform G ε _ _
            (P.nonempty_of_mem_parts (P.parts.equivFin.symm p.1).2)
            (P.nonempty_of_mem_parts (P.parts.equivFin.symm p.2).2)
            hUniform)

lemma isRegularPartition_of_mathlib_isUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (P : Finpartition (Finset.univ : Finset V))
    (hε : 0 ≤ ε) (hUniform : P.IsUniform G ε) :
    IsRegularPartition G ε (vertexPartitionOfFinpartition P) := by
  rw [IsRegularPartition]
  calc
    (irregularPairCount G ε (vertexPartitionOfFinpartition P) : ℝ) ≤
        ((P.nonUniforms G ε).card : ℝ) := by
      exact_mod_cast irregularPairCount_le_mathlib_nonUniforms G ε P
    _ ≤ ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) * ε :=
      hUniform
    _ ≤ (P.parts.card : ℝ) ^ 2 * ε := by
      gcongr
      norm_cast
      simpa [pow_two] using
        Nat.mul_le_mul_left P.parts.card (Nat.sub_le P.parts.card 1)
    _ = ε * ((vertexPartitionOfFinpartition P).partCount : ℝ) ^ 2 := by
      simp [mul_comm]

lemma equitable_of_mathlib_isEquipartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (hP : P.IsEquipartition) :
    (vertexPartitionOfFinpartition P).Equitable := by
  intro i j
  change
    (P.parts.equivFin.symm i).1.card ≤
        (P.parts.equivFin.symm j).1.card + 1 ∧
      (P.parts.equivFin.symm j).1.card ≤
        (P.parts.equivFin.symm i).1.card + 1
  exact
    ⟨hP (P.parts.equivFin.symm i).2 (P.parts.equivFin.symm j).2,
      hP (P.parts.equivFin.symm j).2 (P.parts.equivFin.symm i).2⟩

/--
---
conclusion: Lax18.SzemerediRegularityLemma.szemeredi_regularity_lemma
---
The proof translates mathlib's equitable uniform partition into the indexed
partition and non-strict regularity conventions used by this submission.

# Proof strategy
Apply mathlib's effective equitable form of Szemerédi's regularity lemma, map
its finite partition to the indexed partition used by the concept package,
and transport equitability and regularity across the two definitions.

# Attribution
The mathematical statement and energy-increment presentation follow Reinhard
Diestel, *Graph Theory*, 5th edition, Section 7.4.  The checked proof concludes
the clean equipartition variant by translating the theorem formalized in
mathlib by Yaël Dillies and Bhavik Mehta.
-/
theorem szemeredi_regularity_lemma :
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
                        IsEquitableRegularPartition G ε P := by
  intro ε m₀ hε _hm₀
  classical
  refine ⟨SzemerediRegularity.bound ε m₀,
    SzemerediRegularity.le_bound ε m₀, ?_⟩
  intro V _instFintype _instDecidableEq G hcard
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨P, hEquitable, hLower, hUpper, hUniform⟩ :=
    szemeredi_regularity G hε hcard
  refine ⟨vertexPartitionOfFinpartition P, ?_, ?_, ?_⟩
  · simpa using hLower
  · simpa using hUpper
  · exact
      ⟨equitable_of_mathlib_isEquipartition P hEquitable,
        isRegularPartition_of_mathlib_isUniform G ε P hε.le hUniform⟩

end Lax18Proofs
