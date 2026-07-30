import Lax18.EnergyIncrement
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Lax18Proofs

open Finset Fintype
open Lax18.EdgeDensity
open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy
open Lax18.RegularPairs
open Lax18.RegularPartitions
open scoped BigOperators

universe u

private lemma density_eq_edgeDensity
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

/-- Turn an unlabelled `Finpartition` into the indexed partition used by the
concept statement. -/
private noncomputable def vertexPartitionOfFinpartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (R : Finpartition (Finset.univ : Finset V)) : VertexPartition V := by
  classical
  refine
    { partCount := R.parts.card
      part := fun i => (R.parts.equivFin.symm i).1
      nonempty_part := fun i =>
        R.nonempty_of_mem_parts (R.parts.equivFin.symm i).2
      pairwise_disjoint := fun i j hij =>
        R.disjoint (R.parts.equivFin.symm i).2
          (R.parts.equivFin.symm j).2 ?_
      covers := fun v => ?_ }
  · intro h
    apply hij
    exact R.parts.equivFin.symm.injective (Subtype.ext h)
  · obtain ⟨A, hA, hvA⟩ := R.exists_mem (Finset.mem_univ v)
    let a : R.parts := ⟨A, hA⟩
    refine ⟨R.parts.equivFin a, ?_⟩
    simpa [a] using hvA

private noncomputable def weightedEnergy
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finpartition (Finset.univ : Finset V)) : ℝ :=
  ∑ A ∈ R.parts, ∑ B ∈ R.parts,
    ((A.card : ℝ) * (B.card : ℝ)) /
        (Fintype.card V : ℝ) ^ 2 *
      (G.edgeDensity A B : ℝ) ^ 2

private lemma partitionEnergy_vertexPartitionOfFinpartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finpartition (Finset.univ : Finset V)) :
    partitionEnergy G (vertexPartitionOfFinpartition R) =
      weightedEnergy G R := by
  classical
  simp only [partitionEnergy, pairWeight, VertexPartition.partSize,
    vertexPartitionOfFinpartition, density_eq_edgeDensity]
  calc
    _ = ∑ i : Fin R.parts.card, ∑ B : R.parts,
        (((R.parts.equivFin.symm i).1.card : ℝ) * (B.1.card : ℝ)) /
            (Fintype.card V : ℝ) ^ 2 *
          (G.edgeDensity (R.parts.equivFin.symm i).1 B.1 : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using
        (Equiv.sum_comp R.parts.equivFin.symm
          (fun B : R.parts =>
            (((R.parts.equivFin.symm i).1.card : ℝ) * (B.1.card : ℝ)) /
                (Fintype.card V : ℝ) ^ 2 *
              (G.edgeDensity (R.parts.equivFin.symm i).1 B.1 : ℝ) ^ 2))
    _ = ∑ A : R.parts, ∑ B : R.parts,
        ((A.1.card : ℝ) * (B.1.card : ℝ)) /
            (Fintype.card V : ℝ) ^ 2 *
          (G.edgeDensity A.1 B.1 : ℝ) ^ 2 := by
      simpa using
        (Equiv.sum_comp R.parts.equivFin.symm
          (fun A : R.parts => ∑ B : R.parts,
            ((A.1.card : ℝ) * (B.1.card : ℝ)) /
                (Fintype.card V : ℝ) ^ 2 *
              (G.edgeDensity A.1 B.1 : ℝ) ^ 2))
    _ = weightedEnergy G R := by
      unfold weightedEnergy
      rw [Finset.univ_eq_attach]
      calc
        _ = ∑ A ∈ R.parts.attach, ∑ B ∈ R.parts,
            ((A.1.card : ℝ) * (B.card : ℝ)) /
                (Fintype.card V : ℝ) ^ 2 *
              (G.edgeDensity A.1 B : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro A _
          exact Finset.sum_attach R.parts
            (fun B : Finset V =>
              ((A.1.card : ℝ) * (B.card : ℝ)) /
                  (Fintype.card V : ℝ) ^ 2 *
                (G.edgeDensity A.1 B : ℝ) ^ 2)
        _ = _ := Finset.sum_attach R.parts
          (fun A : Finset V => ∑ B ∈ R.parts,
            ((A.card : ℝ) * (B.card : ℝ)) /
                (Fintype.card V : ℝ) ^ 2 *
              (G.edgeDensity A B : ℝ) ^ 2)

private lemma part_injective
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) : Function.Injective P.part := by
  intro i j hij
  by_contra hne
  obtain ⟨v, hv⟩ := P.nonempty_part i
  exact Finset.disjoint_left.mp (P.pairwise_disjoint i j hne)
    hv (hij ▸ hv)

/-- Forget the labels on an indexed vertex partition. -/
private noncomputable def finpartitionOfVertexPartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  refine Finpartition.ofExistsUnique
    (Finset.univ.image P.part) (fun A _ => Finset.subset_univ A) ?_ ?_
  · intro v _
    obtain ⟨i, hvi⟩ := P.covers v
    refine ⟨P.part i, ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hvi⟩, ?_⟩
    intro A hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA.1
    apply congrArg P.part
    by_contra hij
    exact Finset.disjoint_left.mp (P.pairwise_disjoint j i hij)
      hA.2 hvi
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact (P.nonempty_part i).ne_empty hi

@[simp] private lemma finpartitionOfVertexPartition_parts
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    (finpartitionOfVertexPartition P).parts = Finset.univ.image P.part :=
  rfl

private lemma card_finpartitionOfVertexPartition_parts
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    (finpartitionOfVertexPartition P).parts.card = P.partCount := by
  classical
  rw [finpartitionOfVertexPartition_parts,
    Finset.card_image_of_injective _ (part_injective P), Finset.card_univ,
    Fintype.card_fin]

private noncomputable def witnessSets
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (R : Finpartition (Finset.univ : Finset V)) (A : Finset V) :
    Finset (Finset V) :=
  R.parts.image (fun B => G.nonuniformWitness ε A B)

private noncomputable def witnessRefinement
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (R : Finpartition (Finset.univ : Finset V))
    (A : Finset V) : Finpartition A :=
  Finpartition.atomise A (witnessSets G ε R A)

private noncomputable def incrementFinpartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (R : Finpartition (Finset.univ : Finset V)) :
    Finpartition (Finset.univ : Finset V) :=
  R.bind fun A _ => witnessRefinement G ε R A

/-- Weighted finite variance, with one distinguished subfamily. -/
private lemma weighted_variance_increment
    {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (hst : s ⊆ t)
    (w z : ι → ℝ) (hw : ∀ i ∈ t, 0 < w i)
    (W Ws d ds : ℝ)
    (hW : ∑ i ∈ t, w i = W)
    (hmean : ∑ i ∈ t, w i * z i = W * d)
    (hWs : ∑ i ∈ s, w i = Ws)
    (hsmean : ∑ i ∈ s, w i * z i = Ws * ds)
    (hWspos : 0 < Ws) :
    W * d ^ 2 + Ws * (ds - d) ^ 2 ≤
      ∑ i ∈ t, w i * z i ^ 2 := by
  have hcauchy := Finset.sq_sum_div_le_sum_sq_div
    (R := ℝ) s (fun i => w i * (z i - d))
    (g := w) (fun i hi => hw i (hst hi))
  have hsubmean :
      ∑ i ∈ s, w i * (z i - d) = Ws * (ds - d) := by
    calc
      _ = (∑ i ∈ s, w i * z i) - d * ∑ i ∈ s, w i := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = _ := by rw [hsmean, hWs]; ring
  have hcauchy' :
      Ws * (ds - d) ^ 2 ≤ ∑ i ∈ s, w i * (z i - d) ^ 2 := by
    rw [hsubmean, hWs] at hcauchy
    have hcancel (i : ι) (hi : i ∈ s) :
        (w i * (z i - d)) ^ 2 / w i = w i * (z i - d) ^ 2 := by
      have hwi : w i ≠ 0 := (hw i (hst hi)).ne'
      field_simp
    have hsumcancel :
        (∑ i ∈ s, (w i * (z i - d)) ^ 2 / w i) =
          ∑ i ∈ s, w i * (z i - d) ^ 2 := by
      apply Finset.sum_congr rfl
      exact hcancel
    change (Ws * (ds - d)) ^ 2 / Ws ≤
      ∑ i ∈ s, (w i * (z i - d)) ^ 2 / w i at hcauchy
    rw [hsumcancel] at hcauchy
    calc
      _ = (Ws * (ds - d)) ^ 2 / Ws := by field_simp
      _ ≤ _ := hcauchy
  have hsubset :
      ∑ i ∈ s, w i * (z i - d) ^ 2 ≤
        ∑ i ∈ t, w i * (z i - d) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hst
      (fun i _ _ => mul_nonneg (hw i ‹i ∈ t›).le (sq_nonneg _))
  have hvariance :
      ∑ i ∈ t, w i * (z i - d) ^ 2 =
        (∑ i ∈ t, w i * z i ^ 2) - W * d ^ 2 := by
    calc
      _ = ∑ i ∈ t,
          (w i * z i ^ 2 - 2 * d * (w i * z i) + d ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i ∈ t, w i * z i ^ 2) -
          2 * d * (∑ i ∈ t, w i * z i) +
            d ^ 2 * ∑ i ∈ t, w i := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hmean, hW]; ring
  have h := hcauchy'.trans hsubset
  rw [hvariance] at h
  linarith

private lemma card_mul_edgeDensity
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.card : ℝ) * (B.card : ℝ) * (G.edgeDensity A B : ℝ) =
      (G.interedges A B).card := by
  rw [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_mul]
  have hA0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  field_simp
  norm_cast
  ring

private lemma sum_cell_weights
    {V : Type u} [DecidableEq V]
    {A B : Finset V} (RA : Finpartition A) (RB : Finpartition B) :
    ∑ ab ∈ RA.parts ×ˢ RB.parts,
        ((ab.1.card : ℝ) * (ab.2.card : ℝ)) =
      (A.card : ℝ) * (B.card : ℝ) := by
  rw [Finset.sum_product]
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.sum_mul_sum]
  norm_cast
  rw [RA.sum_card_parts, RB.sum_card_parts]

private lemma sum_cell_weighted_density
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (RA : Finpartition A) (RB : Finpartition B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∑ ab ∈ RA.parts ×ˢ RB.parts,
        ((ab.1.card : ℝ) * (ab.2.card : ℝ)) *
          (G.edgeDensity ab.1 ab.2 : ℝ) =
      (A.card : ℝ) * (B.card : ℝ) * (G.edgeDensity A B : ℝ) := by
  calc
    _ = ∑ ab ∈ RA.parts ×ˢ RB.parts,
        ((G.interedges ab.1 ab.2).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro ab hab
      exact card_mul_edgeDensity G ab.1 ab.2
        (RA.nonempty_of_mem_parts (Finset.mem_product.mp hab).1)
        (RB.nonempty_of_mem_parts (Finset.mem_product.mp hab).2)
    _ = ((G.interedges A B).card : ℝ) := by
      norm_cast
      exact (Rel.card_interedges_finpartition G.Adj RA RB).symm
    _ = _ := (card_mul_edgeDensity G A B hA hB).symm

private lemma coarse_pair_le_cells
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (RA : Finpartition A) (RB : Finpartition B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.card : ℝ) * (B.card : ℝ) * (G.edgeDensity A B : ℝ) ^ 2 ≤
      ∑ ab ∈ RA.parts ×ˢ RB.parts,
        ((ab.1.card : ℝ) * (ab.2.card : ℝ)) *
          (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2 := by
  let t := RA.parts ×ˢ RB.parts
  let w : Finset V × Finset V → ℝ :=
    fun ab => (ab.1.card : ℝ) * (ab.2.card : ℝ)
  let z : Finset V × Finset V → ℝ :=
    fun ab => (G.edgeDensity ab.1 ab.2 : ℝ)
  have hw : ∀ ab ∈ t, 0 < w ab := by
    intro ab hab
    exact mul_pos
      (by exact_mod_cast (RA.nonempty_of_mem_parts (Finset.mem_product.mp hab).1).card_pos)
      (by exact_mod_cast (RB.nonempty_of_mem_parts (Finset.mem_product.mp hab).2).card_pos)
  have h := weighted_variance_increment t t (fun _ h => h) w z hw
    ((A.card : ℝ) * (B.card : ℝ))
    ((A.card : ℝ) * (B.card : ℝ))
    (G.edgeDensity A B : ℝ) (G.edgeDensity A B : ℝ)
    (sum_cell_weights RA RB)
    (sum_cell_weighted_density G RA RB hA hB)
    (sum_cell_weights RA RB)
    (sum_cell_weighted_density G RA RB hA hB)
    (mul_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hB.card_pos))
  simpa [t, w, z] using h

private noncomputable def witnessSubpartition
    {V : Type u} [DecidableEq V]
    {A : Finset V} {F : Finset (Finset V)}
    (X : Finset V) (hXF : X ∈ F) (hXA : X ⊆ A) :
    Finpartition X :=
  Finpartition.ofSubset (Finpartition.atomise A F)
    (Finset.filter_subset _ _)
    (by
      rw [Finset.sup_eq_biUnion]
      exact Finpartition.biUnion_filter_atomise hXF hXA)

private lemma irregular_pair_increment
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (FA FB : Finset (Finset V))
    {X Y : Finset V}
    (hXFA : X ∈ FA) (hYFB : Y ∈ FB)
    (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (hXcard : (A.card : ℝ) * ε ≤ (X.card : ℝ))
    (hYcard : (B.card : ℝ) * ε ≤ (Y.card : ℝ))
    (hdiff : ε ≤
      |(G.edgeDensity X Y : ℝ) - (G.edgeDensity A B : ℝ)|) :
    (A.card : ℝ) * (B.card : ℝ) *
          ((G.edgeDensity A B : ℝ) ^ 2 + ε ^ 4) ≤
      ∑ ab ∈ (Finpartition.atomise A FA).parts ×ˢ
          (Finpartition.atomise B FB).parts,
        ((ab.1.card : ℝ) * (ab.2.card : ℝ)) *
          (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2 := by
  let RA := Finpartition.atomise A FA
  let RB := Finpartition.atomise B FB
  let RX := witnessSubpartition X hXFA hXA
  let RY := witnessSubpartition Y hYFB hYB
  let t := RA.parts ×ˢ RB.parts
  let s := RX.parts ×ˢ RY.parts
  let w : Finset V × Finset V → ℝ :=
    fun ab => (ab.1.card : ℝ) * (ab.2.card : ℝ)
  let z : Finset V × Finset V → ℝ :=
    fun ab => (G.edgeDensity ab.1 ab.2 : ℝ)
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
    have : 0 < (X.card : ℝ) := (mul_pos hApos hε).trans_le hXcard
    exact_mod_cast this
  have hY : Y.Nonempty := by
    apply Finset.card_pos.mp
    have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
    have : 0 < (Y.card : ℝ) := (mul_pos hBpos hε).trans_le hYcard
    exact_mod_cast this
  have hst : s ⊆ t := by
    dsimp [s, t, RX, RY, RA, RB, witnessSubpartition]
    exact Finset.product_subset_product
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hw : ∀ ab ∈ t, 0 < w ab := by
    intro ab hab
    exact mul_pos
      (by exact_mod_cast (RA.nonempty_of_mem_parts (Finset.mem_product.mp hab).1).card_pos)
      (by exact_mod_cast (RB.nonempty_of_mem_parts (Finset.mem_product.mp hab).2).card_pos)
  have hvar := weighted_variance_increment s t hst w z hw
    ((A.card : ℝ) * (B.card : ℝ))
    ((X.card : ℝ) * (Y.card : ℝ))
    (G.edgeDensity A B : ℝ) (G.edgeDensity X Y : ℝ)
    (sum_cell_weights RA RB)
    (sum_cell_weighted_density G RA RB hA hB)
    (sum_cell_weights RX RY)
    (sum_cell_weighted_density G RX RY hX hY)
    (mul_pos (by exact_mod_cast hX.card_pos) (by exact_mod_cast hY.card_pos))
  have hweight :
      (A.card : ℝ) * (B.card : ℝ) * ε ^ 4 ≤
        (X.card : ℝ) * (Y.card : ℝ) *
          ((G.edgeDensity X Y : ℝ) - (G.edgeDensity A B : ℝ)) ^ 2 := by
    have hcards :
        (A.card : ℝ) * (B.card : ℝ) * ε ^ 2 ≤
          (X.card : ℝ) * (Y.card : ℝ) := by
      calc
        _ = ((A.card : ℝ) * ε) * ((B.card : ℝ) * ε) := by ring
        _ ≤ _ := mul_le_mul hXcard hYcard
          (mul_nonneg (by positivity) hε.le) (by positivity)
    have hsquare : ε ^ 2 ≤
        ((G.edgeDensity X Y : ℝ) - (G.edgeDensity A B : ℝ)) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ hε.le (abs_nonneg _)).2 hdiff
    calc
      _ = ((A.card : ℝ) * (B.card : ℝ) * ε ^ 2) * ε ^ 2 := by ring
      _ ≤ ((X.card : ℝ) * (Y.card : ℝ)) *
          ((G.edgeDensity X Y : ℝ) - (G.edgeDensity A B : ℝ)) ^ 2 :=
        mul_le_mul hcards hsquare (sq_nonneg ε)
          (mul_nonneg (by positivity) (by positivity))
  have hmain := add_le_add_left hweight
    ((A.card : ℝ) * (B.card : ℝ) * (G.edgeDensity A B : ℝ) ^ 2)
  calc
    _ = (A.card : ℝ) * (B.card : ℝ) * (G.edgeDensity A B : ℝ) ^ 2 +
        (A.card : ℝ) * (B.card : ℝ) * ε ^ 4 := by ring
    _ ≤ (A.card : ℝ) * (B.card : ℝ) * (G.edgeDensity A B : ℝ) ^ 2 +
        (X.card : ℝ) * (Y.card : ℝ) *
          ((G.edgeDensity X Y : ℝ) - (G.edgeDensity A B : ℝ)) ^ 2 := by
      simpa [add_comm] using hmain
    _ ≤ _ := by simpa [RA, RB, RX, RY, s, t, w, z] using hvar

private lemma regularPair_of_isUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : G.IsUniform ε A B) : IsRegularPair G ε A B := by
  refine ⟨hA, hB, ?_⟩
  intro X Y hX hY
  have hu := h hX.1 hY.1 (by simpa [mul_comm] using hX.2)
    (by simpa [mul_comm] using hY.2)
  simpa only [density_eq_edgeDensity] using hu.le

private noncomputable def rawEnergy
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finpartition (Finset.univ : Finset V)) : ℝ :=
  ∑ A ∈ R.parts, ∑ B ∈ R.parts,
    ((A.card : ℝ) * (B.card : ℝ)) *
      (G.edgeDensity A B : ℝ) ^ 2

private lemma weightedEnergy_eq_rawEnergy_div
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finpartition (Finset.univ : Finset V)) :
    weightedEnergy G R = rawEnergy G R / (Fintype.card V : ℝ) ^ 2 := by
  unfold weightedEnergy rawEnergy
  calc
    _ = ∑ A ∈ R.parts, ∑ B ∈ R.parts,
        (((A.card : ℝ) * (B.card : ℝ)) *
          (G.edgeDensity A B : ℝ) ^ 2) /
            (Fintype.card V : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = ∑ A ∈ R.parts,
        (∑ B ∈ R.parts,
          ((A.card : ℝ) * (B.card : ℝ)) *
            (G.edgeDensity A B : ℝ) ^ 2) /
              (Fintype.card V : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_div]
    _ = _ := (Finset.sum_div R.parts
      (fun A => ∑ B ∈ R.parts,
        ((A.card : ℝ) * (B.card : ℝ)) *
          (G.edgeDensity A B : ℝ) ^ 2)
      ((Fintype.card V : ℝ) ^ 2)).symm

private lemma weightedEnergy_finpartitionOfVertexPartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : VertexPartition V) :
    weightedEnergy G (finpartitionOfVertexPartition P) =
      partitionEnergy G P := by
  classical
  unfold weightedEnergy partitionEnergy
  rw [finpartitionOfVertexPartition_parts]
  rw [Finset.sum_image (fun _ _ _ _ h => part_injective P h)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image (fun _ _ _ _ h => part_injective P h)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairWeight, VertexPartition.partSize, density_eq_edgeDensity]

private lemma sum_increment_parts
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (R : Finpartition (Finset.univ : Finset V))
    (f : Finset V → ℝ) :
    ∑ X ∈ (incrementFinpartition G ε R).parts, f X =
      ∑ A ∈ R.parts, ∑ X ∈ (witnessRefinement G ε R A).parts, f X := by
  classical
  have hdisj :
      ((R.parts.attach : Finset R.parts) : Set R.parts).PairwiseDisjoint
        (fun A : R.parts => (witnessRefinement G ε R A.1).parts) := by
    intro A _ B _ hAB
    rw [Function.onFun, Finset.disjoint_left]
    intro X hXA hXB
    obtain ⟨v, hv⟩ :=
      (witnessRefinement G ε R A.1).nonempty_of_mem_parts hXA
    have hvA := (witnessRefinement G ε R A.1).le hXA hv
    have hvB := (witnessRefinement G ε R B.1).le hXB hv
    exact hAB (Subtype.ext (R.eq_of_mem_parts A.2 B.2 hvA hvB))
  rw [incrementFinpartition, Finpartition.bind_parts,
    Finset.sum_biUnion hdisj]
  exact Finset.sum_attach R.parts
    (fun A : Finset V =>
      ∑ X ∈ (witnessRefinement G ε R A).parts, f X)

private lemma rawEnergy_increment_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (R : Finpartition (Finset.univ : Finset V)) :
    rawEnergy G (incrementFinpartition G ε R) =
      ∑ A ∈ R.parts, ∑ B ∈ R.parts,
        ∑ ab ∈ (witnessRefinement G ε R A).parts ×ˢ
            (witnessRefinement G ε R B).parts,
          ((ab.1.card : ℝ) * (ab.2.card : ℝ)) *
            (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2 := by
  classical
  unfold rawEnergy
  rw [sum_increment_parts G ε R]
  apply Finset.sum_congr rfl
  intro A _
  calc
    _ = ∑ X ∈ (witnessRefinement G ε R A).parts,
        ∑ B ∈ R.parts, ∑ Y ∈ (witnessRefinement G ε R B).parts,
          ((X.card : ℝ) * (Y.card : ℝ)) *
            (G.edgeDensity X Y : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro X _
      exact sum_increment_parts G ε R _
    _ = ∑ B ∈ R.parts, ∑ X ∈ (witnessRefinement G ε R A).parts,
        ∑ Y ∈ (witnessRefinement G ε R B).parts,
          ((X.card : ℝ) * (Y.card : ℝ)) *
            (G.edgeDensity X Y : ℝ) ^ 2 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B _
      rw [Finset.sum_product]

private lemma rawEnergy_finpartitionOfVertexPartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : VertexPartition V) :
    rawEnergy G (finpartitionOfVertexPartition P) =
      ∑ i : Fin P.partCount, ∑ j : Fin P.partCount,
        ((P.part i).card : ℝ) * ((P.part j).card : ℝ) *
          (G.edgeDensity (P.part i) (P.part j) : ℝ) ^ 2 := by
  classical
  unfold rawEnergy
  rw [finpartitionOfVertexPartition_parts]
  rw [Finset.sum_image (fun _ _ _ _ h => part_injective P h)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image (fun _ _ _ _ h => part_injective P h)]

private lemma rawEnergy_increment_indexed
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (P : VertexPartition V) :
    rawEnergy G (incrementFinpartition G ε (finpartitionOfVertexPartition P)) =
      ∑ i : Fin P.partCount, ∑ j : Fin P.partCount,
        ∑ ab ∈
            (witnessRefinement G ε (finpartitionOfVertexPartition P) (P.part i)).parts ×ˢ
            (witnessRefinement G ε (finpartitionOfVertexPartition P) (P.part j)).parts,
          ((ab.1.card : ℝ) * (ab.2.card : ℝ)) *
            (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2 := by
  classical
  rw [rawEnergy_increment_eq]
  rw [finpartitionOfVertexPartition_parts]
  rw [Finset.sum_image (fun _ _ _ _ h => part_injective P h)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image (fun _ _ _ _ h => part_injective P h)]

private lemma sum_part_cards_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : VertexPartition V) :
    ∑ i : Fin P.partCount, (P.part i).card = Fintype.card V := by
  have hdisj :
      ((Finset.univ : Finset (Fin P.partCount)) : Set (Fin P.partCount)).PairwiseDisjoint
        P.part := by
    intro i _ j _ hij
    exact P.pairwise_disjoint i j hij
  have hcover :
      (Finset.univ : Finset (Fin P.partCount)).biUnion P.part =
        (Finset.univ : Finset V) := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => P.covers v⟩
  rw [← Finset.card_biUnion hdisj, hcover, Finset.card_univ]

private lemma irregular_bonus_lower_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : ℝ) (hε : 0 < ε)
    (P : VertexPartition V) (hEq : P.Equitable)
    (hnot : ¬ IsRegularPartition G ε P) :
    (Fintype.card V : ℝ) ^ 2 * ε ^ 5 / 4 ≤
      ∑ p ∈ irregularPairIndices G ε P,
        ((P.part p.1).card : ℝ) * ((P.part p.2).card : ℝ) * ε ^ 4 := by
  classical
  have hk : 0 < P.partCount := by
    by_contra hk
    have hk0 : P.partCount = 0 := Nat.eq_zero_of_not_pos hk
    have hempty : irregularPairIndices G ε P = ∅ := by
      ext p
      simp only [irregularPairIndices, Finset.mem_filter,
        Finset.notMem_empty, iff_false]
      intro _
      have hp := p.1.isLt
      omega
    apply hnot
    rw [IsRegularPartition, irregularPairCount, hempty]
    simp [hk0]
  have hpart (i : Fin P.partCount) :
      Fintype.card V ≤ P.partCount * (2 * (P.part i).card) := by
    calc
      Fintype.card V = ∑ j : Fin P.partCount, (P.part j).card :=
        (sum_part_cards_eq P).symm
      _ ≤ ∑ _j : Fin P.partCount, 2 * (P.part i).card := by
        apply Finset.sum_le_sum
        intro j _
        have hij := (hEq j i).1
        simp only [VertexPartition.partSize] at hij
        have hi : 1 ≤ (P.part i).card := (P.nonempty_part i).card_pos
        omega
      _ = P.partCount * (2 * (P.part i).card) := by simp
  have hterm (p : Fin P.partCount × Fin P.partCount)
      (_hp : p ∈ irregularPairIndices G ε P) :
      (Fintype.card V : ℝ) ^ 2 * ε ^ 4 ≤
        4 * (P.partCount : ℝ) ^ 2 *
          (((P.part p.1).card : ℝ) * ((P.part p.2).card : ℝ) * ε ^ 4) := by
    have hi : (Fintype.card V : ℝ) ≤
        2 * (P.partCount : ℝ) * ((P.part p.1).card : ℝ) := by
      have hi' : (Fintype.card V : ℝ) ≤
          (P.partCount : ℝ) * (2 * ((P.part p.1).card : ℝ)) := by
        exact_mod_cast hpart p.1
      simpa [mul_comm, mul_left_comm, mul_assoc] using hi'
    have hj : (Fintype.card V : ℝ) ≤
        2 * (P.partCount : ℝ) * ((P.part p.2).card : ℝ) := by
      have hj' : (Fintype.card V : ℝ) ≤
          (P.partCount : ℝ) * (2 * ((P.part p.2).card : ℝ)) := by
        exact_mod_cast hpart p.2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hj'
    have hp := mul_le_mul hi hj (by positivity) (by positivity)
    calc
      _ = ((Fintype.card V : ℝ) * (Fintype.card V : ℝ)) * ε ^ 4 := by ring
      _ ≤ ((2 * (P.partCount : ℝ) * ((P.part p.1).card : ℝ)) *
          (2 * (P.partCount : ℝ) * ((P.part p.2).card : ℝ))) * ε ^ 4 :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by ring
  let bonus : ℝ := ∑ p ∈ irregularPairIndices G ε P,
    ((P.part p.1).card : ℝ) * ((P.part p.2).card : ℝ) * ε ^ 4
  have hsum :
      (irregularPairCount G ε P : ℝ) *
          ((Fintype.card V : ℝ) ^ 2 * ε ^ 4) ≤
        4 * (P.partCount : ℝ) ^ 2 * bonus := by
    calc
      _ = ∑ _p ∈ irregularPairIndices G ε P,
          (Fintype.card V : ℝ) ^ 2 * ε ^ 4 := by
        simp [irregularPairCount, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ irregularPairIndices G ε P,
          4 * (P.partCount : ℝ) ^ 2 *
            (((P.part p.1).card : ℝ) * ((P.part p.2).card : ℝ) * ε ^ 4) :=
        Finset.sum_le_sum hterm
      _ = _ := by
        unfold bonus
        rw [← Finset.mul_sum]
  have hcount :
      ε * (P.partCount : ℝ) ^ 2 < (irregularPairCount G ε P : ℝ) := by
    exact lt_of_not_ge hnot
  have hcountmul :
      (ε * (P.partCount : ℝ) ^ 2) *
          ((Fintype.card V : ℝ) ^ 2 * ε ^ 4) ≤
        (irregularPairCount G ε P : ℝ) *
          ((Fintype.card V : ℝ) ^ 2 * ε ^ 4) :=
    mul_le_mul_of_nonneg_right hcount.le (by positivity)
  have hcombined := hcountmul.trans hsum
  have hk2 : 0 < (P.partCount : ℝ) ^ 2 := by exact_mod_cast (sq_pos_of_pos hk)
  have hcancel :
      (Fintype.card V : ℝ) ^ 2 * ε ^ 5 ≤ 4 * bonus := by
    nlinarith [hcombined]
  dsimp [bonus] at hcancel
  linarith

/--
---
conclusion: Lax18.EnergyIncrement.energy_increment_refinement
---
Every class is atomised simultaneously along the witnesses supplied by its
irregular partners. A weighted variance calculation on each old pair gives
the required global energy increment.
-/
theorem energy_increment_refinement :
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
                          partitionEnergy G Q := by
  classical
  intro ε hε V _ _ G P hEq hnot
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let R := finpartitionOfVertexPartition P
  let S := incrementFinpartition G ε R
  let Q := vertexPartitionOfFinpartition S
  have hRcard : R.parts.card = P.partCount := by
    simpa [R] using card_finpartitionOfVertexPartition_parts P
  have hk : 0 < P.partCount := by
    by_contra hk
    have hk0 : P.partCount = 0 := Nat.eq_zero_of_not_pos hk
    have hempty : irregularPairIndices G ε P = ∅ := by
      ext p
      simp only [irregularPairIndices, Finset.mem_filter,
        Finset.notMem_empty, iff_false]
      intro _
      have hp := p.1.isLt
      omega
    apply hnot
    rw [IsRegularPartition, irregularPairCount, hempty]
    simp [hk0]
  have hVpos : 0 < Fintype.card V := by
    let i : Fin P.partCount := ⟨0, hk⟩
    have hle : (P.part i).card ≤ Fintype.card V :=
      Finset.card_le_card (Finset.subset_univ _)
    exact (P.nonempty_part i).card_pos.trans_le hle
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj : (S.parts.equivFin.symm j).1 ∈ S.parts :=
      (S.parts.equivFin.symm j).2
    obtain ⟨A, hAR, hjA⟩ := by
      simpa [S, incrementFinpartition] using
        (Finpartition.mem_bind.mp hj)
    have hAR' : A ∈ Finset.univ.image P.part := by simpa [R] using hAR
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hAR'
    refine ⟨i, ?_⟩
    exact (witnessRefinement G ε R (P.part i)).le hjA
  · change P.partCount ≤ S.parts.card
    change P.partCount ≤ (incrementFinpartition G ε R).parts.card
    rw [incrementFinpartition, Finpartition.card_bind]
    calc
      P.partCount = ∑ A ∈ R.parts.attach, 1 := by simp [hRcard]
      _ ≤ ∑ A ∈ R.parts.attach,
          (witnessRefinement G ε R A.1).parts.card := by
        apply Finset.sum_le_sum
        intro A _
        exact (witnessRefinement G ε R A.1).parts_nonempty
          (R.ne_empty A.2) |>.card_pos
  · change S.parts.card ≤ P.partCount * 2 ^ P.partCount
    change (incrementFinpartition G ε R).parts.card ≤
      P.partCount * 2 ^ P.partCount
    rw [incrementFinpartition, Finpartition.card_bind]
    calc
      _ ≤ ∑ _A ∈ R.parts.attach, 2 ^ P.partCount := by
        apply Finset.sum_le_sum
        intro A _
        calc
          (witnessRefinement G ε R A.1).parts.card ≤
              2 ^ (witnessSets G ε R A.1).card :=
            Finpartition.card_atomise_le
          _ ≤ 2 ^ P.partCount := by
            have hcard : (witnessSets G ε R A.1).card ≤ P.partCount := by
              change (R.parts.image
                (fun B => G.nonuniformWitness ε A.1 B)).card ≤ P.partCount
              exact Finset.card_image_le.trans_eq hRcard
            exact Nat.pow_le_pow_right (by norm_num) hcard
      _ = _ := by simp [hRcard]
  · let coarse : Fin P.partCount × Fin P.partCount → ℝ := fun p =>
      ((P.part p.1).card : ℝ) * ((P.part p.2).card : ℝ) *
        (G.edgeDensity (P.part p.1) (P.part p.2) : ℝ) ^ 2
    let gain : Fin P.partCount × Fin P.partCount → ℝ := fun p =>
      ((P.part p.1).card : ℝ) * ((P.part p.2).card : ℝ) * ε ^ 4
    let fine : Fin P.partCount × Fin P.partCount → ℝ := fun p =>
      ∑ ab ∈
          (witnessRefinement G ε R (P.part p.1)).parts ×ˢ
          (witnessRefinement G ε R (P.part p.2)).parts,
        ((ab.1.card : ℝ) * (ab.2.card : ℝ)) *
          (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2
    have hlocal (p : Fin P.partCount × Fin P.partCount) :
        coarse p +
            (if p ∈ irregularPairIndices G ε P then gain p else 0) ≤
          fine p := by
      by_cases hp : p ∈ irregularPairIndices G ε P
      · have hp' := Finset.mem_filter.mp hp
        have hpir : ¬ IsRegularPair G ε (P.part p.1) (P.part p.2) := hp'.2.2
        have hne : P.part p.1 ≠ P.part p.2 :=
          fun h => (ne_of_lt hp'.2.1) (part_injective P h)
        have hnu : ¬G.IsUniform ε (P.part p.1) (P.part p.2) := by
          intro hu
          exact hpir (regularPair_of_isUniform G ε
            (P.nonempty_part p.1) (P.nonempty_part p.2) hu)
        let X := G.nonuniformWitness ε (P.part p.1) (P.part p.2)
        let Y := G.nonuniformWitness ε (P.part p.2) (P.part p.1)
        have hAin : P.part p.1 ∈ R.parts := by
          simpa [R] using (Finset.mem_image.mpr
            ⟨p.1, Finset.mem_univ p.1, rfl⟩)
        have hBin : P.part p.2 ∈ R.parts := by
          simpa [R] using (Finset.mem_image.mpr
            ⟨p.2, Finset.mem_univ p.2, rfl⟩)
        have hXmem : X ∈ witnessSets G ε R (P.part p.1) :=
          Finset.mem_image.mpr ⟨P.part p.2, hBin, rfl⟩
        have hYmem : Y ∈ witnessSets G ε R (P.part p.2) :=
          Finset.mem_image.mpr ⟨P.part p.1, hAin, rfl⟩
        have hspec : ε ≤
            |(G.edgeDensity X Y : ℝ) -
              (G.edgeDensity (P.part p.1) (P.part p.2) : ℝ)| := by
          simpa [X, Y, Rat.cast_abs, Rat.cast_sub] using
            (G.nonuniformWitness_spec hne hnu)
        have hinc := irregular_pair_increment G ε hε
          (P.nonempty_part p.1) (P.nonempty_part p.2)
          (witnessSets G ε R (P.part p.1))
          (witnessSets G ε R (P.part p.2))
          hXmem hYmem
          (G.nonuniformWitness_subset hnu)
          (G.nonuniformWitness_subset (fun hu => hnu hu.symm))
          (G.le_card_nonuniformWitness hnu)
          (G.le_card_nonuniformWitness (fun hu => hnu hu.symm))
          hspec
        rw [if_pos hp]
        change coarse p + gain p ≤ fine p
        dsimp [coarse, gain, fine, witnessRefinement]
        convert hinc using 1 <;> ring
      · have hbase := coarse_pair_le_cells G
          (witnessRefinement G ε R (P.part p.1))
          (witnessRefinement G ε R (P.part p.2))
          (P.nonempty_part p.1) (P.nonempty_part p.2)
        rw [if_neg hp]
        simpa [coarse, fine] using hbase
    let allPairs : Finset (Fin P.partCount × Fin P.partCount) :=
      Finset.univ ×ˢ Finset.univ
    have hsumlocal :
        ∑ p ∈ allPairs,
            (coarse p +
              if p ∈ irregularPairIndices G ε P then gain p else 0) ≤
          ∑ p ∈ allPairs, fine p :=
      Finset.sum_le_sum (fun p _ => hlocal p)
    have hirrsub : irregularPairIndices G ε P ⊆ allPairs := by
      intro p _
      simp [allPairs]
    have hgainSum :
        (∑ p ∈ allPairs,
          if p ∈ irregularPairIndices G ε P then gain p else 0) =
        ∑ p ∈ irregularPairIndices G ε P, gain p := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hirrsub h, h⟩⟩
      · intro p _
        rfl
    have hraw :
        rawEnergy G R +
            (∑ p ∈ irregularPairIndices G ε P, gain p) ≤
          rawEnergy G S := by
      rw [rawEnergy_finpartitionOfVertexPartition G P]
      rw [rawEnergy_increment_indexed G ε P]
      change
        (∑ i : Fin P.partCount, ∑ j : Fin P.partCount, coarse (i, j)) +
            (∑ p ∈ irregularPairIndices G ε P, gain p) ≤
          ∑ i : Fin P.partCount, ∑ j : Fin P.partCount, fine (i, j)
      rw [← Finset.sum_product, ← Finset.sum_product]
      change (∑ p ∈ allPairs, coarse p) +
          (∑ p ∈ irregularPairIndices G ε P, gain p) ≤
        ∑ p ∈ allPairs, fine p
      rw [← hgainSum, ← Finset.sum_add_distrib]
      exact hsumlocal
    have hbonus := irregular_bonus_lower_bound G ε hε P hEq hnot
    change (Fintype.card V : ℝ) ^ 2 * ε ^ 5 / 4 ≤
      ∑ p ∈ irregularPairIndices G ε P, gain p at hbonus
    have hrawinc :
        rawEnergy G R + (Fintype.card V : ℝ) ^ 2 * ε ^ 5 / 4 ≤
          rawEnergy G S :=
      (add_le_add_right hbonus _).trans hraw
    calc
      partitionEnergy G P + ε ^ 5 / 4 =
          rawEnergy G R / (Fintype.card V : ℝ) ^ 2 + ε ^ 5 / 4 := by
        rw [← weightedEnergy_eq_rawEnergy_div G R,
          weightedEnergy_finpartitionOfVertexPartition G P]
      _ = (rawEnergy G R +
          (Fintype.card V : ℝ) ^ 2 * ε ^ 5 / 4) /
            (Fintype.card V : ℝ) ^ 2 := by
        have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hVpos.ne'
        field_simp
      _ ≤ rawEnergy G S / (Fintype.card V : ℝ) ^ 2 := by
        gcongr
      _ = partitionEnergy G Q := by
        rw [← weightedEnergy_eq_rawEnergy_div G S,
          ← partitionEnergy_vertexPartitionOfFinpartition G S]

end Lax18Proofs
