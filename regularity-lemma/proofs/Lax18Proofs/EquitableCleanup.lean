import Lax18.EquitableCleanup
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Lax18Proofs

open Finset Fintype
open scoped BigOperators
open Lax18.EdgeDensity
open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy

universe u

namespace EquitableCleanup

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

private lemma part_injective (P : VertexPartition V) : Function.Injective P.part := by
  intro i j hij
  by_contra hne
  obtain ⟨v, hv⟩ := P.nonempty_part i
  have hd := P.pairwise_disjoint i j hne
  exact (Finset.disjoint_left.mp hd hv) (hij ▸ hv)

/-- The unordered collection of classes of an indexed partition. -/
private def partSet (P : VertexPartition V) : Finset (Finset V) :=
  Finset.univ.image P.part

/-- Forget the indexing of a vertex partition. -/
private noncomputable def toFinpartition (P : VertexPartition V) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  refine Finpartition.ofExistsUnique (partSet P) ?_ ?_ ?_
  · intro A hA v hv
    simp
  · intro v hv
    obtain ⟨i, hi⟩ := P.covers v
    refine ⟨P.part i, ⟨?_, hi⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · intro B hB
      obtain ⟨hB, hvB⟩ := hB
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hB
      by_cases hji : j = i
      · simpa [hji]
      · have hd := P.pairwise_disjoint j i hji
        exact False.elim ((Finset.disjoint_left.mp hd hvB) hi)
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact (P.nonempty_part i).ne_empty hi

@[simp] private lemma parts_toFinpartition (P : VertexPartition V) :
    (toFinpartition P).parts = partSet P := rfl

/-- Put the canonical `Fin` indexing on a finpartition. -/
private noncomputable def fromFinpartition
    (P : Finpartition (Finset.univ : Finset V)) : VertexPartition V where
  partCount := P.parts.card
  part i := ((P.parts.equivFin).symm i : P.parts).1
  nonempty_part i := P.nonempty_of_mem_parts ((P.parts.equivFin).symm i).2
  pairwise_disjoint i j hij := by
    apply P.disjoint ((P.parts.equivFin).symm i).2 ((P.parts.equivFin).symm j).2
    intro h
    apply hij
    exact (P.parts.equivFin).symm.injective (Subtype.ext h)
  covers v := by
    obtain ⟨A, hA, hv⟩ := P.exists_mem (Finset.mem_univ v)
    refine ⟨P.parts.equivFin ⟨A, hA⟩, ?_⟩
    simpa using hv

private noncomputable def rawPairTerm (G : SimpleGraph V) (n : ℕ)
    (A B : Finset V) : ℝ :=
  (edgeCountBetween G A B : ℝ) ^ 2 /
    ((n : ℝ) ^ 2 * (A.card : ℝ) * (B.card : ℝ))

private noncomputable def rawEnergy (G : SimpleGraph V) (n : ℕ)
    (S : Finset (Finset V)) : ℝ :=
  ∑ A ∈ S, ∑ B ∈ S, rawPairTerm G n A B

private noncomputable def rawCrossEnergy (G : SimpleGraph V) (n : ℕ)
    (S T : Finset (Finset V)) : ℝ :=
  ∑ A ∈ S, ∑ B ∈ T, rawPairTerm G n A B

private lemma pairWeight_mul_density_sq_eq_rawPairTerm
    (G : SimpleGraph V) (P : VertexPartition V)
    (i j : Fin P.partCount) :
    pairWeight P i j * density G (P.part i) (P.part j) ^ 2 =
      rawPairTerm G (Fintype.card V) (P.part i) (P.part j) := by
  have hi : (P.part i).card ≠ 0 := (P.nonempty_part i).card_ne_zero
  have hj : (P.part j).card ≠ 0 := (P.nonempty_part j).card_ne_zero
  rw [density, if_neg (not_or_intro hi hj)]
  unfold pairWeight VertexPartition.partSize rawPairTerm
  field_simp [hi, hj]
  <;> ring

private lemma partitionEnergy_eq_rawEnergy_partSet
    (G : SimpleGraph V) (P : VertexPartition V) :
    partitionEnergy G P = rawEnergy G (Fintype.card V) (partSet P) := by
  classical
  rw [partitionEnergy, rawEnergy, partSet]
  simp_rw [pairWeight_mul_density_sq_eq_rawPairTerm]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_image]
    exact (part_injective P).injOn
  · exact (part_injective P).injOn

private lemma partSet_fromFinpartition
    (P : Finpartition (Finset.univ : Finset V)) :
    partSet (fromFinpartition P) = P.parts := by
  classical
  ext A
  constructor
  · rintro hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    exact ((P.parts.equivFin).symm i).2
  · intro hA
    refine Finset.mem_image.mpr ⟨P.parts.equivFin ⟨A, hA⟩, Finset.mem_univ _, ?_⟩
    simp [fromFinpartition]

private lemma partitionEnergy_fromFinpartition
    (G : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)) :
    partitionEnergy G (fromFinpartition P) =
      rawEnergy G (Fintype.card V) P.parts := by
  rw [partitionEnergy_eq_rawEnergy_partSet, partSet_fromFinpartition]

private lemma edgeCountBetween_eq_sum_partition
    (G : SimpleGraph V) {A B : Finset V}
    (PA : Finpartition A) (PB : Finpartition B) :
    (edgeCountBetween G A B : ℝ) =
      ∑ XY ∈ PA.parts ×ˢ PB.parts,
        (edgeCountBetween G XY.1 XY.2 : ℝ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have h := Rel.card_interedges_finpartition G.Adj PA PB
  exact_mod_cast h

private lemma sum_card_mul_card_partition {A B : Finset V}
    (PA : Finpartition A) (PB : Finpartition B) :
    ∑ XY ∈ PA.parts ×ˢ PB.parts,
        (XY.1.card : ℝ) * (XY.2.card : ℝ) =
      (A.card : ℝ) * (B.card : ℝ) := by
  rw [Finset.sum_product]
  simp only [Prod.fst, Prod.snd]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  norm_cast
  exact congrArg₂ (fun x y : ℕ ↦ x * y) PA.sum_card_parts PB.sum_card_parts

private lemma rawPairTerm_le_cross_of_partitions
    (G : SimpleGraph V) (n : ℕ) {A B : Finset V}
    (PA : Finpartition A) (PB : Finpartition B) :
    rawPairTerm G n A B ≤ rawCrossEnergy G n PA.parts PB.parts := by
  classical
  let I := PA.parts ×ˢ PB.parts
  let f : Finset V × Finset V → ℝ :=
    fun XY ↦ (edgeCountBetween G XY.1 XY.2 : ℝ)
  let g : Finset V × Finset V → ℝ :=
    fun XY ↦ (XY.1.card : ℝ) * (XY.2.card : ℝ)
  have hg : ∀ XY ∈ I, 0 < g XY := by
    intro XY hXY
    rw [Finset.mem_product] at hXY
    exact mul_pos (mod_cast PA.nonempty_of_mem_parts hXY.1 |>.card_pos)
      (mod_cast PB.nonempty_of_mem_parts hXY.2 |>.card_pos)
  have htitu := Finset.sq_sum_div_le_sum_sq_div I f hg
  have hcount : (edgeCountBetween G A B : ℝ) = ∑ XY ∈ I, f XY := by
    simpa [I, f] using edgeCountBetween_eq_sum_partition G PA PB
  have hcard : (A.card : ℝ) * (B.card : ℝ) = ∑ XY ∈ I, g XY := by
    simpa [I, g] using (sum_card_mul_card_partition PA PB).symm
  rw [rawPairTerm, hcount, mul_assoc, hcard]
  calc
    (∑ XY ∈ I, f XY) ^ 2 /
          ((n : ℝ) ^ 2 * ∑ XY ∈ I, g XY) =
        ((∑ XY ∈ I, f XY) ^ 2 / ∑ XY ∈ I, g XY) /
          (n : ℝ) ^ 2 := by ring
    _ ≤ (∑ XY ∈ I, f XY ^ 2 / g XY) / (n : ℝ) ^ 2 := by
      gcongr
    _ = rawCrossEnergy G n PA.parts PB.parts := by
      rw [Finset.sum_div, rawCrossEnergy]
      simp only [I, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro X hX
      apply Finset.sum_congr rfl
      intro Y hY
      simp only [f, g]
      unfold rawPairTerm
      ring

private lemma sum_bind_eq_sum_subtype {A : Finset V}
    (P : Finpartition A) (Q : ∀ X ∈ P.parts, Finpartition X)
    (f : Finset V → ℝ) :
    ∑ X ∈ (P.bind Q).parts, f X =
      ∑ X ∈ P.parts.attach, ∑ Y ∈ (Q X.1 X.2).parts, f Y := by
  simpa [Finpartition.bind] using
    (Finpartition.sum_combine
      (I := P.parts.attach) (fun X : P.parts ↦ Q X.1 X.2)
      P.supIndep.attach f)

private lemma rawEnergy_le_rawEnergy_bind
    (G : SimpleGraph V) (n : ℕ) {A : Finset V}
    (P : Finpartition A) (Q : ∀ X ∈ P.parts, Finpartition X) :
    rawEnergy G n P.parts ≤ rawEnergy G n (P.bind Q).parts := by
  classical
  unfold rawEnergy
  rw [sum_bind_eq_sum_subtype]
  simp_rw [sum_bind_eq_sum_subtype]
  rw [← Finset.sum_attach P.parts
    (fun X ↦ ∑ Y ∈ P.parts, rawPairTerm G n X Y)]
  apply Finset.sum_le_sum
  intro X hX
  rw [← Finset.sum_attach P.parts (fun Y ↦ rawPairTerm G n X.1 Y)]
  calc
    (∑ Y ∈ P.parts.attach, rawPairTerm G n X.1 Y.1) ≤
        ∑ Y ∈ P.parts.attach,
          rawCrossEnergy G n (Q X.1 X.2).parts (Q Y.1 Y.2).parts := by
      apply Finset.sum_le_sum
      intro Y hY
      exact rawPairTerm_le_cross_of_partitions G n (Q X.1 X.2) (Q Y.1 Y.2)
    _ = ∑ x ∈ (Q X.1 X.2).parts,
        ∑ Y ∈ P.parts.attach, ∑ y ∈ (Q Y.1 Y.2).parts,
          rawPairTerm G n x y := by
      simp only [rawCrossEnergy]
      rw [Finset.sum_comm]

private lemma bind_restrict_eq_inf {A : Finset V}
    (P Q : Finpartition A) :
    P.bind (fun X hX ↦ Q.restrict (P.le hX)) = P ⊓ Q := by
  classical
  ext X
  simp only [Finpartition.mem_bind, Finpartition.restrict, Finpartition.parts_inf,
    Finpartition.ofErase_parts, Finset.mem_erase, Finset.mem_image,
    Finset.mem_product]
  constructor
  · rintro ⟨A, hA, hX0, B, hB, hBA⟩
    refine ⟨hX0, ⟨(A, B), ⟨hA, hB⟩, ?_⟩⟩
    simpa [Finset.inf_eq_inter, Finset.inter_comm] using hBA
  · rintro ⟨hX0, ⟨⟨A, B⟩, ⟨hA, hB⟩, hAB⟩⟩
    refine ⟨A, hA, hX0, B, hB, ?_⟩
    simpa [Finset.inf_eq_inter, Finset.inter_comm] using hAB

private noncomputable def pairMass (n : ℕ) (A B : Finset V) : ℝ :=
  ((A.card : ℝ) * (B.card : ℝ)) / (n : ℝ) ^ 2

private lemma pairMass_nonneg (n : ℕ) (A B : Finset V) :
    0 ≤ pairMass n A B := by
  unfold pairMass
  positivity

private lemma edgeCountBetween_le_card_mul (G : SimpleGraph V) (A B : Finset V) :
    edgeCountBetween G A B ≤ A.card * B.card := by
  classical
  unfold edgeCountBetween
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product A B)

private lemma rawPairTerm_nonneg (G : SimpleGraph V) (n : ℕ)
    (A B : Finset V) : 0 ≤ rawPairTerm G n A B := by
  unfold rawPairTerm
  positivity

private lemma rawPairTerm_le_pairMass (G : SimpleGraph V) {n : ℕ}
    (hn : 0 < n) {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) :
    rawPairTerm G n A B ≤ pairMass n A B := by
  have he : (edgeCountBetween G A B : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) := by
    exact_mod_cast edgeCountBetween_le_card_mul G A B
  have he0 : (0 : ℝ) ≤ edgeCountBetween G A B := by positivity
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hB0 : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rawPairTerm pairMass
  rw [div_le_iff₀ (mul_pos (mul_pos (sq_pos_of_pos hn0) hA0) hB0)]
  have hs : (edgeCountBetween G A B : ℝ) ^ 2 ≤
      ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by nlinarith
  calc
    (edgeCountBetween G A B : ℝ) ^ 2 ≤
        ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := hs
    _ = ((A.card : ℝ) * (B.card : ℝ)) / (n : ℝ) ^ 2 *
        ((n : ℝ) ^ 2 * (A.card : ℝ) * (B.card : ℝ)) := by
      field_simp

private lemma rawCrossEnergy_le_pairMass (G : SimpleGraph V) {n : ℕ}
    (hn : 0 < n) {A B : Finset V}
    (PA : Finpartition A) (PB : Finpartition B) :
    rawCrossEnergy G n PA.parts PB.parts ≤ pairMass n A B := by
  classical
  rw [rawCrossEnergy]
  calc
    (∑ X ∈ PA.parts, ∑ Y ∈ PB.parts, rawPairTerm G n X Y) ≤
        ∑ X ∈ PA.parts, ∑ Y ∈ PB.parts, pairMass n X Y := by
      apply Finset.sum_le_sum
      intro X hX
      apply Finset.sum_le_sum
      intro Y hY
      exact rawPairTerm_le_pairMass G hn
        (PA.nonempty_of_mem_parts hX) (PB.nonempty_of_mem_parts hY)
    _ = ∑ XY ∈ PA.parts ×ˢ PB.parts, pairMass n XY.1 XY.2 := by
      rw [Finset.sum_product]
    _ = pairMass n A B := by
      simp_rw [pairMass]
      rw [← Finset.sum_div, sum_card_mul_card_partition PA PB]

private lemma restrict_eq_indiscrete_of_subset {S : Finset V}
    (P : Finpartition S) {A B : Finset V}
    (hA : A ∈ P.parts) (hBS : B ⊆ S) (hB0 : B ≠ ∅) (hBA : B ⊆ A) :
    P.restrict hBS = Finpartition.indiscrete hB0 := by
  classical
  ext X
  simp only [Finpartition.restrict, Finpartition.indiscrete_parts,
    Finset.mem_erase, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨hX0, C, hC, hCX⟩
    by_cases hCA : C = A
    · subst C
      simpa [Finset.inf_eq_inter, Finset.inter_eq_right.mpr hBA] using hCX.symm
    · have hd := P.disjoint hC hA hCA
      exfalso
      apply hX0
      apply le_bot_iff.mp
      rw [← hCX]
      exact (hd.mono_right hBA).le_bot
  · rintro rfl
    refine ⟨hB0, A, hA, ?_⟩
    exact Finset.inf_eq_inter.trans (Finset.inter_eq_right.mpr hBA)

private def GoodFor {S : Finset V} (P : Finpartition S) (B : Finset V) : Prop :=
  ∃ A ∈ P.parts, B ⊆ A

private lemma rawCross_restrict_eq_of_good {S : Finset V}
    (G : SimpleGraph V) (n : ℕ) (P Q : Finpartition S)
    {B C : Finset V} (hB : B ∈ Q.parts) (hC : C ∈ Q.parts)
    (hBg : GoodFor P B) (hCg : GoodFor P C) :
    rawCrossEnergy G n (P.restrict (Q.le hB)).parts
        (P.restrict (Q.le hC)).parts = rawPairTerm G n B C := by
  obtain ⟨A, hA, hBA⟩ := hBg
  obtain ⟨D, hD, hCD⟩ := hCg
  rw [restrict_eq_indiscrete_of_subset P hA (Q.le hB) (Q.ne_bot hB) hBA,
    restrict_eq_indiscrete_of_subset P hD (Q.le hC) (Q.ne_bot hC) hCD]
  simp [rawCrossEnergy]

private noncomputable def badParts {S : Finset V} (P Q : Finpartition S) :
    Finset (Finset V) :=
  Q.parts.filter fun B ↦ ¬ GoodFor P B

private noncomputable def badVertexCount {S : Finset V} (P Q : Finpartition S) : ℕ :=
  ∑ B ∈ badParts P Q, B.card

private lemma rawEnergy_bind_restrict_eq_sum_cross {S : Finset V}
    (G : SimpleGraph V) (n : ℕ) (P Q : Finpartition S) :
    rawEnergy G n
        (Q.bind (fun B hB ↦ P.restrict (Q.le hB))).parts =
      ∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
        rawCrossEnergy G n (P.restrict (Q.le B.2)).parts
          (P.restrict (Q.le C.2)).parts := by
  classical
  unfold rawEnergy
  rw [sum_bind_eq_sum_subtype]
  simp_rw [sum_bind_eq_sum_subtype]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.sum_comm]
  rfl

private lemma cross_restrict_le_with_bad_penalty {S : Finset V}
    (G : SimpleGraph V) {n : ℕ} (hn : 0 < n)
    (P Q : Finpartition S) {B C : Finset V}
    (hB : B ∈ Q.parts) (hC : C ∈ Q.parts) :
    rawCrossEnergy G n (P.restrict (Q.le hB)).parts
        (P.restrict (Q.le hC)).parts ≤
      rawPairTerm G n B C +
        (if ¬ GoodFor P B then pairMass n B C else 0) +
          (if ¬ GoodFor P C then pairMass n B C else 0) := by
  classical
  by_cases hBg : GoodFor P B
  · by_cases hCg : GoodFor P C
    · rw [rawCross_restrict_eq_of_good G n P Q hB hC hBg hCg]
      simp [hBg, hCg]
    · rw [if_neg (not_not.mpr hBg), if_pos hCg]
      have hcross := rawCrossEnergy_le_pairMass G hn
        (P.restrict (Q.le hB)) (P.restrict (Q.le hC))
      linarith [rawPairTerm_nonneg G n B C]
  · rw [if_pos hBg]
    have hcross := rawCrossEnergy_le_pairMass G hn
      (P.restrict (Q.le hB)) (P.restrict (Q.le hC))
    have hraw := rawPairTerm_nonneg G n B C
    have hlast : 0 ≤ (if ¬ GoodFor P C then pairMass n B C else 0) := by
      split
      · exact pairMass_nonneg n B C
      · norm_num
    linarith

private lemma sum_pairMass_right {S : Finset V} (Q : Finpartition S)
    {n : ℕ} (hn : 0 < n) (hSn : S.card = n) (B : Finset V) :
    ∑ C ∈ Q.parts, pairMass n B C = (B.card : ℝ) / (n : ℝ) := by
  have hsum : ∑ C ∈ Q.parts, (C.card : ℝ) = (n : ℝ) := by
    norm_cast
    simpa [hSn] using Q.sum_card_parts
  simp_rw [pairMass]
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  field_simp

private lemma sum_bad_row_penalty {S : Finset V} (P Q : Finpartition S)
    {n : ℕ} (hn : 0 < n) (hSn : S.card = n) :
    ∑ B ∈ Q.parts, ∑ C ∈ Q.parts,
        (if ¬ GoodFor P B then pairMass n B C else 0) =
      (badVertexCount P Q : ℝ) / (n : ℝ) := by
  classical
  calc
    (∑ B ∈ Q.parts, ∑ C ∈ Q.parts,
        (if ¬ GoodFor P B then pairMass n B C else 0)) =
        ∑ B ∈ Q.parts,
          (if ¬ GoodFor P B then (B.card : ℝ) / (n : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hbad : ¬ GoodFor P B
      · simp [hbad, sum_pairMass_right Q hn hSn]
      · simp [hbad]
    _ = (badVertexCount P Q : ℝ) / (n : ℝ) := by
      rw [← Finset.sum_filter, ← Finset.sum_div]
      unfold badVertexCount badParts
      norm_cast

private lemma sum_bad_column_penalty {S : Finset V} (P Q : Finpartition S)
    {n : ℕ} (hn : 0 < n) (hSn : S.card = n) :
    ∑ B ∈ Q.parts, ∑ C ∈ Q.parts,
        (if ¬ GoodFor P C then pairMass n B C else 0) =
      (badVertexCount P Q : ℝ) / (n : ℝ) := by
  classical
  rw [Finset.sum_comm]
  have hsymm : ∀ B C : Finset V, pairMass n B C = pairMass n C B := by
    intro B C
    unfold pairMass
    ring
  simp_rw [hsymm]
  exact sum_bad_row_penalty P Q hn hSn

private lemma rawEnergy_inf_le_add_bad {S : Finset V}
    (G : SimpleGraph V) {n : ℕ} (hn : 0 < n) (hSn : S.card = n)
    (P Q : Finpartition S) :
    rawEnergy G n (P ⊓ Q).parts ≤
      rawEnergy G n Q.parts + 2 * (badVertexCount P Q : ℝ) / (n : ℝ) := by
  classical
  rw [inf_comm P Q, ← bind_restrict_eq_inf Q P,
    rawEnergy_bind_restrict_eq_sum_cross G n P Q]
  have hraw :
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
        rawPairTerm G n B.1 C.1) = rawEnergy G n Q.parts := by
    simp_rw [Finset.sum_attach]
    rw [rawEnergy]
    exact Finset.sum_attach Q.parts
      (fun B ↦ ∑ C ∈ Q.parts, rawPairTerm G n B C)
  have hrow :
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
        (if ¬ GoodFor P B.1 then pairMass n B.1 C.1 else 0)) =
        (badVertexCount P Q : ℝ) / (n : ℝ) := by
    calc
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
          (if ¬ GoodFor P B.1 then pairMass n B.1 C.1 else 0)) =
          ∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts,
            (if ¬ GoodFor P B.1 then pairMass n B.1 C else 0) := by
        apply Finset.sum_congr rfl
        intro B hB
        exact Finset.sum_attach Q.parts (fun C ↦
          (if ¬ GoodFor P B.1 then pairMass n B.1 C else 0))
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts,
          (if ¬ GoodFor P B.1 then pairMass n B.1 C else 0)) =
          ∑ B ∈ Q.parts, ∑ C ∈ Q.parts,
            (if ¬ GoodFor P B then pairMass n B C else 0) :=
        Finset.sum_attach Q.parts (fun B ↦ ∑ C ∈ Q.parts,
          (if ¬ GoodFor P B then pairMass n B C else 0))
      _ = _ := sum_bad_row_penalty P Q hn hSn
  have hcol :
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
        (if ¬ GoodFor P C.1 then pairMass n B.1 C.1 else 0)) =
        (badVertexCount P Q : ℝ) / (n : ℝ) := by
    calc
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
          (if ¬ GoodFor P C.1 then pairMass n B.1 C.1 else 0)) =
          ∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts,
            (if ¬ GoodFor P C then pairMass n B.1 C else 0) := by
        apply Finset.sum_congr rfl
        intro B hB
        exact Finset.sum_attach Q.parts (fun C ↦
          (if ¬ GoodFor P C then pairMass n B.1 C else 0))
      (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts,
          (if ¬ GoodFor P C then pairMass n B.1 C else 0)) =
          ∑ B ∈ Q.parts, ∑ C ∈ Q.parts,
            (if ¬ GoodFor P C then pairMass n B C else 0) :=
        Finset.sum_attach Q.parts (fun B ↦ ∑ C ∈ Q.parts,
          (if ¬ GoodFor P C then pairMass n B C else 0))
      _ = _ := sum_bad_column_penalty P Q hn hSn
  calc
    (∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
        rawCrossEnergy G n (P.restrict (Q.le B.2)).parts
          (P.restrict (Q.le C.2)).parts) ≤
      ∑ B ∈ Q.parts.attach, ∑ C ∈ Q.parts.attach,
        (rawPairTerm G n B.1 C.1 +
          (if ¬ GoodFor P B.1 then pairMass n B.1 C.1 else 0) +
            (if ¬ GoodFor P C.1 then pairMass n B.1 C.1 else 0)) := by
      apply Finset.sum_le_sum
      intro B hB
      apply Finset.sum_le_sum
      intro C hC
      exact cross_restrict_le_with_bad_penalty G hn P Q B.2 C.2
    _ = rawEnergy G n Q.parts + 2 * (badVertexCount P Q : ℝ) / (n : ℝ) := by
      simp_rw [Finset.sum_add_distrib]
      rw [hraw, hrow, hcol]
      ring

private def remainder {S : Finset V} (Q : Finpartition S) (A : Finset V) :
    Finset V :=
  A \ ({B ∈ Q.parts | B ⊆ A}.biUnion id)

private lemma badVertexCount_le_of_remainders {S : Finset V}
    (P Q : Finpartition S) (m : ℕ)
    (hrem : ∀ A ∈ P.parts, (remainder Q A).card ≤ m) :
    badVertexCount P Q ≤ P.parts.card * m := by
  classical
  have hbad_disjoint :
      ∀ B ∈ badParts P Q, ∀ C ∈ badParts P Q, B ≠ C → Disjoint B C := by
    intro B hB C hC hBC
    exact Q.disjoint (Finset.mem_filter.mp hB).1 (Finset.mem_filter.mp hC).1 hBC
  have hbadcard :
      ((badParts P Q).biUnion id).card = badVertexCount P Q := by
    unfold badVertexCount
    simpa only [id_eq] using (Finset.card_biUnion hbad_disjoint)
  have hsubset :
      (badParts P Q).biUnion id ⊆ P.parts.biUnion (remainder Q) := by
    intro v hv
    obtain ⟨B, hBbad, hvB⟩ := Finset.mem_biUnion.mp hv
    have hBQ := (Finset.mem_filter.mp hBbad).1
    have hBng := (Finset.mem_filter.mp hBbad).2
    obtain ⟨A, hAP, hvA⟩ := P.exists_mem (Q.le hBQ hvB)
    refine Finset.mem_biUnion.mpr ⟨A, hAP, ?_⟩
    rw [remainder, Finset.mem_sdiff]
    refine ⟨hvA, ?_⟩
    intro hvUnion
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hvUnion
    have hCQ := (Finset.mem_filter.mp hC).1
    have hCA := (Finset.mem_filter.mp hC).2
    have hBC : B = C := Q.eq_of_mem_parts hBQ hCQ hvB hvC
    apply hBng
    exact ⟨A, hAP, hBC ▸ hCA⟩
  calc
    badVertexCount P Q = ((badParts P Q).biUnion id).card := hbadcard.symm
    _ ≤ (P.parts.biUnion (remainder Q)).card := Finset.card_le_card hsubset
    _ ≤ ∑ A ∈ P.parts, (remainder Q A).card := Finset.card_biUnion_le
    _ ≤ ∑ A ∈ P.parts, m := by
      apply Finset.sum_le_sum
      exact hrem
    _ = P.parts.card * m := by simp

private lemma card_parts_toFinpartition (P : VertexPartition V) :
    (toFinpartition P).parts.card = P.partCount := by
  classical
  rw [parts_toFinpartition, partSet, Finset.card_image_iff.mpr (part_injective P).injOn]
  simp

@[simp] private lemma partCount_fromFinpartition
    (P : Finpartition (Finset.univ : Finset V)) :
    (fromFinpartition P).partCount = P.parts.card := rfl

private lemma equitable_fromFinpartition_of_two_sizes
    (P : Finpartition (Finset.univ : Finset V)) (m : ℕ)
    (hsize : ∀ A ∈ P.parts, A.card = m ∨ A.card = m + 1) :
    (fromFinpartition P).Equitable := by
  intro i j
  have hi := hsize _ ((P.parts.equivFin).symm i).2
  have hj := hsize _ ((P.parts.equivFin).symm j).2
  change ((P.parts.equivFin).symm i).1.card ≤
      ((P.parts.equivFin).symm j).1.card + 1 ∧
    ((P.parts.equivFin).symm j).1.card ≤
      ((P.parts.equivFin).symm i).1.card + 1
  omega

end EquitableCleanup

open EquitableCleanup

/--
---
conclusion: Lax18.EquitableCleanup.equitable_cleanup
---
Choose a sufficiently fine uniform scale, equitabilise each old class at that
scale, and bound the energy lost in the few mixed remainder blocks.
-/
theorem equitable_cleanup :
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
                                  partitionEnergy G Q + η := by
  intro η r hη hr
  obtain ⟨t, ht⟩ := (exists_nat_gt (2 / η) : ∃ t : ℕ, (2 : ℝ) / η < t)
  have htpos : 0 < t := by
    have : (0 : ℝ) < t := (div_pos (by norm_num) hη).trans ht
    exact_mod_cast this
  let K := r * t
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos hr htpos
  have hrK : r ≤ K := by
    dsimp [K]
    exact Nat.le_mul_of_pos_right r htpos
  refine ⟨K, K, hrK, hrK, ?_⟩
  intro V instFV instDE G P hPr hKn
  let n := Fintype.card V
  have hnpos : 0 < n := hKpos.trans_le hKn
  let m := n / K
  let b := n % K
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos hKn hKpos
  have hbK : b ≤ K := by
    exact (Nat.mod_lt n hKpos).le
  have hdecomp : (K - b) * m + b * (m + 1) = n := by
    dsimp [m, b]
    rw [Nat.sub_mul, mul_add, ← add_assoc,
      Nat.sub_add_cancel (Nat.mul_le_mul_right _ (Nat.mod_lt n hKpos).le),
      mul_one, add_comm, Nat.mod_add_div]
  let PF := toFinpartition P
  let QF := PF.equitabilise hdecomp
  have hQsize : ∀ A ∈ QF.parts, A.card = m ∨ A.card = m + 1 := by
    intro A hA
    simpa [QF] using
      (Finpartition.card_eq_of_mem_parts_equitabilise
        (P := PF) (h := hdecomp) hA)
  have hQcard : QF.parts.card = K := by
    calc
      QF.parts.card = (K - b) + b := by
        simpa [QF] using
          (Finpartition.card_parts_equitabilise PF hdecomp hmpos.ne')
      _ = K := Nat.sub_add_cancel hbK
  have hrem : ∀ A ∈ PF.parts, (remainder QF A).card ≤ m := by
    intro A hA
    simpa [QF, remainder] using
      (Finpartition.card_parts_equitabilise_subset_le PF hdecomp hA)
  have hbad : badVertexCount PF QF ≤ r * m := by
    calc
      badVertexCount PF QF ≤ PF.parts.card * m :=
        badVertexCount_le_of_remainders PF QF m hrem
      _ = P.partCount * m := by rw [card_parts_toFinpartition]
      _ ≤ r * m := Nat.mul_le_mul_right m hPr
  have hmK : m * K ≤ n := by
    dsimp [m]
    exact Nat.div_mul_le_self n K
  have hbadK : badVertexCount PF QF * K ≤ r * n := by
    calc
      badVertexCount PF QF * K ≤ (r * m) * K :=
        Nat.mul_le_mul_right K hbad
      _ = r * (m * K) := by simp [mul_assoc]
      _ ≤ r * n := Nat.mul_le_mul_left r hmK
  have hbadKreal :
      (badVertexCount PF QF : ℝ) * (K : ℝ) ≤ (r : ℝ) * (n : ℝ) := by
    exact_mod_cast hbadK
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hbad_t : (badVertexCount PF QF : ℝ) * (t : ℝ) ≤ (n : ℝ) := by
    have hmul :
        (r : ℝ) * ((badVertexCount PF QF : ℝ) * (t : ℝ)) ≤
          (r : ℝ) * (n : ℝ) := by
      calc
      (r : ℝ) * ((badVertexCount PF QF : ℝ) * (t : ℝ)) =
          (badVertexCount PF QF : ℝ) * (K : ℝ) := by
        simp [K]
        ring
      _ ≤ (r : ℝ) * (n : ℝ) := hbadKreal
    by_contra hnot
    have hlt : (n : ℝ) < (badVertexCount PF QF : ℝ) * (t : ℝ) :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge hmul) (mul_lt_mul_of_pos_left hlt hrreal)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have htreal : (0 : ℝ) < t := by exact_mod_cast htpos
  have hfrac :
      2 * (badVertexCount PF QF : ℝ) / (n : ℝ) ≤ 2 / (t : ℝ) := by
    rw [div_le_div_iff₀ hnreal htreal]
    nlinarith
  have hsmall : (2 : ℝ) / t < η := by
    apply (div_lt_iff₀ htreal).2
    have := (div_lt_iff₀ hη).mp ht
    nlinarith
  have herror :
      2 * (badVertexCount PF QF : ℝ) / (n : ℝ) ≤ η :=
    hfrac.trans hsmall.le
  refine ⟨fromFinpartition QF,
    equitable_fromFinpartition_of_two_sizes QF m hQsize, ?_, ?_, ?_⟩
  · rw [partCount_fromFinpartition, hQcard]
    exact hPr.trans hrK
  · rw [partCount_fromFinpartition, hQcard]
  · have hmono :
        rawEnergy G n PF.parts ≤ rawEnergy G n (PF ⊓ QF).parts := by
      rw [← bind_restrict_eq_inf PF QF]
      exact rawEnergy_le_rawEnergy_bind G n PF
        (fun A hA ↦ QF.restrict (PF.le hA))
    have hclean := rawEnergy_inf_le_add_bad G hnpos rfl PF QF
    rw [partitionEnergy_eq_rawEnergy_partSet,
      partitionEnergy_fromFinpartition]
    change rawEnergy G n (partSet P) ≤ rawEnergy G n QF.parts + η
    rw [← parts_toFinpartition]
    exact hmono.trans (hclean.trans (by
      simpa [add_comm] using add_le_add_left herror (rawEnergy G n QF.parts)))

end Lax18Proofs
