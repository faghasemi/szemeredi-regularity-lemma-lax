import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Tactic
import Lax18.PartitionEnergyMonotonicity

namespace Lax18Proofs

open Lax18.EdgeDensity
open Lax18.FiniteGraphPartitions
open Lax18.PartitionEnergy
open scoped BigOperators

universe u

/--
---
conclusion: Lax18.PartitionEnergyMonotonicity.partitionEnergy_mono_of_refines
---
The density on each coarse pair is the weighted average of the densities on
the fine pairs above it. Finite Cauchy–Schwarz on every fibre, followed by
summation, proves that refinement cannot decrease partition energy.
-/
theorem partitionEnergy_mono_of_refines :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (P Q : VertexPartition V),
        Refines Q P → partitionEnergy G P ≤ partitionEnergy G Q := by
  classical
  intro V _ _ G P Q hQP
  letI : DecidableRel G.Adj := Classical.decRel G.Adj

  let parent : Fin Q.partCount → Fin P.partCount :=
    fun j ↦ Classical.choose (hQP j)
  have hparent (j : Fin Q.partCount) : Q.part j ⊆ P.part (parent j) :=
    Classical.choose_spec (hQP j)

  let fiber (i : Fin P.partCount) : Finset (Fin Q.partCount) :=
    Finset.univ.filter fun j ↦ parent j = i

  have parent_eq_of_mem {i : Fin P.partCount} {j : Fin Q.partCount} {v : V}
      (hvj : v ∈ Q.part j) (hvi : v ∈ P.part i) : parent j = i := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.pairwise_disjoint (parent j) i hne)
      (hparent j hvj) hvi

  have part_eq_biUnion (i : Fin P.partCount) :
      P.part i = (fiber i).biUnion Q.part := by
    ext v
    constructor
    · intro hvi
      obtain ⟨j, hvj⟩ := Q.covers v
      exact Finset.mem_biUnion.mpr
        ⟨j, by simp [fiber, parent_eq_of_mem hvj hvi], hvj⟩
    · intro hv
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hv
      have hjparent : parent j = i := by simpa [fiber] using hj
      simpa [hjparent] using hparent j hvj

  have fiber_parts_disjoint (i : Fin P.partCount) :
      ((fiber i : Finset (Fin Q.partCount)) : Set (Fin Q.partCount)).PairwiseDisjoint Q.part := by
    intro j _ l _ hjl
    exact Q.pairwise_disjoint j l hjl

  have part_card_eq_sum (i : Fin P.partCount) :
      (P.part i).card = ∑ j ∈ fiber i, (Q.part j).card := by
    rw [part_eq_biUnion i, Finset.card_biUnion (fiber_parts_disjoint i)]

  let coarseFiber (ik : Fin P.partCount × Fin P.partCount) :
      Finset (Fin Q.partCount × Fin Q.partCount) :=
    fiber ik.1 ×ˢ fiber ik.2

  have coarseFiber_disjoint :
      ((Finset.univ ×ˢ Finset.univ : Finset (Fin P.partCount × Fin P.partCount)) :
          Set (Fin P.partCount × Fin P.partCount)).PairwiseDisjoint coarseFiber := by
    intro ik _ i'k' _ hne
    change Disjoint (coarseFiber ik) (coarseFiber i'k')
    rw [Finset.disjoint_left]
    intro jl hjl hjl'
    have hfirst : ik.1 = i'k'.1 := by
      have h₁ := (Finset.mem_product.mp hjl).1
      have h₂ := (Finset.mem_product.mp hjl').1
      simpa [coarseFiber, fiber] using (show parent jl.1 = ik.1 from by simpa [fiber] using h₁).symm.trans
        (show parent jl.1 = i'k'.1 from by simpa [fiber] using h₂)
    have hsecond : ik.2 = i'k'.2 := by
      have h₁ := (Finset.mem_product.mp hjl).2
      have h₂ := (Finset.mem_product.mp hjl').2
      simpa [coarseFiber, fiber] using (show parent jl.2 = ik.2 from by simpa [fiber] using h₁).symm.trans
        (show parent jl.2 = i'k'.2 from by simpa [fiber] using h₂)
    exact hne (Prod.ext hfirst hsecond)

  have coarseFiber_biUnion :
      (Finset.univ ×ˢ Finset.univ : Finset (Fin P.partCount × Fin P.partCount)).biUnion
          coarseFiber =
        (Finset.univ ×ˢ Finset.univ : Finset (Fin Q.partCount × Fin Q.partCount)) := by
    ext jl
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ik, hjl⟩
      trivial
    · intro _
      refine ⟨(parent jl.1, parent jl.2), ?_⟩
      simp [coarseFiber, fiber]

  have edgeCount_eq_card_interedges (A B : Finset V) :
      edgeCountBetween G A B = (G.interedges A B).card := by
    simp [edgeCountBetween, SimpleGraph.interedges_def]

  have density_eq_card_interedges (A B : Finset V)
      (hA : A.Nonempty) (hB : B.Nonempty) :
      density G A B =
        ((G.interedges A B).card : ℝ) / ((A.card : ℝ) * (B.card : ℝ)) := by
    simp [density, hA.card_ne_zero, hB.card_ne_zero, edgeCount_eq_card_interedges]

  have edge_fibers_disjoint (ik : Fin P.partCount × Fin P.partCount) :
      ((coarseFiber ik : Finset (Fin Q.partCount × Fin Q.partCount)) :
          Set (Fin Q.partCount × Fin Q.partCount)).PairwiseDisjoint
        (fun jl ↦ G.interedges (Q.part jl.1) (Q.part jl.2)) := by
    intro jl _ j'l' _ hne
    change Disjoint
      (G.interedges (Q.part jl.1) (Q.part jl.2))
      (G.interedges (Q.part j'l'.1) (Q.part j'l'.2))
    rw [Finset.disjoint_left]
    intro e he he'
    have he := G.mem_interedges_iff.mp he
    have he' := G.mem_interedges_iff.mp he'
    have hfirst : jl.1 = j'l'.1 := by
      by_contra h
      exact Finset.disjoint_left.mp (Q.pairwise_disjoint _ _ h) he.1 he'.1
    have hsecond : jl.2 = j'l'.2 := by
      by_contra h
      exact Finset.disjoint_left.mp (Q.pairwise_disjoint _ _ h) he.2.1 he'.2.1
    exact hne (Prod.ext hfirst hsecond)

  have coarse_edge_count_eq_sum (ik : Fin P.partCount × Fin P.partCount) :
      ((G.interedges (P.part ik.1) (P.part ik.2)).card : ℝ) =
        ∑ jl ∈ coarseFiber ik,
          ((G.interedges (Q.part jl.1) (Q.part jl.2)).card : ℝ) := by
    have hnat :
        (G.interedges (P.part ik.1) (P.part ik.2)).card =
          ∑ jl ∈ coarseFiber ik,
            (G.interedges (Q.part jl.1) (Q.part jl.2)).card := by
      rw [part_eq_biUnion ik.1, part_eq_biUnion ik.2,
        G.interedges_biUnion, Finset.card_biUnion (edge_fibers_disjoint ik)]
    exact_mod_cast hnat

  have coarse_weight_eq_sum (ik : Fin P.partCount × Fin P.partCount) :
      ((P.part ik.1).card : ℝ) * ((P.part ik.2).card : ℝ) =
        ∑ jl ∈ coarseFiber ik,
          ((Q.part jl.1).card : ℝ) * ((Q.part jl.2).card : ℝ) := by
    rw [show coarseFiber ik = fiber ik.1 ×ˢ fiber ik.2 from rfl,
      Finset.sum_product]
    change ((P.part ik.1).card : ℝ) * ((P.part ik.2).card : ℝ) =
      ∑ x ∈ fiber ik.1, ∑ y ∈ fiber ik.2,
        ((Q.part x).card : ℝ) * ((Q.part y).card : ℝ)
    rw [← Finset.sum_mul_sum]
    norm_cast
    rw [← part_card_eq_sum ik.1, ← part_card_eq_sum ik.2]

  have coarse_term_le_fiber_sum (ik : Fin P.partCount × Fin P.partCount) :
      ((G.interedges (P.part ik.1) (P.part ik.2)).card : ℝ) ^ 2 /
          (((P.part ik.1).card : ℝ) * ((P.part ik.2).card : ℝ)) ≤
        ∑ jl ∈ coarseFiber ik,
          ((G.interedges (Q.part jl.1) (Q.part jl.2)).card : ℝ) ^ 2 /
            (((Q.part jl.1).card : ℝ) * ((Q.part jl.2).card : ℝ)) := by
    rw [coarse_edge_count_eq_sum ik, coarse_weight_eq_sum ik]
    apply Finset.sq_sum_div_le_sum_sq_div
    intro jl _
    exact mul_pos (by exact_mod_cast (Q.nonempty_part jl.1).card_pos)
      (by exact_mod_cast (Q.nonempty_part jl.2).card_pos)

  let quotientSum (R : VertexPartition V) : ℝ :=
    ∑ ij : Fin R.partCount × Fin R.partCount,
      ((G.interedges (R.part ij.1) (R.part ij.2)).card : ℝ) ^ 2 /
        (((R.part ij.1).card : ℝ) * ((R.part ij.2).card : ℝ))

  have partitionEnergy_eq (R : VertexPartition V) :
      partitionEnergy G R = quotientSum R / (Fintype.card V : ℝ) ^ 2 := by
    rw [partitionEnergy]
    simp_rw [pairWeight, VertexPartition.partSize,
      density_eq_card_interedges _ _ (R.nonempty_part _) (R.nonempty_part _)]
    rw [← Fintype.sum_prod_type']
    simp only [quotientSum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ij _
    have h₁ : ((R.part ij.1).card : ℝ) ≠ 0 := by
      exact_mod_cast (R.nonempty_part ij.1).card_ne_zero
    have h₂ : ((R.part ij.2).card : ℝ) ≠ 0 := by
      exact_mod_cast (R.nonempty_part ij.2).card_ne_zero
    let ⟨v, _⟩ := R.nonempty_part ij.1
    letI : Nonempty V := ⟨v⟩
    have hV : ((Fintype.card V : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    set a : ℝ := ((R.part ij.1).card : ℝ)
    set b : ℝ := ((R.part ij.2).card : ℝ)
    set e : ℝ := ((G.interedges (R.part ij.1) (R.part ij.2)).card : ℝ)
    set n : ℝ := (Fintype.card V : ℝ)
    have ha : a ≠ 0 := by simpa [a] using h₁
    have hb : b ≠ 0 := by simpa [b] using h₂
    have hn : n ≠ 0 := hV
    field_simp [ha, hb, hn]

  rw [partitionEnergy_eq P, partitionEnergy_eq Q]
  gcongr
  calc
    quotientSum P ≤
        ∑ ik : Fin P.partCount × Fin P.partCount,
          ∑ jl ∈ coarseFiber ik,
            ((G.interedges (Q.part jl.1) (Q.part jl.2)).card : ℝ) ^ 2 /
              (((Q.part jl.1).card : ℝ) * ((Q.part jl.2).card : ℝ)) := by
      exact Finset.sum_le_sum fun ik _ ↦ coarse_term_le_fiber_sum ik
    _ = quotientSum Q := by
      simp only [quotientSum]
      rw [show (Finset.univ : Finset (Fin P.partCount × Fin P.partCount)) =
          Finset.univ ×ˢ Finset.univ by ext; simp]
      rw [show (Finset.univ : Finset (Fin Q.partCount × Fin Q.partCount)) =
          Finset.univ ×ˢ Finset.univ by ext; simp]
      rw [← Finset.sum_biUnion coarseFiber_disjoint, coarseFiber_biUnion]

end Lax18Proofs
