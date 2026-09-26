/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Uniform bounds for separately continuous maps

Baire's theorem and compactness of the second factor give a uniform bound on a nonempty
open cylinder. No analyticity or vector-space structure on the parameter spaces is needed.

## Main results

* `exists_open_bounded_cylinder_of_separately_continuous`: Baire's theorem gives a uniform bound
  on an open cylinder from separate continuity and compactness of the second factor. The compact
  set may be empty.

## References

* `Mathlib.Topology.Baire.Lemmas`: formal background used by this module.
* `Mathlib.Analysis.Normed.Group.Continuity`: formal background used by this module.
-/

public section

open Filter Function Metric Set
open scoped Topology

/-- Baire's theorem gives a uniform bound on an open cylinder from separate continuity and
compactness of the second factor. The compact set may be empty. -/
theorem exists_open_bounded_cylinder_of_separately_continuous
    {X Y F : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup F] {U : Set X} {K : Set Y} {f : X → Y → F}
    (hU : IsOpen U) (hne : U.Nonempty) (hK : IsCompact K)
    (hx : ∀ y ∈ K, ContinuousOn (fun x => f x y) U)
    (hy : ∀ x ∈ U, ContinuousOn (f x) K) :
    ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ x ∈ V, ∀ y ∈ K, ‖f x y‖ ≤ M := by
  let : BaireSpace U := hU.baireSpace
  let : Nonempty U := hne.to_subtype
  let S : ℕ → Set U := fun n => {x | ∀ y ∈ K, ‖f x y‖ ≤ n}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun hy =>
      isClosed_le ((continuousOn_iff_continuous_domRestrict.mp (hx y hy)).norm) continuous_const
  have hcover : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨M, hM⟩ := hK.bddAbove_image (hy x x.property).norm
    obtain ⟨n, hn⟩ := exists_nat_ge M
    exact mem_iUnion.mpr ⟨n, fun y hy => (hM (mem_image_of_mem _ hy)).trans hn⟩
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  refine ⟨Subtype.val '' interior (S n),
    hU.isOpenMap_subtype_val _ isOpen_interior, hn.image _, ?_, n, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · rintro _ ⟨x, hx, rfl⟩ y hy
    exact interior_subset hx y hy

end
