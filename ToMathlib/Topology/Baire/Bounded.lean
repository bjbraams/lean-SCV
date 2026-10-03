/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Local uniform bounds for pointwise bounded families

A pointwise bounded-above family of lower semicontinuous real functions on a Baire space
is uniformly bounded above on some nonempty open subset of each nonempty open set.
Consequently the points admitting a local uniform upper bound form a dense open set.
The index type is arbitrary and may be empty.
-/

public section

open Set Filter
open scoped Topology

/-- A pointwise bounded-above family of lower semicontinuous functions has a uniform upper
bound on a nonempty open subset of any nonempty open domain in a Baire space. -/
theorem exists_open_uniformly_boundedAbove_of_lowerSemicontinuousOn
    {X ι : Type*} [TopologicalSpace X] [BaireSpace X] {U : Set X} {g : ι → X → ℝ}
    (hU : IsOpen U) (hne : U.Nonempty) (hg : ∀ i, LowerSemicontinuousOn (g i) U)
    (hb : ∀ x ∈ U, BddAbove (range (fun i ↦ g i x))) :
    ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ x ∈ V, ∀ i, g i x ≤ M := by
  let : BaireSpace U := hU.baireSpace
  let : Nonempty U := hne.to_subtype
  let S : ℕ → Set U := fun n ↦ {x | ∀ i, g i x ≤ n}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun i ↦
      (lowerSemicontinuous_restrict_iff.mpr (hg i)).isClosed_preimage (n : ℝ)
  have hcover : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨M, hM⟩ := hb x x.property
    obtain ⟨n, hn⟩ := exists_nat_ge M
    exact mem_iUnion.mpr ⟨n, fun i ↦ (hM (mem_range_self i)).trans hn⟩
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  refine ⟨Subtype.val '' interior (S n), hU.isOpenMap_subtype_val _ isOpen_interior,
    hn.image _, ?_, n, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · rintro _ ⟨x, hx, rfl⟩ i
    exact interior_subset hx i

/-- Points where a family admits a local uniform upper bound form an open set. -/
theorem isOpen_setOf_locally_uniformly_boundedAbove
    {X ι : Type*} [TopologicalSpace X] (g : ι → X → ℝ) :
    IsOpen {x | ∃ M : ℝ, ∀ᶠ y in 𝓝 x, ∀ i, g i y ≤ M} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨M, hM⟩
  exact hM.eventually_nhds.mono fun y hy ↦ ⟨M, hy⟩

/-- A pointwise bounded-above family of lower semicontinuous real functions on a Baire
space admits a local uniform upper bound on a dense open set. -/
theorem dense_setOf_locally_uniformly_boundedAbove
    {X ι : Type*} [TopologicalSpace X] [BaireSpace X] {g : ι → X → ℝ}
    (hg : ∀ i, LowerSemicontinuous (g i))
    (hb : ∀ x, BddAbove (range (fun i ↦ g i x))) :
    Dense {x | ∃ M : ℝ, ∀ᶠ y in 𝓝 x, ∀ i, g i y ≤ M} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨V, hV, ⟨x, hx⟩, hVU, M, hM⟩ :=
    exists_open_uniformly_boundedAbove_of_lowerSemicontinuousOn hU hne
      (fun i ↦ (hg i).lowerSemicontinuousOn U) (fun x _ ↦ hb x)
  exact ⟨x, hVU hx, M, Filter.Eventually.mono (hV.mem_nhds hx) hM⟩

end
