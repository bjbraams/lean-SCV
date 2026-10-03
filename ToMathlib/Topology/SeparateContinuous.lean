/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import ToMathlib.Topology.Baire.Bounded

/-!
# Uniform bounds for separately continuous maps

Separate continuity and compactness of the parameter set give pointwise bounds on the norms.
The general Baire theorem for lower semicontinuous families then gives a uniform bound on
a nonempty open cylinder. The target need only be seminormed, and the compact set may be empty.
-/

public section

open Set

/-- Baire's theorem gives a uniform bound on an open cylinder from separate continuity and
compactness of the second factor. The compact set may be empty. -/
theorem exists_open_bounded_cylinder_of_separately_continuous
    {X Y F : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace Y]
    [SeminormedAddCommGroup F] {U : Set X} {K : Set Y} {f : X → Y → F}
    (hU : IsOpen U) (hne : U.Nonempty) (hK : IsCompact K)
    (hx : ∀ y ∈ K, ContinuousOn (fun x ↦ f x y) U)
    (hy : ∀ x ∈ U, ContinuousOn (f x) K) :
    ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ x ∈ V, ∀ y ∈ K, ‖f x y‖ ≤ M := by
  have hb (x : X) (hxU : x ∈ U) : BddAbove (range (fun y : K ↦ ‖f x y‖)) := by
    obtain ⟨M, hM⟩ := hK.bddAbove_image (hy x hxU).norm
    exact ⟨M, by rintro _ ⟨y, rfl⟩; exact hM (mem_image_of_mem _ y.property)⟩
  obtain ⟨V, hV, hneV, hVU, M, hM⟩ :=
    exists_open_uniformly_boundedAbove_of_lowerSemicontinuousOn
      (g := fun (y : K) x ↦ ‖f x y‖) hU hne
      (fun y ↦ (hx y y.property).norm.lowerSemicontinuousOn) hb
  exact ⟨V, hV, hneV, hVU, M, fun x hxV y hyK ↦ hM x hxV ⟨y, hyK⟩⟩

end
