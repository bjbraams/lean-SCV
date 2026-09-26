/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import ComplexAnalysis.Subharmonic.Basic

/-!
# Subharmonicity of continuous convex functions on planar domains

The local submean property is preserved by translation. A continuous real-valued convex function
on an open convex subset of the complex plane is subharmonic, by applying convexity to circular
averages.

## Main results

* `Complex.HasSubmeanAt.comp_add_right`: Translating the parameter of a function with the local
  submean property.
* `ConvexOn.subharmonicOn`: A continuous function that is convex on an open set of `ℂ` is
  subharmonic there.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Filter Metric Set Real
open scoped Topology

namespace Complex

/-- Translating the parameter of a function with the local submean property. -/
theorem HasSubmeanAt.comp_add_right {u : ℂ → ℝ} {t₀ : ℂ}
    (h : HasSubmeanAt (fun t ↦ u (t + t₀)) 0) : HasSubmeanAt u t₀ := by
  filter_upwards [h] with r ⟨hint, hle⟩
  have hmap : ∀ θ : ℝ, circleMap 0 r θ + t₀ = circleMap t₀ r θ := fun θ ↦ by
    simp [circleMap, add_comm]
  refine ⟨?_, ?_⟩
  · rw [circleIntegrable_def] at hint ⊢
    simpa only [hmap] using hint
  · simpa only [zero_add, circleAverage_map_add_const] using hle

/-- A continuous function that is convex on an open set of `ℂ` is subharmonic there. -/
theorem _root_.ConvexOn.subharmonicOn {u : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hu : ConvexOn ℝ W u) (hc : ContinuousOn u W) : SubharmonicOn u W := by
  refine ⟨hc.upperSemicontinuousOn, fun a ha ↦ ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds ha)
  refine hasSubmeanAt_of_forall_lt hρ fun r hr hrρ ↦ ?_
  have hsub : closedBall a r ⊆ W := (closedBall_subset_ball hrρ).trans hball
  have hint : CircleIntegrable u a r :=
    (hc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  have hrefl : ∀ t ∈ sphere a r, 2 * a - t ∈ sphere a r := by
    intro t ht
    rw [mem_sphere, dist_eq_norm] at ht ⊢
    rw [← ht, ← norm_neg]
    congr 1
    ring
  have hint' : CircleIntegrable (fun t ↦ u (2 * a - t)) a r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    exact (hc.mono (sphere_subset_closedBall.trans hsub)).comp (by fun_prop) fun t ht ↦
      hrefl t (by simpa [abs_of_pos hr] using ht)
  refine ⟨hint, ?_⟩
  have hmid : ∀ t ∈ sphere a r, u a ≤ (1 / 2 : ℝ) • u t + (1 / 2 : ℝ) • u (2 * a - t) := by
    intro t ht
    have h1 : t ∈ W := hsub (sphere_subset_closedBall ht)
    have h2 : 2 * a - t ∈ W := hsub (sphere_subset_closedBall (hrefl t ht))
    have := hu.2 h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert this using 2
    simp only [Complex.real_smul]
    push_cast
    ring
  have hi₁ : CircleIntegrable (fun t ↦ (1 / 2 : ℝ) • u t) a r := hint.const_smul
  have hi₂ : CircleIntegrable (fun t ↦ (1 / 2 : ℝ) • u (2 * a - t)) a r := hint'.const_smul
  have hle := circleAverage_mono (circleIntegrable_const (u a) a r) (hi₁.add hi₂)
    (fun t ht ↦ hmid t (by simpa [abs_of_pos hr] using ht))
  rw [circleAverage_const, circleAverage_add hi₁ hi₂, circleAverage_fun_smul,
    circleAverage_fun_smul, Real.circleAverage_reflect] at hle
  simp only [smul_eq_mul] at hle
  linarith

end Complex
