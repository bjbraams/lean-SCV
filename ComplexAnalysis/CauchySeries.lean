/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Bounds and convergence of one-variable Cauchy power series

For a function bounded on a closed complex disc, its Cauchy power-series coefficients satisfy
geometric bounds. For a function analytic on a neighborhood of that disc with values in a
complete complex normed space, the Cauchy series represents the function throughout the open
disc.

## Main results

* `Complex.norm_cauchyPowerSeries_apply_one_le`: Cauchy's estimate for the values of the Cauchy
  power-series coefficients on unit inputs, from a bound on the closed disc.
* `Complex.hasFPowerSeriesOnBall_cauchyPowerSeries_of_analyticOnNhd`: The Cauchy power series of
  a function analytic on a closed disc converges on the open disc, with the radius given as an
  extended real number.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Real Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Cauchy's estimate for the values of the Cauchy power-series coefficients on unit inputs,
from a bound on the closed disc. -/
theorem norm_cauchyPowerSeries_apply_one_le {g : ℂ → F} {b : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ w ∈ closedBall b ρ, ‖g w‖ ≤ M) (k : ℕ) :
    ‖cauchyPowerSeries g b ρ k (fun _ ↦ 1)‖ ≤ M * ρ⁻¹ ^ k := by
  have hint : ∫ θ in (0:ℝ)..2 * π, ‖g (circleMap b ρ θ)‖ ≤ M * (2 * π) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (f := fun θ ↦ ‖g (circleMap b ρ θ)‖) (C := M) (fun θ _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hM _ (circleMap_mem_closedBall b hρ.le θ))
    rw [sub_zero, abs_of_pos Real.two_pi_pos, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  calc ‖cauchyPowerSeries g b ρ k (fun _ ↦ 1)‖
      ≤ ‖cauchyPowerSeries g b ρ k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries g b ρ k‖ := by simp
    _ ≤ ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, ‖g (circleMap b ρ θ)‖) * |ρ|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le g b ρ k
    _ ≤ M * ρ⁻¹ ^ k := by
        rw [abs_of_pos hρ]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, ‖g (circleMap b ρ θ)‖
            ≤ (2 * π)⁻¹ * (M * (2 * π)) := by gcongr
          _ = M := by field_simp

/-- The Cauchy power series of a function analytic on a closed disc converges on the open disc, with
the radius given as an extended real number. -/
theorem hasFPowerSeriesOnBall_cauchyPowerSeries_of_analyticOnNhd {g : ℂ → F} {b : ℂ}
    {r : ℝ} (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (closedBall b r)) :
    HasFPowerSeriesOnBall g (cauchyPowerSeries g b r) b (ENNReal.ofReal r) := by
  have := hg.differentiableOn.hasFPowerSeriesOnBall (R := ⟨r, hr.le⟩) hr
  rwa [ENNReal.ofReal_eq_coe_nnreal hr.le]

end Complex
