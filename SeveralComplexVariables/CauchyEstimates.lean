/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyEstimates
public import Mathlib.Topology.MetricSpace.Thickening
public import SeveralComplexVariables.Derivatives
public import ToMathlib.Topology.MetricSpace.Pi

/-!
# Cauchy estimates and local derivative bounds

These estimates reuse the one-variable Cauchy estimate on coordinate slices. The source has the
supremum norm, so a coordinate disc fits in the ball of the same radius. The one-variable
bound for derivatives on small closed thickenings of compact subsets of a holomorphic domain is
imported from `ComplexAnalysis.CauchyEstimates` and re-exported.

## Main results

`norm_partialDeriv_le` is the Cauchy estimate for a coordinate derivative on a polydisc.
`norm_partialDeriv_le_of_slice` is the one-variable slice form.
`AnalyticOnNhd.exists_cthickening_deriv_bound` (imported from `ComplexAnalysis.CauchyEstimates`)
bounds derivatives uniformly on a closed thickening of a compact subset of a one-variable
domain.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public section

open Complex Function Metric Set

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [Fintype ι] in
/-- Cauchy's first derivative bound only needs holomorphy along the chosen coordinate disc. -/
theorem norm_partialDeriv_le_of_slice {f : (ι → ℂ) → F} {z : ι → ℂ}
    (i : ι) {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ (fun w => f (update z i w)) (closedBall (z i) r))
    (hM : ∀ w ∈ sphere (z i) r, ‖f (update z i w)‖ ≤ M) :
    ‖partialDeriv i f z‖ ≤ M / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hf.diffContOnCl_ball Subset.rfl) hM

/-- A bound on a closed sup-norm ball controls every coordinate derivative at its center. -/
theorem norm_partialDeriv_le {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {z : ι → ℂ} (i : ι) {r M : ℝ} (hr : 0 < r)
    (hball : closedBall z r ⊆ U) (hM : ∀ w ∈ closedBall z r, ‖f w‖ ≤ M) :
    ‖partialDeriv i f z‖ ≤ M / r := by
  apply norm_partialDeriv_le_of_slice i hr
  · intro w hw
    exact ((hf _ (hball (update_mem_closedBall hr.le (mem_closedBall_self hr.le) i hw))
      ).differentiableAt.comp w (hasDerivAt_update z i w).differentiableAt).differentiableWithinAt
  · intro w hw
    exact hM _ (update_mem_closedBall hr.le (mem_closedBall_self hr.le) i
      (sphere_subset_closedBall hw))

end SeveralComplexVariables

end
